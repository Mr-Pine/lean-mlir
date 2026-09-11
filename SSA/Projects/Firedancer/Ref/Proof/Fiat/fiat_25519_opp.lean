import SSA.Projects.Firedancer.Ref.Spec.Fiat.fiat_25519_opp
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_opp
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Limb


namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

def opp_repr (q : Fin 5 → Nat) :=
  ![0xfffffffffffda - q 0, 0xffffffffffffe - q 1, 0xffffffffffffe - q 2,
    0xffffffffffffe - q 3, 0xffffffffffffe - q 4]

set_option linter.unnecessarySeqFocus false in
lemma opp_repr_bounds (q : Fin 5 → Nat) (i : Fin 5) : opp_repr q i ≤ biasLimb i := by
  fin_cases i <;> simp [opp_repr] <;> omega

/-- One limb of the region's `const - load`, over `toNat`: at fiat's input
bound the bias limb dominates, so the `sub` does not wrap. -/
theorem opp_limb_toNat {b : BitVec 64} {c n : ℕ} (hb : b.toNat = n)
    (hn : n ≤ c) (hc' : c < 2 ^ 64) :
    (BitVec.ofNat 64 c - b).toNat = c - n := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, hb]
  omega

lemma opp_repr_correct (q : Fin 5 → Nat)
    (hq : ∀ (i : Fin 5), q i ≤ biasLimb i) :
    decodeFieldElem (opp_repr q) = -(decodeFieldElem q) := by
  have p_separation : decodeFieldElem (opp_repr q)
      = decodeFieldElem ![0xfffffffffffda, 0xffffffffffffe, 0xffffffffffffe,
          0xffffffffffffe, 0xffffffffffffe] - decodeFieldElem q := by
    simp [decodeFieldElem, opp_repr]
    -- each limb's `-` is genuine: the bias limb alone exceeds `q i`
    have e0 : q 0 ≤ 0xfffffffffffda := hq 0
    have e1 : q 1 ≤ 0xffffffffffffe := hq 1
    have e2 : q 2 ≤ 0xffffffffffffe := hq 2
    have e3 : q 3 ≤ 0xffffffffffffe := hq 3
    have e4 : q 4 ≤ 0xffffffffffffe := hq 4
    rw [Nat.cast_sub e0, Nat.cast_sub e1, Nat.cast_sub e2, Nat.cast_sub e3, Nat.cast_sub e4]
    push_cast
    ring
  -- the bias is exactly `2 * p`, hence `0` in `ZMod p`
  have p_decode : decodeFieldElem ![0xfffffffffffda, 0xffffffffffffe, 0xffffffffffffe,
      0xffffffffffffe, 0xffffffffffffe] = 0 := by
    have hS : (4503599627370458 + 4503599627370494 * 2 ^ 51 + 4503599627370494 * 2 ^ 102
        + 4503599627370494 * 2 ^ 153 + 4503599627370494 * 2 ^ 204 : ℕ) = 2 * _root_.p := by
      norm_num [_root_.p]
    have hcast := congrArg (fun n : ℕ => (n : ZMod _root_.p)) hS
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_self,
      mul_zero] at hcast
    simpa [decodeFieldElem] using hcast
  rw [p_separation, p_decode, zero_sub]

set_option maxHeartbeats 1600000 in
theorem fiat_25519_opp_conforms (o q: Pointer) (s: GlobalState)
  (hs : s.WF)
  (ho: IsFieldElemPtr s.mem o)
  (hq: IsFieldElemPtr s.mem q)
  (hqbounds : BiasBounds hq) :
  fiat_25519_opp_spec o q s ho hq := by
    -- the walk produces the limbwise forms; read them back once, here
    suffices h : ∃ out : BitVec (5 * 64),
        let output_state : GlobalState := { s with mem := s.mem.splice o out }
        (∃ s' : GlobalState,
            StateT.run (runFunction (fiat_25519_opp.denote
                (Ctxt.Valuation.ofHVector [.value q, .value o]ₕ))) s = .value ([]ₕ, s')
          ∧ output_state ≈ s')
        ∧ readFieldElem? o output_state.mem = Neg.neg <$> readFieldElem? q s.mem
        ∧ BiasBounds? o output_state.mem by
      obtain ⟨out, hrun, hval, hbnd⟩ := h
      refine ⟨out, ?_, biasBounds_of_readLimb? _ hbnd, hrun⟩
      refine readFieldElem_eq_of ?_
      rw [hval, show readFieldElem? q s.mem = some (readFieldElem hq) from (Option.some_get _).symm]
      rfl
    simp only [Cfg.denote]

    obtain ⟨qblk, hqblk, hqlen⟩ := id hq.left
    obtain ⟨qinput, hqinput⟩ := exists_limbs hqblk
    let output := opp_repr qinput
    let outputBV := BitVec.ofNat 64 ∘ output

    refine ⟨packLimbs outputBV, ?_⟩

    constructor
    case right =>
      simp [readFieldElem?, hqinput, ho, limbReadbackPack, outputBV]
      have qinput_bounds (j: Fin 5) : qinput j ≤ biasLimb j := by
        simp only [hqinput, biasBounds_readLimb? hq hqbounds j]
      have output_bounds (i: Fin 5) : output i ≤ biasLimb i := opp_repr_bounds qinput i
      have loose_output_bounds (i: Fin 5) : output i < 18446744073709551616 :=
        ((output_bounds i).trans (biasLimb_le i)).trans_lt (by norm_num)
      simp [BiasBounds?, loose_output_bounds, Nat.mod_eq_of_lt]
      constructor
      simp only [vec_eq, Neg.neg, output, opp_repr_correct qinput qinput_bounds]

      intro i l hl
      rw [limbReadbackPack s.mem o outputBV (show Fits s.mem o (5 * 64) from ho.left) i,
        Option.some.injEq] at hl
      subst hl
      simpa [outputBV, Nat.mod_eq_of_lt (loose_output_bounds i)] using output_bounds i

    obtain ⟨outMem, houtMem⟩ : ∃ m : MemoryState,
        m = ((((s.mem.splice o (outputBV 0)).splice (o.withOffset 8) (outputBV 1)).splice
              (o.withOffset 16) (outputBV 2)).splice (o.withOffset 24) (outputBV 3)).splice
              (o.withOffset 32) (outputBV 4) := ⟨_, rfl⟩
    refine ⟨s.popFrame outMem, run_runFunction (s' := { s with mem := outMem }) ?_, ?equiv⟩
    case equiv =>
      have hnone : ∀ (b : BlockId), s.alloc.nextFreeBlock ≤ b.id → outMem.live? b = none := by
        rw [houtMem]
        exact fun b hb => live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none
          (live?_splice_eq_none (live?_splice_eq_none (hs b hb)))))
      refine GlobalState.Equiv.trans ?_ (GlobalState.Equiv.symm
        (killFrom_equiv_of_none (s := s) (m := outMem) hnone))
      rw [houtMem]
      exact GlobalState.Equiv.symm
        (splice5_equiv (outputBV 0) (outputBV 1) (outputBV 2) (outputBV 3) (outputBV 4) ho)

    denote_step_reduce v 1 [LLVM.const?] fold
    subst hv0 hv1

    peel_limb 0, q, hq.left, qblk, hqblk, qlimb
    denote_step_reduce v 3 [LLVM.sub, LLVM.sub?]

    peel_gep_limb 1, q, hq.left, s, q
    peel_limb 1, q₁, hq₁, qblk, hqblk, qlimb
    denote_step_reduce v 6 [LLVM.sub, LLVM.sub?]

    peel_gep_limb 2, q, hq.left, s, q
    peel_limb 2, q₂, hq₂, qblk, hqblk, qlimb
    denote_step_reduce v 9 [LLVM.sub, LLVM.sub?]

    peel_gep_limb 3, q, hq.left, s, q
    peel_limb 3, q₃, hq₃, qblk, hqblk, qlimb
    denote_step_reduce v 12 [LLVM.sub, LLVM.sub?]

    peel_gep_limb 4, q, hq.left, s, q
    peel_limb 4, q₄, hq₄, qblk, hqblk, qlimb
    denote_step_reduce v 15 [LLVM.sub, LLVM.sub?]

    -- a loaded limb is the spec's, once the `getelementptr` offset is
    -- normalised; `hq.right` rules out the pointer wrapping
    have hql : ∀ (i : Fin 5) (d : BitVec 64), d.toNat = 8 * i.toNat →
        (qblk.bytes.extractLsb' (q.withOffset d).offsetInBits 64).toNat = qinput i := by
      rintro i d hd
      have h5 : i.toNat < 5 := i.isLt
      rw [limbOffsetInBits hq.right (k := i.toNat) (by omega) hd]
      simpa [readLimb?, MemoryState.live?, hqblk] using hqinput i
    have qb : ∀ i : Fin 5, qinput i ≤ biasLimb i :=
      fun i => biasBounds_readLimb? hq hqbounds i _ (hqinput i)
    -- limb 0 is loaded straight off the base pointer, with no `getelementptr`
    have m1 : (0xfffffffffffda#64 - qlimb₀).toNat = 0xfffffffffffda - qinput 0 :=
      opp_limb_toNat (by simpa [readLimb?, MemoryState.live?, hqblk, hqlimb₀] using hqinput 0)
        (qb 0) (by norm_num)
    have m2 : (0xffffffffffffe#64 - qlimb₁).toNat = 0xffffffffffffe - qinput 1 :=
      opp_limb_toNat (by rw [hqlimb₁]; exact hql 1 8#64 (by simp)) (qb 1) (by norm_num)
    have m3 : (0xffffffffffffe#64 - qlimb₂).toNat = 0xffffffffffffe - qinput 2 :=
      opp_limb_toNat (by rw [hqlimb₂]; exact hql 2 16#64 (by simp)) (qb 2) (by norm_num)
    have m4 : (0xffffffffffffe#64 - qlimb₃).toNat = 0xffffffffffffe - qinput 3 :=
      opp_limb_toNat (by rw [hqlimb₃]; exact hql 3 24#64 (by simp)) (qb 3) (by norm_num)
    have m5 : (0xffffffffffffe#64 - qlimb₄).toNat = 0xffffffffffffe - qinput 4 :=
      opp_limb_toNat (by rw [hqlimb₄]; exact hql 4 32#64 (by simp)) (qb 4) (by norm_num)

    have hout : ∀ (u : BitVec 64) (i : Fin 5), u.toNat = output i → u = outputBV i :=
      fun _ _ h => eq_ofNat_of_toNat h
    rw [hout _ 0 m1] at hv3
    rw [hout _ 1 m2] at hv6
    rw [hout _ 2 m3] at hv9
    rw [hout _ 3 m4] at hv12
    rw [hout _ 4 m5] at hv15
    rw [hv3, hv6, hv9, hv12, hv15]

    store_limbs outputBV, o, ho.left, s

    simp_return
    simp [houtMem, hs₁, hs₂, hs₃, hs₄, o₁, o₂, o₃, o₄]


end Firedancer.Ref
