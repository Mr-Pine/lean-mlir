module

public import SSA.Projects.Firedancer.Ref.Spec.Fiat.fiat_25519_sub
public import SSA.Projects.Firedancer.Ref.Spec.Bias
public import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_sub
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Proof.Tactics
public import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
public import SSA.Projects.Firedancer.Ref.Proof.Limb

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

def sub_repr (p q : Fin 5 → Nat) :=
  let x1 := (0xfffffffffffda + p 0) - q 0
  let x2 := (0xffffffffffffe + p 1) - q 1
  let x3 := (0xffffffffffffe + p 2) - q 2
  let x4 := (0xffffffffffffe + p 3) - q 3
  let x5 := (0xffffffffffffe + p 4) - q 4
  ![x1, x2, x3, x4, x5]

lemma sub_repr_bounds (p q : Fin 5 → Nat) (i : Fin 5)
    (hpbounds : ∀ (i : Fin 5), p i ≤ 0x8000000000000) : sub_repr p q i ≤ 0x18000000000000 := by
  -- only `p`'s bound matters: `-` is truncated, so subtracting `q i` can only
  -- lower the limb. omega needs the bounds at the same atoms the goal has, so
  -- they are instantiated before the case split.
  have h0 := hpbounds 0; have h1 := hpbounds 1; have h2 := hpbounds 2
  have h3 := hpbounds 3; have h4 := hpbounds 4
  simp only [sub_repr]
  fin_cases i <;> simp <;> omega

/-- One limb of the region's `add bias; sub` pair, over `toNat`. The subtrahend
is at most the bias limb `c` itself, so neither the `add` nor the `sub` wraps
and the 64-bit chain agrees with `sub_repr`'s `ℕ` one. A carried operand is
below `c`; so is a `fiat_25519_opp` result, which is what lets `fd_f25519_eq`
compare against one. -/
theorem sub_limb_toNat {a b : BitVec 64} {c m n : ℕ} (ha : a.toNat = m) (hb : b.toNat = n)
    (hn : n ≤ c) (hm : m ≤ 0x8000000000000) (hc' : c < 2 ^ 53) :
    ((a + BitVec.ofNat 64 c) - b).toNat = (c + m) - n := by
  have hadd : (a + BitVec.ofNat 64 c).toNat = m + c := by
    rw [BitVec.toNat_add, ha, BitVec.toNat_ofNat]; omega
  rw [BitVec.toNat_sub, hadd, hb]
  omega

lemma sub_repr_correct (q r : Fin 5 → Nat) (hr : ∀ (i : Fin 5), r i ≤ biasLimb i) :
    decodeFieldElem (sub_repr q r) = (decodeFieldElem q) - (decodeFieldElem r) := by
  have p_separation :
    decodeFieldElem (sub_repr q r) =
      (decodeFieldElem
            ![0xfffffffffffda, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe,
              0xffffffffffffe]) +
          decodeFieldElem q -
        decodeFieldElem r := by
    simp [decodeFieldElem, sub_repr]
    -- each limb's `-` is a genuine subtraction: the bias alone already exceeds
    -- `q i`, so `Nat.cast_sub` applies and the whole thing is linear
    have e0 : r 0 ≤ 0xfffffffffffda + q 0 := by
      have := hr 0; simp at this; omega
    have e1 : r 1 ≤ 0xffffffffffffe + q 1 := by
      have := hr 1; simp at this; omega
    have e2 : r 2 ≤ 0xffffffffffffe + q 2 := by
      have := hr 2; simp at this; omega
    have e3 : r 3 ≤ 0xffffffffffffe + q 3 := by
      have := hr 3; simp at this; omega
    have e4 : r 4 ≤ 0xffffffffffffe + q 4 := by
      have := hr 4; simp at this; omega
    rw [Nat.cast_sub e0, Nat.cast_sub e1, Nat.cast_sub e2, Nat.cast_sub e3, Nat.cast_sub e4]
    push_cast
    ring
  -- the bias is exactly `2 * p`, hence `0` in `ZMod p` -- as is `↑p` itself
  have p_decode :
    decodeFieldElem
        ![0xfffffffffffda, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe] =
      p := by
    have hS :
      (4503599627370458 + 4503599627370494 * 2 ^ 51 + 4503599627370494 * 2 ^ 102 +
            4503599627370494 * 2 ^ 153 +
            4503599627370494 * 2 ^ 204 :
          ℕ) =
        2 * _root_.p := by
      norm_num [_root_.p]
    have hcast := congrArg (fun n : ℕ => (n : ZMod _root_.p)) hS
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_self,
      mul_zero] at hcast
    simpa [decodeFieldElem] using hcast
  rw [p_separation, p_decode, ZMod.natCast_self, zero_add]

set_option maxHeartbeats 3200000 in
theorem fiat_25519_sub_conforms (o p q : Pointer) (s : GlobalState) (hs : s.WF)
    (hpbounds : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l ≤ 0x8000000000000)
    (hqbounds : BiasBounds? q s.mem) (ho : IsFieldElemPtr s.mem o) (hp : IsFieldElemPtr s.mem p)
    (hq : IsFieldElemPtr s.mem q) : fiat_25519_sub_spec o p q s ho hp hq := by
  -- the walk produces the limbwise forms; read them back once, here
  suffices h :
    ∃ out : BitVec (5 * 64),
        let output_state : GlobalState := { s with mem := s.mem.splice o out }
        (∃ s' : GlobalState,
          StateT.run
                (runFunction
                  (fiat_25519_sub.denote
                    (Ctxt.Valuation.ofHVector [.value q, .value p, .value o]ₕ)))
                s =
              .value ([]ₕ, s') ∧
            output_state ≈ s') ∧
        (readFieldElem? o output_state.mem =
            Sub.sub <$> readFieldElem? p s.mem <*> readFieldElem? q s.mem ∧
          ∀ (i : Fin 5) (l : ℕ), readLimb? o i output_state.mem = some l → l ≤ 0x18000000000000) ∧
        ∀ (i : Fin 5) (lp lq : ℕ),
          readLimb? p i s.mem = some lp →
            readLimb? q i s.mem = some lq →
            readLimb? o i output_state.mem = some (biasLimb i + lp - lq)
    by
    obtain ⟨out, hrun, ⟨hval, hbnd⟩, hlimbs⟩ := h
    refine
      ⟨out, ?_, limbBounds_of_readLimb? _ hbnd, hrun, fun i =>
        hlimbs i _ _ (Option.some_get _).symm (Option.some_get _).symm⟩
    refine readFieldElem_eq_of ?_
    rw [hval, show readFieldElem? p s.mem = some (readFieldElem hp) from (Option.some_get _).symm,
      show readFieldElem? q s.mem = some (readFieldElem hq) from (Option.some_get _).symm]
    rfl
  simp only [Cfg.denote]
  obtain ⟨pblk, hpblk, hplen⟩ := id hp.left
  obtain ⟨qblk, hqblk, hqlen⟩ := id hq.left
  obtain ⟨pinput, hpinput⟩ := exists_limbs hpblk
  obtain ⟨qinput, hqinput⟩ := exists_limbs hqblk
  let output := sub_repr pinput qinput
  let outputBV := BitVec.ofNat 64 ∘ output
  refine ⟨packLimbs outputBV, ?left, ?right, ?limbs⟩
  case limbs =>
    intro i lp lq hlp hlq
    have hpl : pinput i = lp := Option.some.inj ((hpinput i).symm.trans hlp)
    have hql : qinput i = lq := Option.some.inj ((hqinput i).symm.trans hlq)
    have hlt : output i < 2 ^ 64 :=
      (sub_repr_bounds pinput qinput i fun j => hpbounds j _ (hpinput j)).trans_lt (by norm_num)
    rw [limbReadbackPack s.mem o outputBV ho.left i]
    show some (BitVec.ofNat 64 (output i)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, ← hpl, ← hql]
    fin_cases i <;> rfl
  case right =>
    simp [readFieldElem?, hqinput, hpinput, ho, limbReadbackPack, outputBV]
    have pinput_bounds (j : Fin 5) : pinput j ≤ 0x8000000000000 := by
      simp only [hpinput, hpbounds j]
    have qinput_bounds (j : Fin 5) : qinput j ≤ biasLimb j := by simp only [hqinput, hqbounds j]
    have output_bounds (i : Fin 5) : output i ≤ 0x18000000000000 := by
      simp only [output]
      simp only [sub_repr_bounds pinput qinput i pinput_bounds]
    have loose_output_bounds (i : Fin 5) : output i < 18446744073709551616 :=
      (output_bounds i).trans_lt (by norm_num)
    simp [loose_output_bounds, Nat.mod_eq_of_lt]
    constructor
    simp only [vec_eq, HSub.hSub, output, sub_repr_correct pinput qinput qinput_bounds]
    intro i
    exact output_bounds i
  obtain ⟨outMem, houtMem⟩ :
    ∃ m : MemoryState,
      m =
        ((((s.mem.splice o (outputBV 0)).splice (o.withOffset 8) (outputBV 1)).splice
                  (o.withOffset 16) (outputBV 2)).splice
              (o.withOffset 24) (outputBV 3)).splice
          (o.withOffset 32) (outputBV 4) :=
    ⟨_, rfl⟩
  refine ⟨s.popFrame outMem, run_runFunction (s' := { s with mem := outMem }) ?_, ?equiv⟩
  case
    equiv =>
    have hnone : ∀ (b : BlockId), s.alloc.nextFreeBlock ≤ b.id → outMem.live? b = none := by
      rw [houtMem]
      exact fun b hb =>
        live?_splice_eq_none
          (live?_splice_eq_none
            (live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none (hs b hb)))))
    refine
      GlobalState.Equiv.trans ?_
        (GlobalState.Equiv.symm (killFrom_equiv_of_none (s := s) (m := outMem) hnone))
    rw [houtMem]
    exact
      GlobalState.Equiv.symm
        (splice5_equiv (outputBV 0) (outputBV 1) (outputBV 2) (outputBV 3) (outputBV 4) ho)
  denote_step_reduce v 1 [LLVM.const?] fold
  subst hv0 hv1
  peel_limb 0, p, hp.left, pblk, hpblk, plimb
  denote_step_reduce v 3 [LLVM.add, LLVM.add?]
  peel_limb 0, q, hq.left, qblk, hqblk, qlimb
  denote_step_reduce v 5 [LLVM.sub, LLVM.sub?, hv3]
  denote_clear v 3 3
  peel_gep_limb 1, p, hp.left, s, p
  peel_limb 1, p₁, hp₁, pblk, hpblk, plimb
  denote_step_reduce v 8 [LLVM.add, LLVM.add?]
  peel_gep_limb 1, q, hq.left, s, q
  peel_limb 1, q₁, hq₁, qblk, hqblk, qlimb
  denote_step_reduce v 11 [LLVM.sub, LLVM.sub?, hv8]
  denote_clear v 8 8
  peel_gep_limb 2, p, hp.left, s, p
  peel_limb 2, p₂, hp₂, pblk, hpblk, plimb
  denote_step_reduce v 14 [LLVM.add, LLVM.add?]
  peel_gep_limb 2, q, hq.left, s, q
  peel_limb 2, q₂, hq₂, qblk, hqblk, qlimb
  denote_step_reduce v 17 [LLVM.sub, LLVM.sub?, hv14]
  denote_clear v 14 14
  peel_gep_limb 3, p, hp.left, s, p
  peel_limb 3, p₃, hp₃, pblk, hpblk, plimb
  denote_step_reduce v 20 [LLVM.add, LLVM.add?]
  peel_gep_limb 3, q, hq.left, s, q
  peel_limb 3, q₃, hq₃, qblk, hqblk, qlimb
  denote_step_reduce v 23 [LLVM.sub, LLVM.sub?, hv20]
  denote_clear v 20 20
  peel_gep_limb 4, p, hp.left, s, p
  peel_limb 4, p₄, hp₄, pblk, hpblk, plimb
  denote_step_reduce v 26 [LLVM.add, LLVM.add?]
  peel_gep_limb 4, q, hq.left, s, q
  peel_limb 4, q₄, hq₄, qblk, hqblk, qlimb
  denote_step_reduce v 29 [LLVM.sub, LLVM.sub?, hv26]
  denote_clear v 26 26
  -- a loaded limb is the spec's: `readLimb?` reads the same range of the same
  -- block, once the `getelementptr` offset is normalised; `hp.right`/`hq.right`
  -- rule out the pointer wrapping.
  have hpl :
    ∀ (i : Fin 5) (d : BitVec 64),
      d.toNat = 8 * i.toNat →
        (pblk.bytes.extractLsb' (p.withOffset d).offsetInBits 64).toNat = pinput i := by
    rintro i d hd
    have h5 : i.toNat < 5 := i.isLt
    rw [limbOffsetInBits hp.right (k := i.toNat) (by omega) hd]
    simpa [readLimb?, MemoryState.live?, hpblk] using hpinput i
  have hql :
    ∀ (i : Fin 5) (d : BitVec 64),
      d.toNat = 8 * i.toNat →
        (qblk.bytes.extractLsb' (q.withOffset d).offsetInBits 64).toNat = qinput i := by
    rintro i d hd
    have h5 : i.toNat < 5 := i.isLt
    rw [limbOffsetInBits hq.right (k := i.toNat) (by omega) hd]
    simpa [readLimb?, MemoryState.live?, hqblk] using hqinput i
  have pb : ∀ i : Fin 5, pinput i ≤ 0x8000000000000 := fun i => hpbounds i _ (hpinput i)
  have qb : ∀ i : Fin 5, qinput i ≤ biasLimb i := fun i => hqbounds i _ (hqinput i)
  -- limb 0 is loaded straight off the base pointer, with no `getelementptr`
  have m1 :
    (plimb₀ + 0xfffffffffffda#64 - qlimb₀).toNat = (0xfffffffffffda + pinput 0) - qinput 0 :=
    sub_limb_toNat (by simpa [readLimb?, MemoryState.live?, hpblk, hplimb₀] using hpinput 0)
      (by simpa [readLimb?, MemoryState.live?, hqblk, hqlimb₀] using hqinput 0)
      (by simpa using qb 0) (pb 0) (by norm_num)
  have m2 :
    (plimb₁ + 0xffffffffffffe#64 - qlimb₁).toNat = (0xffffffffffffe + pinput 1) - qinput 1 :=
    sub_limb_toNat
      (by
        rw [hplimb₁]; exact hpl 1 8#64 (by simp))
      (by
        rw [hqlimb₁]; exact hql 1 8#64 (by simp))
      (by simpa using qb 1) (pb 1) (by norm_num)
  have m3 :
    (plimb₂ + 0xffffffffffffe#64 - qlimb₂).toNat = (0xffffffffffffe + pinput 2) - qinput 2 :=
    sub_limb_toNat
      (by
        rw [hplimb₂]; exact hpl 2 16#64 (by simp))
      (by
        rw [hqlimb₂]; exact hql 2 16#64 (by simp))
      (by simpa using qb 2) (pb 2) (by norm_num)
  have m4 :
    (plimb₃ + 0xffffffffffffe#64 - qlimb₃).toNat = (0xffffffffffffe + pinput 3) - qinput 3 :=
    sub_limb_toNat
      (by
        rw [hplimb₃]; exact hpl 3 24#64 (by simp))
      (by
        rw [hqlimb₃]; exact hql 3 24#64 (by simp))
      (by simpa using qb 3) (pb 3) (by norm_num)
  have m5 :
    (plimb₄ + 0xffffffffffffe#64 - qlimb₄).toNat = (0xffffffffffffe + pinput 4) - qinput 4 :=
    sub_limb_toNat
      (by
        rw [hplimb₄]; exact hpl 4 32#64 (by simp))
      (by
        rw [hqlimb₄]; exact hql 4 32#64 (by simp))
      (by simpa using qb 4) (pb 4) (by norm_num)
  have hout : ∀ (u : BitVec 64) (i : Fin 5), u.toNat = output i → u = outputBV i := fun _ _ h =>
    eq_ofNat_of_toNat h
  -- `output i` reduces straight to `mᵢ`'s right-hand side; a `![..]` of the limbs
  -- would blow the kernel's stack
  rw [hout _ 0 m1] at hv5
  rw [hout _ 1 m2] at hv11
  rw [hout _ 2 m3] at hv17
  rw [hout _ 3 m4] at hv23
  rw [hout _ 4 m5] at hv29
  rw [hv5, hv11, hv17, hv23, hv29]
  store_limbs outputBV, o, ho.left, s
  simp_return
  simp [houtMem, hs₁, hs₂, hs₃, hs₄, o₁, o₂, o₃, o₄]

end Firedancer.Ref
