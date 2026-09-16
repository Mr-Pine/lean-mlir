import SSA.Projects.Firedancer.Ref.Spec.Fiat.fiat_25519_add
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_add
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Limb


namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

def add_repr (p q : Fin 5 → Nat) :=
  ![p 0 + q 0, p 1 + q 1, p 2 + q 2, p 3 + q 3, p 4 + q 4]

lemma add_repr_bounds (p q : Fin 5 → Nat) (i : Fin 5) {Bp Bq : ℕ}
    (hp : ∀ (i : Fin 5), p i ≤ Bp) (hq : ∀ (i : Fin 5), q i ≤ Bq)
    (hB : Bp + Bq ≤ 0x18000000000000) :
    add_repr p q i ≤ 0x18000000000000 := by
  have p0 := hp 0; have p1 := hp 1; have p2 := hp 2; have p3 := hp 3; have p4 := hp 4
  have q0 := hq 0; have q1 := hq 1; have q2 := hq 2; have q3 := hq 3; have q4 := hq 4
  simp only [add_repr]
  fin_cases i <;> simp <;> omega

/-- One limb of the region's `add`, over `toNat`. Below `2 ^ 64` the machine
`add` does not wrap. The region computes `q + p`, hence the operand order. -/
theorem add_limb_toNat {a b : BitVec 64} {m n : ℕ} (ha : a.toNat = m) (hb : b.toNat = n)
    (hmn : m + n < 2 ^ 64) :
    (b + a).toNat = m + n := by
  rw [BitVec.toNat_add, ha, hb]
  omega

lemma add_repr_correct (p q : Fin 5 → Nat) :
    decodeFieldElem (add_repr p q) = decodeFieldElem p + decodeFieldElem q := by
  simp only [decodeFieldElem, add_repr]
  push_cast
  ring

set_option maxHeartbeats 3200000 in
theorem fiat_25519_add_conforms (o p q: Pointer) (s: GlobalState)
  (hs : s.WF)
  {Bp Bq : ℕ}
  (hpbounds : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l ≤ Bp)
  (hqbounds : ∀ (i : Fin 5) (l : ℕ), readLimb? q i s.mem = some l → l ≤ Bq)
  (ho: IsFieldElemPtr s.mem o)
  (hp: IsFieldElemPtr s.mem p)
  (hq: IsFieldElemPtr s.mem q)
  (hB : Bp + Bq ≤ 0x18000000000000 := by norm_num) :
  fiat_25519_add_spec o p q s ho hp hq := by
    simp only [fiat_25519_add_spec, Cfg.denote]

    obtain ⟨pblk, hpblk, hplen⟩ := id hp.left
    obtain ⟨qblk, hqblk, hqlen⟩ := id hq.left

    obtain ⟨pinput, hpinput⟩ := exists_limbs hpblk
    obtain ⟨qinput, hqinput⟩ := exists_limbs hqblk
    have pb : ∀ i : Fin 5, pinput i ≤ Bp := fun i => hpbounds i _ (hpinput i)
    have qb : ∀ i : Fin 5, qinput i ≤ Bq := fun i => hqbounds i _ (hqinput i)
    have hlt : ∀ i : Fin 5, pinput i + qinput i < 2 ^ 64 :=
      fun i => ((Nat.add_le_add (pb i) (qb i)).trans hB).trans_lt (by norm_num)
    let output := add_repr pinput qinput
    let outputBV := BitVec.ofNat 64 ∘ output
    have output_bounds : ∀ i : Fin 5, output i ≤ 0x18000000000000 :=
      fun i => add_repr_bounds pinput qinput i pb qb hB

    refine ⟨outputBV, ?value, ?bounds, ?exec⟩

    case value =>
      have hout : readFieldElem? o (s.mem.splice o (packLimbs outputBV))
          = some (decodeFieldElem fun i => (outputBV i).toNat) := by
        rw [readFieldElem?_splice _ ho.left]
        simp only [extractLsb'_packLimbs]
      have hp' : readFieldElem? p s.mem = some (decodeFieldElem pinput) := by
        simp [readFieldElem?, hpinput, vec_eq]
      have hq' : readFieldElem? q s.mem = some (decodeFieldElem qinput) := by
        simp [readFieldElem?, hqinput, vec_eq]
      rw [readFieldElem_eq_of hout, readFieldElem_eq_of hp', readFieldElem_eq_of hq']
      -- every limb is below `2 ^ 64`, so `ofNat` does not truncate
      have htoNat : (fun i : Fin 5 => (outputBV i).toNat) = output := by
        funext i
        simp only [outputBV, Function.comp_apply, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt ((output_bounds i).trans_lt (by norm_num))
      rw [htoNat]
      exact add_repr_correct pinput qinput
    case bounds =>
      intro i
      simp only [readLimb, limbReadbackPack s.mem o outputBV ho.left i, Option.get_some,
        outputBV, Function.comp_apply, BitVec.toNat_ofNat]
      exact (Nat.mod_le _ _).trans (output_bounds i)
    case exec =>
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

    denote_expose

    peel_limb 0, p, hp.left, pblk, hpblk, plimb
    peel_limb 0, q, hq.left, qblk, hqblk, qlimb
    denote_step_reduce v 2 [LLVM.add, LLVM.add?]

    peel_gep_limb 1, p, hp.left, s, p
    peel_limb 1, p₁, hp₁, pblk, hpblk, plimb
    peel_gep_limb 1, q, hq.left, s, q
    peel_limb 1, q₁, hq₁, qblk, hqblk, qlimb
    denote_step_reduce v 7 [LLVM.add, LLVM.add?]

    peel_gep_limb 2, p, hp.left, s, p
    peel_limb 2, p₂, hp₂, pblk, hpblk, plimb
    peel_gep_limb 2, q, hq.left, s, q
    peel_limb 2, q₂, hq₂, qblk, hqblk, qlimb
    denote_step_reduce v 12 [LLVM.add, LLVM.add?]

    peel_gep_limb 3, p, hp.left, s, p
    peel_limb 3, p₃, hp₃, pblk, hpblk, plimb
    peel_gep_limb 3, q, hq.left, s, q
    peel_limb 3, q₃, hq₃, qblk, hqblk, qlimb
    denote_step_reduce v 17 [LLVM.add, LLVM.add?]

    peel_gep_limb 4, p, hp.left, s, p
    peel_limb 4, p₄, hp₄, pblk, hpblk, plimb
    peel_gep_limb 4, q, hq.left, s, q
    peel_limb 4, q₄, hq₄, qblk, hqblk, qlimb
    denote_step_reduce v 22 [LLVM.add, LLVM.add?]

    -- a loaded limb is the spec's: `readLimb?` reads the same range of the same
    -- block, once the `getelementptr` offset is normalised
    have hpl : ∀ (i : Fin 5) (d : BitVec 64), d.toNat = 8 * i.toNat →
        (pblk.bytes.extractLsb' (p.withOffset d).offsetInBits 64).toNat = pinput i := by
      rintro i d hd
      have h5 : i.toNat < 5 := i.isLt
      rw [limbOffsetInBits hp.right (k := i.toNat) (by omega) hd]
      simpa [readLimb?, MemoryState.live?, hpblk] using hpinput i
    have hql : ∀ (i : Fin 5) (d : BitVec 64), d.toNat = 8 * i.toNat →
        (qblk.bytes.extractLsb' (q.withOffset d).offsetInBits 64).toNat = qinput i := by
      rintro i d hd
      have h5 : i.toNat < 5 := i.isLt
      rw [limbOffsetInBits hq.right (k := i.toNat) (by omega) hd]
      simpa [readLimb?, MemoryState.live?, hqblk] using hqinput i

    have m1 : (qlimb₀ + plimb₀).toNat = pinput 0 + qinput 0 :=
      add_limb_toNat (by simpa [readLimb?, MemoryState.live?, hpblk, hplimb₀] using hpinput 0)
        (by simpa [readLimb?, MemoryState.live?, hqblk, hqlimb₀] using hqinput 0) (hlt 0)
    have m2 : (qlimb₁ + plimb₁).toNat = pinput 1 + qinput 1 :=
      add_limb_toNat (by rw [hplimb₁]; exact hpl 1 8#64 (by simp))
        (by rw [hqlimb₁]; exact hql 1 8#64 (by simp)) (hlt 1)
    have m3 : (qlimb₂ + plimb₂).toNat = pinput 2 + qinput 2 :=
      add_limb_toNat (by rw [hplimb₂]; exact hpl 2 16#64 (by simp))
        (by rw [hqlimb₂]; exact hql 2 16#64 (by simp)) (hlt 2)
    have m4 : (qlimb₃ + plimb₃).toNat = pinput 3 + qinput 3 :=
      add_limb_toNat (by rw [hplimb₃]; exact hpl 3 24#64 (by simp))
        (by rw [hqlimb₃]; exact hql 3 24#64 (by simp)) (hlt 3)
    have m5 : (qlimb₄ + plimb₄).toNat = pinput 4 + qinput 4 :=
      add_limb_toNat (by rw [hplimb₄]; exact hpl 4 32#64 (by simp))
        (by rw [hqlimb₄]; exact hql 4 32#64 (by simp)) (hlt 4)

    have hout : ∀ (u : BitVec 64) (i : Fin 5), u.toNat = output i → u = outputBV i :=
      fun _ _ h => eq_ofNat_of_toNat h
    rw [hout _ 0 m1] at hv2
    rw [hout _ 1 m2] at hv7
    rw [hout _ 2 m3] at hv12
    rw [hout _ 3 m4] at hv17
    rw [hout _ 4 m5] at hv22
    rw [hv2, hv7, hv12, hv17, hv22]

    store_limbs outputBV, o, ho.left, s

    simp_return
    simp [houtMem, hs₁, hs₂, hs₃, hs₄, o₁, o₂, o₃, o₄]

end Firedancer.Ref
