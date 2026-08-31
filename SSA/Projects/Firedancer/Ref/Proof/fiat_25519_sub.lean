import SSA.Projects.Firedancer.Ref.Spec.fiat_25519_sub
import SSA.Projects.Firedancer.Ref.Mlir.fiat_25519_sub
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Limb


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

lemma sub_repr_bounds (p q : Fin 5 → Nat) (i: Fin 5)
  (hpbounds : ∀ (i : Fin 5), p i ≤ 0x8000000000000) : sub_repr p q i ≤ 0x18000000000000 := by
    -- only `p`'s bound matters: `-` is truncated, so subtracting `q i` can only
    -- lower the limb. omega needs the bounds at the same atoms the goal has, so
    -- they are instantiated before the case split.
    have h0 := hpbounds 0; have h1 := hpbounds 1; have h2 := hpbounds 2
    have h3 := hpbounds 3; have h4 := hpbounds 4
    simp only [sub_repr]
    fin_cases i <;> simp <;> omega

/-- One limb of the region's `add bias; sub` pair, over `toNat`. At fiat's input
bound the bias outweighs `q`'s limb on its own, so neither the `add` nor the
`sub` wraps and the 64-bit chain agrees with `sub_repr`'s `ℕ` one. -/
theorem sub_limb_toNat {a b : BitVec 64} {c m n : ℕ} (ha : a.toNat = m) (hb : b.toNat = n)
    (hn : n ≤ 0x8000000000000) (hm : m ≤ 0x8000000000000)
    (hc : 0x8000000000000 ≤ c) (hc' : c < 2 ^ 53) :
    ((a + BitVec.ofNat 64 c) - b).toNat = (c + m) - n := by
  have hadd : (a + BitVec.ofNat 64 c).toNat = m + c := by
    rw [BitVec.toNat_add, ha, BitVec.toNat_ofNat]; omega
  rw [BitVec.toNat_sub, hadd, hb]
  omega

lemma sub_repr_correct (q r : Fin 5 → Nat)
  (hr : ∀ (i : Fin 5), r i ≤ 0x8000000000000) : decodeFieldElem (sub_repr q r) = (decodeFieldElem q) - (decodeFieldElem r) := by
  have p_separation : decodeFieldElem (sub_repr q r) = (decodeFieldElem ![0xfffffffffffda, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe]) + decodeFieldElem q - decodeFieldElem r := by
    simp [decodeFieldElem, sub_repr]
    -- each limb's `-` is a genuine subtraction: the bias alone already exceeds
    -- `q i`, so `Nat.cast_sub` applies and the whole thing is linear
    have e0 : r 0 ≤ 0xfffffffffffda + q 0 := by have := hr 0; omega
    have e1 : r 1 ≤ 0xffffffffffffe + q 1 := by have := hr 1; omega
    have e2 : r 2 ≤ 0xffffffffffffe + q 2 := by have := hr 2; omega
    have e3 : r 3 ≤ 0xffffffffffffe + q 3 := by have := hr 3; omega
    have e4 : r 4 ≤ 0xffffffffffffe + q 4 := by have := hr 4; omega
    rw [Nat.cast_sub e0, Nat.cast_sub e1, Nat.cast_sub e2, Nat.cast_sub e3, Nat.cast_sub e4]
    push_cast
    ring
  -- the bias is exactly `2 * p`, hence `0` in `ZMod p` -- as is `↑p` itself
  have p_decode : decodeFieldElem ![0xfffffffffffda, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe] = p := by
    have hS : (4503599627370458 + 4503599627370494 * 2 ^ 51 + 4503599627370494 * 2 ^ 102
        + 4503599627370494 * 2 ^ 153 + 4503599627370494 * 2 ^ 204 : ℕ) = 2 * _root_.p := by
      norm_num [_root_.p]
    have hcast := congrArg (fun n : ℕ => (n : ZMod _root_.p)) hS
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_self,
      mul_zero] at hcast
    simpa [decodeFieldElem] using hcast
  rw [p_separation, p_decode, ZMod.natCast_self, zero_add]

set_option maxHeartbeats 3200000 in
theorem fiat_25519_sub_conforms (o p q: Pointer) (s: GlobalState)
  (hpbounds : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l ≤ 0x8000000000000)
  (hqbounds : ∀ (i : Fin 5) (l : ℕ), readLimb? q i s.mem = some l → l ≤ 0x8000000000000)
  (ho: IsFieldElemPtr s.mem o)
  (hp: IsFieldElemPtr s.mem p)
  (hq: IsFieldElemPtr s.mem q) :
  fiat_25519_sub_spec o p q s := by
    simp only [fiat_25519_sub_spec, Cfg.denote]

    obtain ⟨pblk, hpblk, hplen⟩ := id hp.left
    obtain ⟨qblk, hqblk, hqlen⟩ := id hq.left

    obtain ⟨pinput, hpinput⟩ := exists_limbs hpblk
    obtain ⟨qinput, hqinput⟩ := exists_limbs hqblk
    let output := sub_repr pinput qinput
    let outputBV := BitVec.ofNat 64 ∘ output

    refine ⟨outputBV 4 ++ outputBV 3 ++ outputBV 2 ++ outputBV 1 ++ outputBV 0, ?_⟩

    constructor
    case right =>
      simp [readFieldElem?, hqinput, hpinput, ho, limbReadback, outputBV]
      have pinput_bounds (j: Fin 5) : pinput j ≤ 0x8000000000000 := by simp only [hpinput, hpbounds j]
      have qinput_bounds (j: Fin 5) : qinput j ≤ 0x8000000000000 := by simp only [hqinput, hqbounds j]
      have output_bounds (i: Fin 5) : output i ≤ 0x18000000000000 := by
        simp only [output]
        simp only [sub_repr_bounds pinput qinput i pinput_bounds]
      have loose_output_bounds (i: Fin 5) : output i < 18446744073709551616 :=
        (output_bounds i).trans_lt (by norm_num)
      simp [loose_output_bounds, Nat.mod_eq_of_lt]
      constructor
      simp only [vec_eq, HSub.hSub, output, sub_repr_correct pinput qinput qinput_bounds]

      intro i
      -- the stored vector is `output` pushed through `ofNat`, limb by limb; the
      -- `ofNat` truncation can only lower a limb, so the bound carries over
      simp only [vec_eq (fun j => BitVec.ofNat 64 (output j)), BitVec.toNat_ofNat]
      exact (Nat.mod_le _ _).trans (output_bounds i)

    let output_state : GlobalState :=
      { s with
        mem := ((((s.mem.splice o (outputBV 0)).splice (o.withOffset 8) (outputBV 1)).splice
                  (o.withOffset 16) (outputBV 2)).splice (o.withOffset 24) (outputBV 3)).splice
                  (o.withOffset 32) (outputBV 4) }
    refine ⟨output_state, ?_, ?_⟩
    pick_goal 2

    exact GlobalState.Equiv.symm (splice5_equiv (outputBV 0) (outputBV 1) (outputBV 2)
      (outputBV 3) (outputBV 4) ho)

    denote_step_all v 5
    denote_eval v 0 5
    simp only [LLVM.const?] at hv0 hv1 hv2 hv3 hv4 hv5
    subst hv0 hv1 hv2 hv3 hv4 hv5

    peel_limb 0, p, hp.left, pblk, hpblk, plimb
    denote_step_all v 7
    denote_eval v 7 7
    eval_llvm 7
    peel_limb 0, q, hq.left, qblk, hqblk, qlimb
    denote_step_all v 9
    denote_eval v 9 9
    eval_llvm 9 as x1
    denote_clear v 7 7

    peel_gep_limb 1, p, hp.left, s, p
    peel_limb 1, p₁, hp₁, pblk, hpblk, plimb
    denote_step_all v 12
    denote_eval v 12 12
    eval_llvm 12
    peel_gep_limb 1, q, hq.left, s, q
    peel_limb 1, q₁, hq₁, qblk, hqblk, qlimb
    denote_step_all v 15
    denote_eval v 15 15
    eval_llvm 15 as x2
    denote_clear v 12 12

    peel_gep_limb 2, p, hp.left, s, p
    peel_limb 2, p₂, hp₂, pblk, hpblk, plimb
    denote_step_all v 18
    denote_eval v 18 18
    eval_llvm 18
    peel_gep_limb 2, q, hq.left, s, q
    peel_limb 2, q₂, hq₂, qblk, hqblk, qlimb
    denote_step_all v 21
    denote_eval v 21 21
    eval_llvm 21 as x3
    denote_clear v 18 18

    peel_gep_limb 3, p, hp.left, s, p
    peel_limb 3, p₃, hp₃, pblk, hpblk, plimb
    denote_step_all v 24
    denote_eval v 24 24
    eval_llvm 24
    peel_gep_limb 3, q, hq.left, s, q
    peel_limb 3, q₃, hq₃, qblk, hqblk, qlimb
    denote_step_all v 27
    denote_eval v 27 27
    eval_llvm 27 as x4
    denote_clear v 24 24

    peel_gep_limb 4, p, hp.left, s, p
    peel_limb 4, p₄, hp₄, pblk, hpblk, plimb
    denote_step_all v 30
    denote_eval v 30 30
    eval_llvm 30
    peel_gep_limb 4, q, hq.left, s, q
    peel_limb 4, q₄, hq₄, qblk, hqblk, qlimb
    denote_step_all v 33
    denote_eval v 33 33
    eval_llvm 33 as x5
    denote_clear v 30 30

    -- a loaded limb is the spec's: `readLimb?` reads the same range of the same
    -- block, once the `getelementptr` offset is normalised. `hp'`/`hq'` are what
    -- rule out the pointer wrapping.
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
    have pb : ∀ i : Fin 5, pinput i ≤ 0x8000000000000 := fun i => hpbounds i _ (hpinput i)
    have qb : ∀ i : Fin 5, qinput i ≤ 0x8000000000000 := fun i => hqbounds i _ (hqinput i)
    -- limb 0 is loaded straight off the base pointer, with no `getelementptr`
    have m1 : x1.toNat = (0xfffffffffffda + pinput 0) - qinput 0 := by
      rw [← hx1]
      exact sub_limb_toNat (by simpa [readLimb?, MemoryState.live?, hpblk, hplimb₀] using hpinput 0)
        (by simpa [readLimb?, MemoryState.live?, hqblk, hqlimb₀] using hqinput 0)
        (qb 0) (pb 0) (by norm_num) (by norm_num)
    have m2 : x2.toNat = (0xffffffffffffe + pinput 1) - qinput 1 := by
      rw [← hx2]
      exact sub_limb_toNat (by rw [hplimb₁]; exact hpl 1 8#64 (by simp))
        (by rw [hqlimb₁]; exact hql 1 8#64 (by simp))
        (qb 1) (pb 1) (by norm_num) (by norm_num)
    have m3 : x3.toNat = (0xffffffffffffe + pinput 2) - qinput 2 := by
      rw [← hx3]
      exact sub_limb_toNat (by rw [hplimb₂]; exact hpl 2 16#64 (by simp))
        (by rw [hqlimb₂]; exact hql 2 16#64 (by simp))
        (qb 2) (pb 2) (by norm_num) (by norm_num)
    have m4 : x4.toNat = (0xffffffffffffe + pinput 3) - qinput 3 := by
      rw [← hx4]
      exact sub_limb_toNat (by rw [hplimb₃]; exact hpl 3 24#64 (by simp))
        (by rw [hqlimb₃]; exact hql 3 24#64 (by simp))
        (qb 3) (pb 3) (by norm_num) (by norm_num)
    have m5 : x5.toNat = (0xffffffffffffe + pinput 4) - qinput 4 := by
      rw [← hx5]
      exact sub_limb_toNat (by rw [hplimb₄]; exact hpl 4 32#64 (by simp))
        (by rw [hqlimb₄]; exact hql 4 32#64 (by simp))
        (qb 4) (pb 4) (by norm_num) (by norm_num)

    have hout : ∀ (u : BitVec 64) (i : Fin 5), u.toNat = output i → u = outputBV i :=
      fun _ _ h => eq_ofNat_of_toNat h
    -- `output i` is `sub_repr pinput qinput i`, which reduces straight to `mᵢ`'s
    -- right-hand side. Routing through `![x1.toNat, ..]` instead makes the kernel
    -- unfold the `xᵢ` limb chain and blow its stack.
    rw [hout _ 0 m1] at hv9
    rw [hout _ 1 m2] at hv15
    rw [hout _ 2 m3] at hv21
    rw [hout _ 3 m4] at hv27
    rw [hout _ 4 m5] at hv33
    rw [hv9, hv15, hv21, hv27, hv33]

    store_limbs outputBV, o, ho.left, s


    simp only [BlockCom.denote_term, Terminator.denote_ret, output_state,
      hs₁, hs₂, hs₃, hs₄, o₁, o₂, o₃, o₄, simp_denote, simp_sllvm]

end Firedancer.Ref
