/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_f25519_is_zero
import SSA.Projects.Firedancer.Avx512.Proof.Quad
import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic
import SSA.Projects.Firedancer.Avx512.Proof.Sub
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.MLIR.DenoteStep

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `Step.Basic.unflatten_readVec` with the width as the literal `512` the
region's load carries, so `rw` matches. Shares the proof; only the statement is
specialised -- the same delegation `fd_f25519_eq` and `fd_f25519_sub` use. -/
private theorem unflatten_readVec_512 {m : MemoryState} {p : Pointer} (h : IsVecPtr m p)
    {blk : LiveBlock} (hblk : m.live? p.id = some blk) :
    LLVM.Ty.unflatten (.vector 8 (.bitvec (.concrete 64)))
        (blk.bytes.extractLsb' p.offsetInBits 512)
      = (readVec h).map PoisonOr.value :=
  unflatten_readVec h hblk


/-- One `wwl_eq`, as the region computes it: the `<8 x i1>` mask of a lane-wise
`ne` compare of two defined vectors, bitcast to `i8`. The mask is a value, and
it is zero exactly when the two vectors agree in every lane -- which is what
the `icmp eq … , 0` that follows it reads. -/
theorem bitcast_vicmp_ne_zero_iff (x c : Vector (BitVec 64) 8) :
    ∃ b : BitVec 8,
      SLLVM.bitcast (.vector 8 (.bitvec (.concrete 1))) (.bitvec (.concrete 8))
          (SLLVM.vicmp LLVM.IntPred.ne (x.map PoisonOr.value) (c.map PoisonOr.value))
        = PoisonOr.value b ∧ (b = 0 ↔ x = c) := by
  set m := SLLVM.vicmp LLVM.IntPred.ne (x.map PoisonOr.value) (c.map PoisonOr.value) with hm
  have hlane : ∀ (i : Nat) (hi : i < 8),
      m[i] = PoisonOr.value (BitVec.ofBool (x[i] != c[i])) := by
    intro i hi
    simp [hm, SLLVM.vicmp, LLVM.icmp, LLVM.icmp?, LLVM.icmp']
  have hget : ∀ (i : Nat) (hi : i < 8),
      (LLVM.Ty.ofVector (l := 8) (e := (.bitvec (.concrete 1) : LLVM.Ty)) m)[i] = m[i] :=
    fun _ _ => rfl
  have hdef : LLVM.Ty.Defined (.vector 8 (.bitvec (.concrete 1))) m := by
    intro i
    show m[i.val] ≠ PoisonOr.poison
    rw [hlane i.val i.isLt]
    exact PoisonOr.value_ne_poison _
  have hsw : (LLVM.Ty.flattenBV (.vector 8 (.bitvec (.concrete 1))) m).setWidth
        (LLVM.Ty.width (.bitvec (.concrete 8)))
      = LLVM.Ty.flattenBV (.vector 8 (.bitvec (.concrete 1))) m := BitVec.setWidth_eq _
  refine ⟨LLVM.Ty.flattenBV (.vector 8 (.bitvec (.concrete 1))) m, ?_, ?_⟩
  · rw [SLLVM.bitcast_of_defined hdef, hsw]
    rfl
  constructor
  · intro hb
    apply Vector.ext
    intro i hi
    have hext := LLVM.Ty.extractLsb'_flattenBV_vector
      (l := 8) (e := (.bitvec (.concrete 1) : LLVM.Ty)) (v := m) i hi
    rw [hb, hget i hi, hlane i hi] at hext
    simp [LLVM.Ty.flattenBV, LLVM.Ty.width] at hext
    by_contra hne
    rw [bne_iff_ne.mpr hne] at hext
    simp at hext
  · intro hxc
    subst hxc
    rw [LLVM.Ty.flattenBV]
    apply BitVec.packLanes_eq_zero
    intro i hi
    simp only [Vector.getElem_ofFn]
    show LLVM.Ty.flattenBV (.bitvec (.concrete 1)) m[i] = 0
    rw [hlane i hi]
    simp [LLVM.Ty.flattenBV, LLVM.Ty.width]

/-- **The two patterns are exactly the zeros.** On a nearly reduced element
with lanes 6 and 7 clear, the bit-pattern test the region runs decides
`= 0` in `GF(2^255 - 19)`: `nearly reduced` bounds the value below `2p` and
the limbs tightly enough to make the radix-`2^43` representation unique, so
the only vectors congruent to zero are `fd_r43x6_zero()` and `fd_r43x6_p()`. -/
theorem eq_zeroVec_or_eq_pVec_iff {v : Vector (BitVec 64) 8}
    (hnr : R43x6.NearlyReduced v) (h6 : v[6] = 0) (h7 : v[7] = 0) :
    (v = zeroVec ∨ v = pVec) ↔ vecValue v = 0 := by
  constructor
  · rintro (rfl | rfl) <;> decide
  intro hz
  -- `nearly reduced` at `2^44`, which is what the `ℤ`/`ℕ` bridge asks for
  have hbnd : ∀ k : Fin R43x6.limbCount,
      0 ≤ R43x6.extractLimbs v k ∧ R43x6.extractLimbs v k < 2 ^ 44 := by
    intro k
    obtain ⟨h04, ⟨h50, h51⟩, -⟩ := hnr
    by_cases hk : (k : ℕ) < 5
    · exact ⟨(h04 k hk).1, by have := (h04 k hk).2; omega⟩
    · have hk5 : k = 5 := by
        apply Fin.ext
        have := k.isLt
        simp only [R43x6.limbCount] at this hk ⊢
        omega
      subst hk5
      exact ⟨h50, by omega⟩
  obtain ⟨h04, ⟨h50, h51⟩, hlt2p⟩ := hnr
  -- the six limbs, as the lanes `decode'_eq` reads them
  have e0 : R43x6.extractLimbs v 0 = v[0].toInt := rfl
  have e1 : R43x6.extractLimbs v 1 = v[1].toInt := rfl
  have e2 : R43x6.extractLimbs v 2 = v[2].toInt := rfl
  have e3 : R43x6.extractLimbs v 3 = v[3].toInt := rfl
  have e4 : R43x6.extractLimbs v 4 = v[4].toInt := rfl
  have e5 : R43x6.extractLimbs v 5 = v[5].toInt := rfl
  have b0 := h04 0 (by decide)
  have b1 := h04 1 (by decide)
  have b2 := h04 2 (by decide)
  have b3 := h04 3 (by decide)
  have b4 := h04 4 (by decide)
  rw [e0] at b0
  rw [e1] at b1
  rw [e2] at b2
  rw [e3] at b3
  rw [e4] at b4
  rw [e5] at h50 h51
  have hdec := R43x6.decode'_eq v
  rw [p_int] at hlt2p
  have hnonneg : 0 ≤ R43x6.decode' v := by rw [hdec]; omega
  -- the value is a multiple of `p` in `[0, 2p)`, so it is `0` or `p`
  rw [← decode'_cast_eq_vecValue v hbnd] at hz
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz
  rw [p_int] at hk
  have hk0 : 0 ≤ k := by nlinarith
  have hk2 : k < 2 := by nlinarith
  interval_cases k
  · -- the all-zero pattern
    left
    rw [hdec] at hk
    apply Vector.ext
    intro i hi
    have hz0 : v[0].toInt = 0 := by omega
    have hz1 : v[1].toInt = 0 := by omega
    have hz2 : v[2].toInt = 0 := by omega
    have hz3 : v[3].toInt = 0 := by omega
    have hz4 : v[4].toInt = 0 := by omega
    have hz5 : v[5].toInt = 0 := by omega
    interval_cases i <;>
      first
        | exact BitVec.toInt_inj.mp (by simpa [zeroVec] using ‹_›)
        | simpa [zeroVec] using ‹_›
  · -- `fd_r43x6_p()`
    right
    rw [hdec] at hk
    apply Vector.ext
    intro i hi
    have hp0 : v[0].toInt = 2 ^ 43 - 19 := by omega
    have hp1 : v[1].toInt = 2 ^ 43 - 1 := by omega
    have hp2 : v[2].toInt = 2 ^ 43 - 1 := by omega
    have hp3 : v[3].toInt = 2 ^ 43 - 1 := by omega
    have hp4 : v[4].toInt = 2 ^ 43 - 1 := by omega
    have hp5 : v[5].toInt = 2 ^ 40 - 1 := by omega
    interval_cases i <;>
      first
        | exact BitVec.toInt_inj.mp (by simpa [pVec] using ‹_›)
        | simpa [pVec] using ‹_›

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
theorem fd_f25519_is_zero_conforms (q : Pointer) (s : GlobalState) (hs : s.WF)
    (hq : IsVecPtr s.mem q) : fd_f25519_is_zero_spec q s hq := by
  simp only [fd_f25519_is_zero_spec, fd_f25519_is_zero, Cfg.denote]
  intro hnr h6 h7
  refine Firedancer.run_runFunction' _ ?_
  refine ⟨s, ?_, hs.popFrame_equiv⟩
  obtain ⟨blk, hblk, hlen⟩ := hq.1
  have hlive : s.mem.live? q.id = some blk := by simp only [MemoryState.live?, hblk]
  denote_step_all v 4
  eval_consts v 0 4
  peel_load (.vector 8 (.bitvec (.concrete 64))), blk, q, hblk, s
  rw [unflatten_readVec_512 hq hlive]
  have hd0 : LLVM.Ty.dense (.vector 8 (.bitvec (.concrete 64))) [0]
      = zeroVec.map PoisonOr.value := by
    apply Vector.ext
    intro i hi
    simp [LLVM.Ty.dense, zeroVec]
  have hdp : LLVM.Ty.dense (.vector 8 (.bitvec (.concrete 64)))
        [8796093022189, 8796093022207, 8796093022207, 8796093022207, 8796093022207,
          1099511627775, 0, 0]
      = pVec.map PoisonOr.value := by
    apply Vector.ext
    intro i hi
    simp only [LLVM.Ty.dense, Vector.getElem_ofFn, Vector.getElem_map]
    interval_cases i <;> rfl
  obtain ⟨c0, hc0, hc0z⟩ := bitcast_vicmp_ne_zero_iff (readVec hq) zeroVec
  obtain ⟨c1, hc1, hc1z⟩ := bitcast_vicmp_ne_zero_iff (readVec hq) pVec
  denote_step_reduce v 13 [hd0, hdp, hc0, hc1, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.select, LLVM.zext, LLVM.zext?] fold
  denote_clear v 6 12
  rw [hv13]
  have hiff := eq_zeroVec_or_eq_pVec_iff hnr h6 h7
  by_cases hzero : vecValue (readVec hq) = 0
  · -- one of the two compares hits, so the `select` returns `true` either way
    rw [if_pos hzero]
    rcases hiff.mpr hzero with hv | hv
    · simp [hc0z.mpr hv]
      simp only [Ctxt.Var.last, Ctxt.Valuation.cons_zero]
    · simp [hc1z.mpr hv]
      simp only [Ctxt.Var.last, Ctxt.Valuation.cons_zero]
  · -- neither pattern matches
    rw [if_neg hzero]
    have hn0 : (c0 == 0#8) = false := by
      simpa using fun h => hzero (hiff.mp (Or.inl (hc0z.mp h)))
    have hn1 : (c1 == 0#8) = false := by
      simpa using fun h => hzero (hiff.mp (Or.inr (hc1z.mp h)))
    simp [hn0, hn1]
    simp only [Ctxt.Var.last, Ctxt.Valuation.cons_zero]

end Firedancer.Avx512
