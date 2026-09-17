/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_dbln
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic
public import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_quad_sqr_fast
public import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_quad_mul_fast
public import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_dbln.Entry

/-!
# `fd_ed25519_point_dbln` conforms (AVX-512)

`^bb0` (`bb0_run`) doubles once and stores into `r`; for `n > 1` the loop
(`loop_run`) doubles `n - 1` more times and `^bb1` (`bb1_run`) stores the last
over the first. The arithmetic is `PointDbln.geDbl`
(`fd_ed25519_point_dbln/Model.lean`), `u44` to `u44`, `Point.dbl` on the point.
-/

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

namespace PointDbln
open Ge

theorem u44_iterate {q : Quad} (hq : QuadU44 q) : ∀ k, QuadU44 (geDbl^[k] q)
  | 0 => hq
  | k + 1 => by rw [Function.iterate_succ_apply']; exact u44_geDbl (u44_iterate hq k)

theorem toPoint_iterate {q : Quad} (hq : QuadU44 q) :
    ∀ k, (geDbl^[k] q).toPoint = Point.dbl^[k] q.toPoint
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      toPoint_geDbl (u44_iterate hq k), toPoint_iterate hq k]

theorem isQuadPtr_writeQuad {m : MemoryState} {r : Pointer} (hr : IsQuadPtr m r) (q : Quad) :
    IsQuadPtr (m.writeQuad r q) r :=
  ⟨fits_splice (fits_splice (fits_splice hr.1)), hr.2⟩


end PointDbln

open PointDbln Ge in
theorem fd_ed25519_point_dbln_conforms (r a : Pointer) (n : BitVec 32) (s : GlobalState)
    (hs : s.WF) (hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a)
    (hu : R43x6.U44 (readQuad ha).v03 ∧ R43x6.U44 (readQuad ha).v14 ∧ R43x6.U44 (readQuad ha).v25)
    (hn : n.toInt < 256) :
    fd_ed25519_point_dbln_spec r a n s hr ha := by
  obtain ⟨W, u, env, hF, hrun⟩ := bb0_run r a n s hs hr ha hu
  have hrlt := lt_nextFreeBlock_of_fits hs hr.1
  have hc : ∀ b, b ≠ r.id → (s.mem.writeQuad r (geDbl (readQuad ha))).live? b = s.mem.live? b :=
    fun b hne => live?_writeQuad_ne (Ne.symm hne)
  refine ⟨geDbl^[dblnCount n] (readQuad ha), ?_, ?_, u44_iterate hu _⟩
  case refine_2 => exact toPoint_iterate hu _
  have hone : (1#32 : BitVec 32).toInt = 1 := rfl
  have hcond := BitVec.toInt_eq_toNat_cond n
  by_cases hn1 : n.toInt ≤ 1
  · have hb : (1#32 <ₛ n) = false := by
      simp only [BitVec.slt, hone, decide_eq_false_iff_not, not_lt]; exact hn1
    rw [hb, BitVec.ofBool_false, if_neg (by decide)] at hrun
    have hcnt : dblnCount n = 1 := by simp [dblnCount, hn1]
    rw [hcnt, Function.iterate_one]
    exact ⟨s.popFrame u.mem, run_runFunction (hrun.trans (bb2_run env u)),
      popFrame_equiv hs hrlt hF hc rfl⟩
  · have h1 : 1 < n.toInt := by omega
    have h2 : 2 ≤ n.toNat := by split at hcond <;> omega
    have h256 : n.toNat < 256 := by split at hcond <;> omega
    have hb : (1#32 <ₛ n) = true := by
      simp only [BitVec.slt, hone, decide_eq_true_eq]; exact h1
    rw [hb, BitVec.ofBool_true, if_pos rfl] at hrun
    obtain ⟨u', hloop, hF'⟩ := loop_run env h2 h256 (u44_geDbl hu) hF
    obtain ⟨u'', hstore, hF''⟩ := bb1_run env (geDbl^[n.toNat - 1] (geDbl (readQuad ha))) hF'
      (isQuadPtr_writeQuad hr _) hrlt
    have hcnt : dblnCount n = n.toNat := by simp [dblnCount, hn1]
    have hit : geDbl^[n.toNat - 1] (geDbl (readQuad ha)) = geDbl^[dblnCount n] (readQuad ha) := by
      obtain ⟨k, hk⟩ : ∃ k, n.toNat = k + 1 := ⟨n.toNat - 1, by omega⟩
      rw [hcnt, hk, Function.iterate_succ_apply, Nat.add_sub_cancel]
    rw [hit] at hloop hstore hF''
    exact ⟨s.popFrame u''.mem, run_runFunction ((hrun.trans hloop).trans hstore),
      popFrame_equiv hs hrlt hF''
        (fun b hne => (live?_writeQuad_ne (Ne.symm hne)).trans (hc b hne))
        (live?_writeQuad_writeQuad _ _ hr.2)⟩

end Firedancer.Avx512
