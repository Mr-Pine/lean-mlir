/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_add_with_opts.Blocks

/-!
# `fd_ed25519_point_add_with_opts`'s entry block

`^bb0`: the constants, the fifteen slots, and the branch on `b_is_precomputed`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

namespace PointAdd
open Ge

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **`^bb0`** with `b_is_precomputed = 1`: control reaches `^bb1` with the slots allocated. -/
theorem entry_run_ex (r a b : Pointer) (s : GlobalState) (hs : s.WF) :
    ∃ (W : fd_ed25519_point_add_with_opts.Γout.Valuation) (u : GlobalState),
      EntryEnv W s r a b ∧ Frame 15 s s.mem u
      ∧ StateT.run (fd_ed25519_point_add_with_opts.denote
          (Ctxt.Valuation.ofHVector [.value 1#32, .value b, .value a, .value r]ₕ)) s
        = StateT.run (fd_ed25519_point_add_with_opts.blocks.run W hdr1) u := by
  simp only [Cfg.denote]
  denote_step_reduce v 139 [LLVM.const?, LLVM.Ty.poison] fold

  -- `%0 … %139`: the masks and the folds' constants
  replace hv24 : v24 = pmaskE 8796093022189#64 8796093022207#64 := by
    simp only [hv24]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskE]
  replace hv41 : v41 = pmaskE 8796093022207#64 8796093022207#64 := by
    simp only [hv41]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskE]
  replace hv59 : v59 = pmaskE 8796093022207#64 1099511627775#64 := by
    simp only [hv59]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskE]
  replace hv60 : v60 = toBitVecValue 64 nbias03 := by
    simp only [nbias03]; denote_dense hv60
  replace hv61 : v61 = toBitVecValue 64 nbias := by
    simp only [nbias]; denote_dense hv61
  replace hv62 : v62 = toBitVecValue 64 quadShift43 := by
    simp only [quadShift43]; denote_dense hv62
  replace hv63 : v63 = toBitVecValue 64 quadShift48 := by
    simp only [quadShift48]; denote_dense hv63
  replace hv81 : v81 = quadMul19 := by
    simp only [hv81]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, quadMul19]
  replace hv82 : v82 = toBitVecValue 64 quadMask43 := by
    simp only [quadMask43]; denote_dense hv82
  replace hv83 : v83 = toBitVecValue 64 bias03 := by
    simp only [bias03]; denote_dense hv83
  replace hv84 : v84 = toBitVecValue 64 bias := by
    simp only [bias]; denote_dense hv84
  replace hv85 : v85 = toBitVecValue 64 quadMask48 := by
    simp only [quadMask48]; denote_dense hv85
  replace hv102 : v102 = pmaskEF 8796093022189#64 8796093022207#64 := by
    simp only [hv102]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskEF]
  replace hv119 : v119 = pmaskEF 8796093022207#64 8796093022207#64 := by
    simp only [hv119]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskEF]
  replace hv136 : v136 = pmaskEF 8796093022207#64 1099511627775#64 := by
    simp only [hv136]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskEF]
  subst hv0 hv1 hv2 hv24 hv41 hv59 hv60 hv61 hv62 hv63 hv81 hv82 hv83 hv84 hv85 hv102 hv119
    hv136
  denote_clear v 3 139
  refine name_of (s.allocaChain cw 15) fun sA hsA => ?_
  have hF0 : Frame 15 s s.mem sA := hsA ▸ frame_allocaChain hs 15
  peel_alloca_chain s, cw, 15
  simp only [slot_eq]
  rw [← hsA]
  denote_step_all v 155
  replace hv155 : v155 = .value 0#1 := by
    simp only [hv155, Expr.denoteOp1, Expr.denoteOpPure]; simp_peephole; rfl
  subst hv155
  simp only [BlockCom.denote_term, Terminator.denote_condBr, simp_spine]
  refine ⟨?W, sA, ?env, hF0, ?run⟩
  case run =>
    rw [if_neg (by decide)]
    rfl
  case env =>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `entry_run_ex`, in continuation form. -/
theorem entry_run (r a b : Pointer) (s : GlobalState) (hs : s.WF) {P : Prop}
    (k : ∀ (W : fd_ed25519_point_add_with_opts.Γout.Valuation) (u : GlobalState),
      EntryEnv W s r a b → Frame 15 s s.mem u →
      StateT.run (fd_ed25519_point_add_with_opts.denote
          (Ctxt.Valuation.ofHVector [.value 1#32, .value b, .value a, .value r]ₕ)) s
        = StateT.run (fd_ed25519_point_add_with_opts.blocks.run W hdr1) u → P) : P :=
  (entry_run_ex r a b s hs).elim fun W h => h.elim fun u h => k W u h.1 h.2.1 h.2.2

end PointAdd

end Firedancer.Avx512
