/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_add_with_opts.Blocks

/-!
# `fd_ed25519_point_add_with_opts`'s entry block

`^bb0`: the constants, the fifteen slots, and the branch on `b_is_precomputed`.
-/

@[expose] public section

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
  denote_step_reduce v 87 [LLVM.const?, LLVM.Ty.poison] fold

  -- `%0 … %87`: the masks and the folds' constants
  replace hv33 : v33 = pmaskE 8796093022189#64 8796093022207#64 := by
    simp only [hv33]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskE]
  replace hv42 : v42 = pmaskE 8796093022207#64 8796093022207#64 := by
    simp only [hv42]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskE]
  replace hv51 : v51 = pmaskE 8796093022207#64 1099511627775#64 := by
    simp only [hv51]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskE]
  replace hv11 : v11 = toBitVecValue 64 nbias03 := by
    simp only [nbias03]; denote_dense hv11
  replace hv10 : v10 = toBitVecValue 64 nbias := by
    simp only [nbias]; denote_dense hv10
  replace hv9 : v9 = toBitVecValue 64 quadShift43 := by
    simp only [quadShift43]; denote_dense hv9
  replace hv8 : v8 = toBitVecValue 64 quadShift48 := by
    simp only [quadShift48]; denote_dense hv8
  replace hv60 : v60 = quadMul19 := by
    simp only [hv60]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, quadMul19]
  replace hv6 : v6 = toBitVecValue 64 quadMask43 := by
    simp only [quadMask43]; denote_dense hv6
  replace hv5 : v5 = toBitVecValue 64 bias03 := by
    simp only [bias03]; denote_dense hv5
  replace hv4 : v4 = toBitVecValue 64 bias := by
    simp only [bias]; denote_dense hv4
  replace hv3 : v3 = toBitVecValue 64 quadMask48 := by
    simp only [quadMask48]; denote_dense hv3
  replace hv69 : v69 = pmaskEF 8796093022189#64 8796093022207#64 := by
    simp only [hv69]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskEF]
  replace hv78 : v78 = pmaskEF 8796093022207#64 8796093022207#64 := by
    simp only [hv78]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskEF]
  replace hv87 : v87 = pmaskEF 8796093022207#64 1099511627775#64 := by
    simp only [hv87]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskEF]
  subst hv20 hv21 hv33 hv42 hv51 hv11 hv10 hv9 hv8 hv60 hv6 hv5 hv4 hv3 hv69 hv78 hv87
  denote_clear v 0 87
  refine name_of (s.allocaChain cw 15) fun sA hsA => ?_
  have hF0 : Frame 15 s s.mem sA := hsA ▸ frame_allocaChain hs 15
  peel_alloca_chain s, cw, 15
  simp only [slot_eq]
  rw [← hsA]
  denote_step_all v 103
  replace hv103 : v103 = .value 0#1 := by
    simp only [hv103, Expr.denoteOp1, Expr.denoteOpPure]; simp_denote_only; rfl
  subst hv103
  simp only [BlockCom.denote_term, Terminator.denote_condBr, simp_spine]
  refine ⟨?W, sA, ?env, hF0, ?run⟩
  case run =>
    rw [if_neg (by decide)]
    rfl
  case env =>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl⟩

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
