import SSA.Projects.RIR.Syntax.Elab
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

namespace Agave.Ed25519.Reduce64.Execution.StepRegression
open LeanMLIR.RIR

/- A second argument-based GEP after a load catches accidental expansion of the
whole environment during the first GEP: that drops its argument equality. -/
mlir_def twoLoads := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
    %1 = "llvm.load"(%0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %2 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
    %3 = "llvm.load"(%2) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %4 = "llvm.add"(%1, %3) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.return"(%4) : (i64) -> ()
}

theorem twoLoads_call (p : Pointer) (s : GlobalState) (hwf : s.WF)
    (hp : SmallRange s.mem p 24) :
    twoLoads.call (twoLoads.args (.value p)) s =
      .value (.cons (.value (s.mem.readAt (p.add 8) 64 + s.mem.readAt (p.add 16) 64)) .nil, s) := by
  have h8 := hp.fits_add (k := 8) (count := 8) (by decide)
  have h16 := hp.fits_add (k := 16) (count := 8) (by decide)
  func_init
  block_init
  have hg8 := hp.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hg8
  try simp only [hS] at hg8
  step_reduce_gep [hg8, GepIndex.inboundsOffset]
  clear hg8
  step_load
  have hg16 := hp.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hg16
  try simp only [hS] at hg16
  step_reduce_gep [hg16, GepIndex.inboundsOffset]
  clear hg16
  step_load
  step_pure
  finish_block
  rw [hS]
  subst_vars
  rfl

end Agave.Ed25519.Reduce64.Execution.StepRegression
