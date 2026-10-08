module

public import SSA.Projects.RIR.Syntax.Elab
public import SSA.Projects.RIR.Run.Tactic

/-! # Step tactic regressions on small functions -/

namespace LeanMLIR.RIR.Tests.Syntax.Steps

@[expose] public section

mlir_def twice :=
  {^bb0(%arg0:i32):%0 = "llvm.add"(%arg0, %arg0):(i32, i32)->i32"llvm.return"(%0):(i32)->()}

-- an argument read before the env is first sealed: by the args fact of the chain's root
example (E : ⟪twice.Γ⟫) (S : GlobalState) (x : BitVec 32)
    (hArgs : E.args = (twice.args (.value x)).get) :
    twice.runFrom (E[%0 := .value 0#32]) 0 S = .value (.cons (.value (x + x)) .nil, S) := by
  block_init
  step_pure
  finish_block
  rfl

mlir_def put :=
  {^bb0(%arg0:!llvm.ptr,
      %arg1:i64):"llvm.store"(%arg1, %arg0)<{alignment = 8:i64, ordering = 0:i64}>:(i64,
        !llvm.ptr)->()"llvm.return"():()->()}

-- a consumed fact is not carried: no goal for `hm`, which the store's state cannot carry
example (p : Pointer) (x : BitVec 64) (s : GlobalState) (m : MemoryState) (hwf : s.WF)
    (hp : Fits s.mem p 64) (hm : m = s.mem) :
    put.call (put.args (.value p) (.value x)) s =
      .value (.nil, { s with mem := s.mem.storeAt p x }) := by
  func_init
  block_init
  step_store consuming hm
  finish_block
  rw [hS]

mlir_def put2 :=
  {^bb0(%arg0:!llvm.ptr, %arg1:!llvm.ptr,
      %arg2:i64):"llvm.store"(%arg2, %arg0)<{alignment = 8:i64, ordering = 0:i64}>:(i64,
        !llvm.ptr)->()"llvm.store"(%arg2, %arg1)<{alignment = 8:i64, ordering = 0:i64}>:(i64,
        !llvm.ptr)->()"llvm.return"():()->()}

-- a read fact past a possibly aliasing store is dropped, and traced
/--
trace: [rir] read fact hread_p dropped (a write not known to miss it):
      (S.mem.storeAt q x).readAt p 64
-/
#guard_msgs in
set_option trace.rir true in
example (p q : Pointer) (x : BitVec 64) (s : GlobalState) (hwf : s.WF) (hp : Fits s.mem p 64)
    (hq : Fits s.mem q 64) :
    put2.call (put2.args (.value p) (.value q) (.value x)) s =
      .value (.nil, { s with mem := (s.mem.storeAt p x).storeAt q x }) := by
  func_init
  block_init
  step_store
  step_store
  finish_block
  rw [hS]

end

end LeanMLIR.RIR.Tests.Syntax.Steps
