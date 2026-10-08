module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic

/-! # Step tactic regressions on small functions -/

namespace MLIR.Tests.Syntax.Steps

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

end

end MLIR.Tests.Syntax.Steps
