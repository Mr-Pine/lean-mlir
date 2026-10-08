module

public import SSA.Projects.RIR.Syntax.Elab
public import SSA.Projects.RIR.Run.Tactic

/-! # Vector operations in steps -/

namespace LeanMLIR.RIR.Tests.Syntax.Vectors

@[expose] public section

mlir_def vand :=
{
  ^bb0(%arg0: vector<2xi64>, %arg1: vector<2xi64>):
    %0 = "llvm.and"(%arg0, %arg1) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.return"(%0) : (vector<2xi64>) -> ()
}

/-- Lane-wise `&&&`. -/
def andLanes (x y : Vector (BitVec 64) 2) : Vector (BitVec 64) 2 :=
  Vector.zipWith (· &&& ·) x y

theorem zipWith_and_wrap (x y : ⟦.vec 2 64⟧ᵣ) :
    Vector.zipWith (Operation.and (w := 64)) (Ty.wrap (t := .vec 2 64) x)
        (Ty.wrap (t := .vec 2 64) y) =
      Ty.wrap (t := .vec 2 64) (andLanes x y) := by
  ext i hi
  simp [Ty.wrap_vec, andLanes, Operation.and]

-- a lemma over a vector operation's `zipWith` of wrapped vectors fires (`simp` indexed its lanes'
-- type `⟦.bv 64⟧` unreduced)
attribute [-mlir_operation] zipWith_eq_ofFn in
example (x y : Vector (BitVec 64) 2) (s : GlobalState) (hwf : s.WF) :
    vand.call (vand.args (Ty.wrap (t := .vec 2 64) x) (Ty.wrap (t := .vec 2 64) y)) s =
      .value (.cons (Ty.wrap (t := .vec 2 64) (andLanes x y)) .nil, s) := by
  func_init
  block_init
  step_pure [zipWith_and_wrap] with z
  guard_hyp hz : z = andLanes x y
  finish_block
  rw [hS]

end

end LeanMLIR.RIR.Tests.Syntax.Vectors
