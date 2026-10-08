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

mlir_def addHalf :=
{
  ^bb0(%arg0: vector<2xi64>):
    %0 = "llvm.mlir.poison"() : () -> vector<2xi64>
    %1 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %3 = "llvm.insertelement"(%0, %1, %2) : (vector<2xi64>, i64, i64) -> vector<2xi64>
    %4 = "llvm.add"(%arg0, %3) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.return"(%4) : (vector<2xi64>) -> ()
}

-- an `add nsw` by a vector with a poison lane, to its lanes where its no-overflow fact is passed
attribute [-mlir_operation] zipWith_eq_ofFn in
example (x : Vector (BitVec 64) 2) (s : GlobalState) (hwf : s.WF)
    (hok : x[0].saddOverflow 1#64 = false) :
    addHalf.call (addHalf.args (Ty.wrap (t := .vec 2 64) x)) s =
      .value (.cons #v[.value (x[0] + 1#64), .poison] .nil, s) := by
  func_init
  block_init
  iterate 4 step_pure
  step_pure [expandZipWith, hok]
  guard_hyp hE : E = E₀[%4 := #v[.value (x[0] + 1#64), .poison]]
  finish_block
  rw [hS]

end

end LeanMLIR.RIR.Tests.Syntax.Vectors
