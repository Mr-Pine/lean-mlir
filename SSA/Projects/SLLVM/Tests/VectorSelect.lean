import SSA.Projects.SLLVM.Dialect

/-! Both LLVM vector-select condition shapes, including unselected poison. -/
namespace LeanMLIR.SLLVM.Tests.VectorSelect
open LeanMLIR
open InstCombine (LLVM)

private abbrev V := SLLVM.Ty.arith (.vector 4 (.bitvec 64))
private abbrev Vec := Vector (LLVM.IntW 64) 4

def scalarCondition : Com SLLVM (Ctxt.ofList [V, V, SLLVM.Ty.bitvec 1]) .pure [V] :=
  [sllvm| {
    ^entry(%c: i1, %a: vector<4xi64>, %b: vector<4xi64>):
      %r = "llvm.select"(%c, %a, %b) : (i1, vector<4xi64>, vector<4xi64>) -> vector<4xi64>
      "llvm.return"(%r) : (vector<4xi64>) -> ()
  }]

private def run (c : LLVM.IntW 1) (a b : Vec) : Vec :=
  (scalarCondition.denote (Ctxt.Valuation.ofHVector [b, a, c]ₕ)).head

theorem scalarCondition_lane (c : LLVM.IntW 1) (a b : Vec) (i : Fin 4) :
    (run c a b)[i.val] = LLVM.select c a[i.val] b[i.val] := by
  change (SLLVM.vselectScalar c a b)[i.val] = _
  exact SLLVM.vselectScalar_lane c a b i

example : run (.value 1#1) #v[.value 7#64, .poison, .value 9#64, .value 10#64]
    #v[.poison, .value 8#64, .poison, .poison] =
    #v[.value 7#64, .poison, .value 9#64, .value 10#64] := by decide +kernel
example : run (.value 0#1) #v[.value 7#64, .poison, .value 9#64, .value 10#64]
    #v[.poison, .value 8#64, .poison, .poison] =
    #v[.poison, .value 8#64, .poison, .poison] := by decide +kernel
example : run .poison #v[.value 7#64, .value 8#64, .value 9#64, .value 10#64]
    #v[.value 7#64, .value 8#64, .value 9#64, .value 10#64] =
    #v[.poison, .poison, .poison, .poison] := by decide +kernel

def vectorCondition : Com SLLVM
    (Ctxt.ofList [V, V, SLLVM.Ty.arith (.vector 4 (.bitvec 1))]) .pure [V] :=
  [sllvm| {
    ^entry(%c: vector<4xi1>, %a: vector<4xi64>, %b: vector<4xi64>):
      %r = "llvm.select"(%c, %a, %b) : (vector<4xi1>, vector<4xi64>, vector<4xi64>) -> vector<4xi64>
      "llvm.return"(%r) : (vector<4xi64>) -> ()
  }]

example : (vectorCondition.denote (Ctxt.Valuation.ofHVector
    [#v[.poison, .value 8#64, .value 9#64, .value 10#64],
     #v[.value 7#64, .poison, .value 9#64, .poison],
     #v[.value 1#1, .value 0#1, .poison, .value 0#1]]ₕ)).head =
    #v[.value 7#64, .value 8#64, .poison, .value 10#64] := by
  rfl

end LeanMLIR.SLLVM.Tests.VectorSelect
