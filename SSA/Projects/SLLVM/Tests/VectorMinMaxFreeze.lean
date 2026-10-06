import SSA.Projects.SLLVM.Dialect

/-! Unsigned ordering, partial poison, and the vector-mask freeze/bitcast path
emitted by the pinned Agave compiler. All examples are kernel reductions. -/
namespace LeanMLIR.SLLVM.Tests.VectorMinMaxFreeze
open LeanMLIR
open InstCombine (LLVM)

example : SLLVM.umin (.value 255#8) (.value 3#8) = .value 3#8 := rfl
example : SLLVM.umax (.value 255#8) (.value 3#8) = .value 255#8 := rfl
example : SLLVM.umin (.value 3#8) .poison = .poison := rfl
example : SLLVM.umax (.poison : LLVM.IntW 8) (.value 3#8) = .poison := rfl

example : SLLVM.vumin #v[.value 255#8, .poison, .value 9#8]
    #v[.value 3#8, .value 4#8, .value 10#8] =
    #v[.value 3#8, .poison, .value 9#8] := rfl
example : SLLVM.vumax #v[.value 255#8, .value 4#8, .value 9#8]
    #v[.value 3#8, .poison, .value 10#8] =
    #v[.value 255#8, .poison, .value 10#8] := rfl

/-- Mixed poison lanes freeze independently, without altering defined ones. -/
example : SLLVM.vfreeze #v[.value 1#1, .poison, .value 0#1] =
    #v[.value 1#1, .value 0#1, .value 0#1] := by decide +kernel

def maskByte : Com SLLVM (Ctxt.ofList [SLLVM.Ty.arith (.vector 8 (.bitvec 1))])
    .pure [SLLVM.Ty.bitvec 8] := [sllvm| {
  ^entry(%x: vector<8xi1>):
    %f = "llvm.freeze"(%x) : (vector<8xi1>) -> vector<8xi1>
    %b = "llvm.bitcast"(%f) : (vector<8xi1>) -> i8
    "llvm.return"(%b) : (i8) -> ()
}]

/-- Least-significant-bit lane order and the chosen zero for poison. -/
example : (maskByte.denote (Ctxt.Valuation.singleton
    #v[.value 1#1, .poison, .value 1#1, .value 0#1,
       .value 0#1, .value 1#1, .poison, .value 1#1])).head = .value 165#8 := by
  change @Eq (PoisonOr (BitVec 8)) _ _
  decide +kernel

def minVec : Com SLLVM
    (Ctxt.ofList [SLLVM.Ty.arith (.vector 2 (.bitvec 8)), SLLVM.Ty.arith (.vector 2 (.bitvec 8))])
    .pure [SLLVM.Ty.arith (.vector 2 (.bitvec 8))] := [sllvm| {
  ^entry(%a: vector<2xi8>, %b: vector<2xi8>):
    %m = "llvm.intr.umin"(%a, %b) : (vector<2xi8>, vector<2xi8>) -> vector<2xi8>
    "llvm.return"(%m) : (vector<2xi8>) -> ()
}]

example : (minVec.denote (Ctxt.Valuation.ofHVector
    [#v[.value 3#8, .value 4#8], #v[.value 255#8, .poison]]ₕ)).head =
    #v[.value 3#8, .poison] := rfl

def maxVec : Com SLLVM
    (Ctxt.ofList [SLLVM.Ty.arith (.vector 2 (.bitvec 8)), SLLVM.Ty.arith (.vector 2 (.bitvec 8))])
    .pure [SLLVM.Ty.arith (.vector 2 (.bitvec 8))] := [sllvm| {
  ^entry(%a: vector<2xi8>, %b: vector<2xi8>):
    %m = "llvm.intr.umax"(%a, %b) : (vector<2xi8>, vector<2xi8>) -> vector<2xi8>
    "llvm.return"(%m) : (vector<2xi8>) -> ()
}]

example : (maxVec.denote (Ctxt.Valuation.ofHVector
    [#v[.value 3#8, .value 4#8], #v[.value 255#8, .poison]]ₕ)).head =
    #v[.value 255#8, .poison] := rfl

def scopeOnly : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [] := [sllvm| {
  ^entry():
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope11}> : () -> ()
    "llvm.return"() : () -> ()
}]

example : scopeOnly.denote Ctxt.Valuation.nil = HVector.nil := rfl

/-- The parsed operation retains its required scope metadata when printed. -/
example : (match scopeOnly with
    | .var e _ => DialectPrint.printAttributes (d := SLLVM) e.op
    | .rets _ => "") = "<{scope = #alias_scope11}>" := rfl

/--
info: builtin.module {
  ^entry():
    "llvm.intr.experimental.noalias.scope.decl"()<{scope = #alias_scope11}> : () -> ()
    "llvm.return"() : () -> ()
}
-/
#guard_msgs in
#eval Com.printModule scopeOnly

/-- error: Missing attribute `scope` -/
#guard_msgs in
def missingScope : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [] := [sllvm| {
  ^entry():
    "llvm.intr.experimental.noalias.scope.decl"() : () -> ()
    "llvm.return"() : () -> ()
}]

/-- error: llvm.intr.experimental.noalias.scope.decl: expected a scope alias -/
#guard_msgs in
def wrongScope : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [] := [sllvm| {
  ^entry():
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = 11 : i32}> : () -> ()
    "llvm.return"() : () -> ()
}]

end LeanMLIR.SLLVM.Tests.VectorMinMaxFreeze
