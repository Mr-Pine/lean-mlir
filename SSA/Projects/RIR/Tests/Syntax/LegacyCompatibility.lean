module

public import SSA.Projects.RIR.Syntax.Elab
public import SSA.Projects.SLLVM.Dialect.Syntax
import all SSA.Projects.RIR.Semantics.Func

/-! The RIR and legacy MLIR parsers can coexist, including their public elaborators.
Importing both used to fail while registering the global `mlir_*` categories. -/

namespace LeanMLIR.RIR.Tests.Syntax.LegacyCompatibility

@[expose] public section

-- Each framework's helpers must keep its own poison type and UB effect.
example (x : Nat) :
    (LeanMLIR.RIR.PoisonOr.getOrUB (.value x) : LeanMLIR.RIR.PoisonOr Nat) = .value x := rfl

example (x : Nat) :
    (_root_.PoisonOr.getOrUB (.value x) : _root_.PoisonOr Nat) = .value x := rfl

example : (LeanMLIR.RIR.Option.getOrUB (none : Option Nat) : Option Nat) = none := rfl
example : (_root_.Option.getOrUB (none : Option Nat) : Option Nat) = none := rfl

private def rirRegion : LeanMLIR.RIR.MLIR.Region := mlir_region% {
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    "llvm.return"(%arg0) : (i64) -> ()
}

private def legacyRegion : _root_.MLIR.AST.Region 0 := [mlir_region| {
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    "llvm.return"(%arg0) : (i64) -> ()
}]

example : rirRegion.blocks.length = 1 := rfl
example : legacyRegion.name = "bb0" := rfl
example : rirRegion.blocks.map (·.ops.length) = [legacyRegion.ops.length] := rfl

mlir_def rirIdentity := {
  ^bb0(%arg0: i64):
    "llvm.return"(%arg0) : (i64) -> ()
}

example : rirIdentity.tRets = [.bv 64] := rfl

open LeanMLIR.SLLVM in
private def sllvmIdentity := [sllvm| {
  ^bb0(%arg0: i64):
    "llvm.return"(%arg0) : (i64) -> ()
}]

end
end LeanMLIR.RIR.Tests.Syntax.LegacyCompatibility
