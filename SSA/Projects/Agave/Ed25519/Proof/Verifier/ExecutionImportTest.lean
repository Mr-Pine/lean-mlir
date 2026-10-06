module

public import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionElab
public import SSA.Projects.RIR.Tests.Syntax.ProjectedBinders

namespace Agave.Ed25519.Verifier.Execution.ImportTest

open LeanMLIR.RIR
@[expose] public section

structure Callees where
  helper : Vals [.bv 64] → EffectM (Vals [.bv 64])

structure Globals where
  address : Pointer

/-- The raw-effect importer must retain projected primitive/global binders
without inserting a call wrapper, across all three dependent block types. -/
execution_def projected (p : Callees) (g : Globals) := {
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.addressof"() <{global_name = @"table.1"}> : () -> !llvm.ptr
    %1 = "llvm.call"(%arg0) <{callee = @"helper.0"}> : (i64) -> i64
    "llvm.br"(%0, %1)[^bb1] : (!llvm.ptr, i64) -> ()
  ^bb1(%2: !llvm.ptr, %3: i64):
    "llvm.br"(%3)[^bb2] : (i64) -> ()
  ^bb2(%4: i64):
    "llvm.return"(%4, %2) : (i64, !llvm.ptr) -> ()
} with @"helper.0" := p.helper
  globals @"table.1" := g.address

example (p : Callees) (g : Globals) :
    (projected p g).blocks ⟨0, by simp⟩ = projected.bb0 p g := rfl

example (p : Callees) (g : Globals) :
    (projected p g).blocks ⟨1, by simp⟩ = projected.bb1 := rfl

example (p : Callees) (g : Globals) :
    (projected p g).blocks ⟨2, by simp⟩ = projected.bb2 := rfl

example : projected.blockTys ⟨1, by decide⟩ = [.ptr, .bv 64] := rfl
example : projected.blockTys ⟨2, by decide⟩ = [.bv 64] := rfl

end
end Agave.Ed25519.Verifier.Execution.ImportTest
