module

public import SSA.Projects.RIR.Syntax.Elab
import all SSA.Projects.RIR.Semantics.Func
meta import SSA.Projects.RIR.Syntax.Parser
meta import Lean.Elab.Command

/-! Exact metadata payloads, existing flag decoding, and quoted symbol bindings. -/

namespace LeanMLIR.RIR.Tests.Syntax.OpaqueMetadata

@[expose] public section

private def metadata : MLIR.Region := mlir_region% {
  "test.metadata"() <{
    memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>,
    range = #llvm.constant_range<i64, 0, -9223372036854775808>,
    arg_attrs = [{llvm.noundef, llvm.range = #llvm.constant_range<i64, 1, 72057594037927936>}],
    flags = #llvm.overflow<nsw, nuw>,
    no_flags = #llvm.overflow<none>,
    quoted_enum = #test.enum<"odd, > name">,
    nested = #test.metadata< {text = "a > ] }", nested = [(#inner<abc>)]} >,
    escaped = #test.metadata<text = "quote \" >", other = none>,
    global_name = @"anon.2688bd6af3b9e90d4f6e608faea972d6.1"
  }> : () -> ()
}

private def attr (name : String) : Option MLIR.AttrValue :=
  metadata.blocks.head?.bind fun b => b.ops.head?.bind (·.getAttr? name)

example : attr "memory_effects" = some (.opaque_ "llvm.memory_effects"
    "other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none") := rfl

example : attr "range" =
    some (.opaque_ "llvm.constant_range" "i64, 0, -9223372036854775808") := rfl

example : attr "arg_attrs" = some (.list [.dict (.mk [
    .mk "llvm.noundef" .unit,
    .mk "llvm.range" (.opaque_ "llvm.constant_range" "i64, 1, 72057594037927936")])]) := rfl

-- The semantic overflow parser still sees each flag individually, in source order.
example : attr "flags" = some (.list [
    .opaque_ "llvm.overflow" "nsw", .opaque_ "llvm.overflow" "nuw"]) := rfl

example : attr "no_flags" = some (.opaque_ "llvm.overflow" "none") := rfl
example : attr "quoted_enum" = some (.opaque_ "test.enum" "odd, > name") := rfl

example : attr "nested" = some (.opaque_ "test.metadata"
    " {text = \"a > ] }\", nested = [(#inner<abc>)]} ") := rfl

example : attr "escaped" = some (.opaque_ "test.metadata"
    "text = \"quote \\\" >\", other = none") := rfl

example : attr "global_name" =
    some (.symbol "anon.2688bd6af3b9e90d4f6e608faea972d6.1") := rfl

-- The raw payload parser rejects mismatched/unterminated brackets and strings.
run_elab do
  let env ← Lean.getEnv
  match Lean.Parser.runParserCategory env `mlir_attr_val
      "#test.metadata<text = \"quoted >\">" with
  | .ok _ => pure ()
  | .error e => throwError "rejected balanced dialect attribute: {e}"
  for input in ["#test.metadata<(]>", "#test.metadata<[x>",
      "#test.metadata<text = \"unterminated>"] do
    match Lean.Parser.runParserCategory env `mlir_attr_val input with
    | .error _ => pure ()
    | .ok _ => throwError "accepted malformed dialect attribute: {input}"

mlir_def quotedGlobal (table : Pointer) := {
  ^bb0:
    %0 = "llvm.mlir.addressof"() <{global_name = @"anon.2688bd6af3b9e90d4f6e608faea972d6.1"}> : () -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
} globals @"anon.2688bd6af3b9e90d4f6e608faea972d6.1" := table

example (table : Pointer) (s : GlobalState) :
    (quotedGlobal table).eval 1 .nil s =
      .value (some (.cons (.value table) .nil), s) := rfl

mlir_def identity := {
  ^bb0(%arg0: i64):
    "llvm.return"(%arg0) : (i64) -> ()
}

-- Both opaque metadata and quoted callee names survive ordinary instruction translation.
mlir_def quotedCall := {
  ^bb0(%arg0: i64):
    %0 = "llvm.call"(%arg0) <{
      callee = @"identity.1",
      memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>,
      arg_attrs = [{llvm.range = #llvm.constant_range<i64, 0, -9223372036854775808>}]
    }> : (i64) -> i64
    "llvm.return"(%0) : (i64) -> ()
} with @"identity.1" := identity

example : quotedCall.tRets = [.bv 64] := rfl

end
end LeanMLIR.RIR.Tests.Syntax.OpaqueMetadata
