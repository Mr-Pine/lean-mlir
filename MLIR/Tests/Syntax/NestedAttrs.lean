module

public import MLIR.Syntax.Elab

/-! # Nested attributes: `>>` closing two `<…>`, inline alias scopes with `distinct` ids -/

namespace MLIR.Tests.Syntax.NestedAttrs

@[expose] public section

/-- A loop annotation's `<disable = true>>`. -/
mlir_def count := {
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    "llvm.br"(%arg0)[^bb1] : (i64) -> ()
  ^bb1(%1: i64):
    %2 = "llvm.sub"(%1, %0) : (i64, i64) -> i64
    %3 = "llvm.icmp"(%2, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%3, %2)[^bb2, ^bb1] <{loop_annotation = #llvm.loop_annotation<unroll = <disable = true>>, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
  ^bb2:
    "llvm.return"(%2) : (i64) -> ()
}

/-- A `memcpy`'s alias scopes, their domain inline. -/
mlir_def copy := {
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i64):
    "llvm.intr.memcpy"(%arg0, %arg1, %arg2) <{alias_scopes = [#llvm.alias_scope<id = distinct[0]<>, domain = <id = distinct[1]<>, description = "copy">, description = "copy: argument 0">], arg_attrs = [{llvm.align = 1 : i64, llvm.nonnull}, {llvm.align = 1 : i64, llvm.readonly}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
}

example : copy.entry.body = [.memcpy (.arg 0 rfl) (.arg 1 rfl) (.arg 2 rfl)] := rfl

end

end MLIR.Tests.Syntax.NestedAttrs
