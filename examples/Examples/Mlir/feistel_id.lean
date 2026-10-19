
module

public import MLIR.Semantics.Func
public import MLIR.Syntax.Elab

public import Examples.Mlir.encrypt_round
public import Examples.Mlir.decrypt_round

namespace Examples.Mlir

@[expose] public section

mlir_def feistel_id := "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], dso_local, function_type = !llvm.func<i128 (i128, i64)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", ["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "feistel_id", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", unnamed_addr = 1 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
^bb0(%arg0: i128, %arg1: i64):
  %0 = "llvm.mlir.constant"() <{value = 64 : i128}> : () -> i128
  %1 = "llvm.lshr"(%arg0, %0) : (i128, i128) -> i128
  %2 = "llvm.trunc"(%1) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %3 = "llvm.trunc"(%arg0) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %4 = "llvm.call"(%2, %3, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %5 = "llvm.call"(%4, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  "llvm.return"(%5) : (i128) -> ()
}) : () -> ()
    with
      @encrypt_round := Examples.Mlir.encrypt_round,
      @decrypt_round := Examples.Mlir.decrypt_round

end

end Examples.Mlir
