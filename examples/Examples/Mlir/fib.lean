
module

public import MLIR.Semantics.Func
public import MLIR.Syntax.Elab



namespace Examples.Mlir

@[expose] public section

mlir_def fib := "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef}], dso_local, function_type = !llvm.func<i64 (i64)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["nofree", "norecurse", "nosync", ["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "fib", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", unnamed_addr = 1 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
^bb0(%arg0: i64):
  %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
  %1 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
  %2 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
  %3 = "llvm.icmp"(%arg0, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
  "llvm.cond_br"(%3, %0, %arg0, %1, %0)[^bb2, ^bb1] <{operandSegmentSizes = array<i32: 1, 1, 3>}> : (i1, i64, i64, i64, i64) -> ()
^bb1(%4: i64, %5: i64, %6: i64):  // 2 preds: ^bb0, ^bb1
  %7 = "llvm.add"(%4, %2) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
  %8 = "llvm.add"(%5, %6) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
  %9 = "llvm.icmp"(%7, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
  "llvm.cond_br"(%9, %5, %7, %8, %5)[^bb2, ^bb1] <{loop_annotation = #llvm.loop_annotation<unroll = <disable = true>, mustProgress = true>, operandSegmentSizes = array<i32: 1, 1, 3>}> : (i1, i64, i64, i64, i64) -> ()
^bb2(%10: i64):  // 2 preds: ^bb0, ^bb1
  "llvm.return"(%10) : (i64) -> ()
}) : () -> ()
end

end Examples.Mlir
