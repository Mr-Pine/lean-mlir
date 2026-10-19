
module

public import MLIR.Semantics.Func
public import MLIR.Syntax.Elab



namespace Examples.Mlir

@[expose] public section

mlir_def collatz_step := "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef}], dso_local, function_type = !llvm.func<i32 (i32)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", ["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "collatz_step", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", unnamed_addr = 1 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
^bb0(%arg0: i32):
  %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
  %1 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
  %2 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
  %3 = "llvm.and"(%arg0, %0) : (i32, i32) -> i32
  %4 = "llvm.icmp"(%3, %1) <{predicate = 0 : i64}> : (i32, i32) -> i1
  "llvm.cond_br"(%4)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^bb1:  // pred: ^bb0
  %5 = "llvm.ashr"(%arg0, %0) <{isExact}> : (i32, i32) -> i32
  "llvm.br"(%5)[^bb3] : (i32) -> ()
^bb2:  // pred: ^bb0
  %6 = "llvm.mul"(%arg0, %2) <{overflowFlags = 0 : i32}> : (i32, i32) -> i32
  %7 = "llvm.add"(%6, %0) <{overflowFlags = 0 : i32}> : (i32, i32) -> i32
  "llvm.br"(%7)[^bb3] : (i32) -> ()
^bb3(%8: i32):  // 2 preds: ^bb1, ^bb2
  "llvm.return"(%8) : (i32) -> ()
}) : () -> ()
end

end Examples.Mlir
