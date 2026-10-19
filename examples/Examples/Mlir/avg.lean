
module

public import MLIR.Semantics.Func
public import MLIR.Syntax.Elab



namespace Examples.Mlir

@[expose] public section

mlir_def avg := "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], dso_local, function_type = !llvm.func<i64 (i64, i64)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", ["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], res_attrs = [{llvm.noundef}], sym_name = "avg", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", unnamed_addr = 1 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
^bb0(%arg0: i64, %arg1: i64):
  %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
  %1 = "llvm.and"(%arg1, %arg0) : (i64, i64) -> i64
  %2 = "llvm.xor"(%arg1, %arg0) : (i64, i64) -> i64
  %3 = "llvm.lshr"(%2, %0) : (i64, i64) -> i64
  %4 = "llvm.add"(%3, %1) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
  "llvm.return"(%4) : (i64) -> ()
}) : () -> ()
end

end Examples.Mlir
