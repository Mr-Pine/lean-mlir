
module

public import MLIR.Semantics.Func
public import MLIR.Syntax.Elab



namespace Examples.Mlir

@[expose] public section

mlir_def decrypt_round := "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], dso_local, function_type = !llvm.func<i128 (i128, i64)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", ["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "decrypt_round", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", unnamed_addr = 1 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
^bb0(%arg0: i128, %arg1: i64):
  %0 = "llvm.mlir.constant"() <{value = 64 : i128}> : () -> i128
  %1 = "llvm.mlir.constant"() <{value = -1162300618236559378 : i64}> : () -> i64
  %2 = "llvm.lshr"(%arg0, %0) : (i128, i128) -> i128
  %3 = "llvm.zext"(%arg1) : (i64) -> i128
  %4 = "llvm.mul"(%2, %3) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
  %5 = "llvm.xor"(%4, %arg0) : (i128, i128) -> i128
  %6 = "llvm.trunc"(%5) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %7 = "llvm.xor"(%6, %1) : (i64, i64) -> i64
  %8 = "llvm.zext"(%7) : (i64) -> i128
  %9 = "llvm.shl"(%8, %0) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
  %10 = "llvm.or"(%9, %2) <{isDisjoint}> : (i128, i128) -> i128
  "llvm.return"(%10) : (i128) -> ()
}) : () -> ()
end

end Examples.Mlir
