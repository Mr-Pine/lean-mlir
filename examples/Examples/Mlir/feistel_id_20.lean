
module

public import MLIR.Semantics.Func
public import MLIR.Syntax.Elab

public import Examples.Mlir.decrypt_round
public import Examples.Mlir.encrypt_round

namespace Examples.Mlir

@[expose] public section

mlir_def feistel_id_20 := "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], dso_local, function_type = !llvm.func<i128 (i128, i64)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", ["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "feistel_id_20", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", unnamed_addr = 1 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64, will_return}> ({
^bb0(%arg0: i128, %arg1: i64):
  %0 = "llvm.mlir.constant"() <{value = 64 : i128}> : () -> i128
  %1 = "llvm.trunc"(%arg0) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %2 = "llvm.lshr"(%arg0, %0) : (i128, i128) -> i128
  %3 = "llvm.trunc"(%2) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %4 = "llvm.call"(%3, %1, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %5 = "llvm.call"(%4, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %6 = "llvm.trunc"(%5) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %7 = "llvm.lshr"(%5, %0) : (i128, i128) -> i128
  %8 = "llvm.trunc"(%7) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %9 = "llvm.call"(%8, %6, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %10 = "llvm.call"(%9, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %11 = "llvm.trunc"(%10) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %12 = "llvm.lshr"(%10, %0) : (i128, i128) -> i128
  %13 = "llvm.trunc"(%12) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %14 = "llvm.call"(%13, %11, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %15 = "llvm.call"(%14, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %16 = "llvm.trunc"(%15) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %17 = "llvm.lshr"(%15, %0) : (i128, i128) -> i128
  %18 = "llvm.trunc"(%17) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %19 = "llvm.call"(%18, %16, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %20 = "llvm.call"(%19, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %21 = "llvm.trunc"(%20) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %22 = "llvm.lshr"(%20, %0) : (i128, i128) -> i128
  %23 = "llvm.trunc"(%22) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %24 = "llvm.call"(%23, %21, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %25 = "llvm.call"(%24, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %26 = "llvm.trunc"(%25) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %27 = "llvm.lshr"(%25, %0) : (i128, i128) -> i128
  %28 = "llvm.trunc"(%27) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %29 = "llvm.call"(%28, %26, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %30 = "llvm.call"(%29, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %31 = "llvm.trunc"(%30) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %32 = "llvm.lshr"(%30, %0) : (i128, i128) -> i128
  %33 = "llvm.trunc"(%32) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %34 = "llvm.call"(%33, %31, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %35 = "llvm.call"(%34, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %36 = "llvm.trunc"(%35) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %37 = "llvm.lshr"(%35, %0) : (i128, i128) -> i128
  %38 = "llvm.trunc"(%37) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %39 = "llvm.call"(%38, %36, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %40 = "llvm.call"(%39, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %41 = "llvm.trunc"(%40) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %42 = "llvm.lshr"(%40, %0) : (i128, i128) -> i128
  %43 = "llvm.trunc"(%42) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %44 = "llvm.call"(%43, %41, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %45 = "llvm.call"(%44, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %46 = "llvm.trunc"(%45) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %47 = "llvm.lshr"(%45, %0) : (i128, i128) -> i128
  %48 = "llvm.trunc"(%47) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %49 = "llvm.call"(%48, %46, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %50 = "llvm.call"(%49, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %51 = "llvm.trunc"(%50) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %52 = "llvm.lshr"(%50, %0) : (i128, i128) -> i128
  %53 = "llvm.trunc"(%52) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %54 = "llvm.call"(%53, %51, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %55 = "llvm.call"(%54, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %56 = "llvm.trunc"(%55) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %57 = "llvm.lshr"(%55, %0) : (i128, i128) -> i128
  %58 = "llvm.trunc"(%57) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %59 = "llvm.call"(%58, %56, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %60 = "llvm.call"(%59, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %61 = "llvm.trunc"(%60) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %62 = "llvm.lshr"(%60, %0) : (i128, i128) -> i128
  %63 = "llvm.trunc"(%62) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %64 = "llvm.call"(%63, %61, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %65 = "llvm.call"(%64, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %66 = "llvm.trunc"(%65) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %67 = "llvm.lshr"(%65, %0) : (i128, i128) -> i128
  %68 = "llvm.trunc"(%67) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %69 = "llvm.call"(%68, %66, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %70 = "llvm.call"(%69, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %71 = "llvm.trunc"(%70) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %72 = "llvm.lshr"(%70, %0) : (i128, i128) -> i128
  %73 = "llvm.trunc"(%72) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %74 = "llvm.call"(%73, %71, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %75 = "llvm.call"(%74, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %76 = "llvm.trunc"(%75) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %77 = "llvm.lshr"(%75, %0) : (i128, i128) -> i128
  %78 = "llvm.trunc"(%77) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %79 = "llvm.call"(%78, %76, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %80 = "llvm.call"(%79, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %81 = "llvm.trunc"(%80) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %82 = "llvm.lshr"(%80, %0) : (i128, i128) -> i128
  %83 = "llvm.trunc"(%82) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %84 = "llvm.call"(%83, %81, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %85 = "llvm.call"(%84, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %86 = "llvm.trunc"(%85) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %87 = "llvm.lshr"(%85, %0) : (i128, i128) -> i128
  %88 = "llvm.trunc"(%87) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %89 = "llvm.call"(%88, %86, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %90 = "llvm.call"(%89, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %91 = "llvm.trunc"(%90) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %92 = "llvm.lshr"(%90, %0) : (i128, i128) -> i128
  %93 = "llvm.trunc"(%92) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %94 = "llvm.call"(%93, %91, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %95 = "llvm.call"(%94, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  %96 = "llvm.trunc"(%95) <{overflowFlags = 0 : i32}> : (i128) -> i64
  %97 = "llvm.lshr"(%95, %0) : (i128, i128) -> i128
  %98 = "llvm.trunc"(%97) <{overflowFlags = 2 : i32}> : (i128) -> i64
  %99 = "llvm.call"(%98, %96, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @encrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, i64) -> i128
  %100 = "llvm.call"(%99, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}], callee = @decrypt_round, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i128, i64) -> i128
  "llvm.return"(%100) : (i128) -> ()
}) : () -> ()
    with
      @decrypt_round := Examples.Mlir.decrypt_round,
      @encrypt_round := Examples.Mlir.encrypt_round

end

end Examples.Mlir
