module

public import SSA.Projects.RIR.Syntax.Elab
public import SSA.Projects.RIR.Run.Tactic
public import SSA.Projects.RIR.Run.Vector

/-! Exact function bodies from the pinned compiler artifacts in ../../MLIR/generated.
No arithmetic or flags are rewritten. The pointer-based from_bytes observations
1–3 and full point compression are not modeled by these pure observations. -/

namespace Agave.Ed25519.Encoding.RIR
open LeanMLIR.RIR
@[expose] public section

mlir_def agave_serial_field_from_bytes_observe_0 :=
{
  ^bb0(%arg0: i64, %arg1: i64, %arg2: i64, %arg3: i64):
    %0 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %1 = "llvm.and"(%arg0, %0) : (i64, i64) -> i64
    "llvm.return"(%1) : (i64) -> ()
}

mlir_def agave_serial_field_from_bytes_observe_4 :=
{
  ^bb0(%arg0: i64, %arg1: i64, %arg2: i64, %arg3: i64):
    %0 = "llvm.mlir.constant"() <{value = 12 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %2 = "llvm.lshr"(%arg3, %0) : (i64, i64) -> i64
    %3 = "llvm.and"(%2, %1) : (i64, i64) -> i64
    "llvm.return"(%3) : (i64) -> ()
}

mlir_def agave_serial_field_to_bytes_observe_0 :=
{
  ^bb0(%arg0: i64, %arg1: i64, %arg2: i64, %arg3: i64, %arg4: i64):
    %0 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %3 = "llvm.lshr"(%arg0, %0) : (i64, i64) -> i64
    %4 = "llvm.lshr"(%arg1, %0) : (i64, i64) -> i64
    %5 = "llvm.lshr"(%arg2, %0) : (i64, i64) -> i64
    %6 = "llvm.lshr"(%arg3, %0) : (i64, i64) -> i64
    %7 = "llvm.lshr"(%arg4, %0) : (i64, i64) -> i64
    %8 = "llvm.and"(%arg0, %1) : (i64, i64) -> i64
    %9 = "llvm.and"(%arg1, %1) : (i64, i64) -> i64
    %10 = "llvm.and"(%arg2, %1) : (i64, i64) -> i64
    %11 = "llvm.and"(%arg3, %1) : (i64, i64) -> i64
    %12 = "llvm.and"(%arg4, %1) : (i64, i64) -> i64
    %13 = "llvm.mul"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %14 = "llvm.add"(%13, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %15 = "llvm.add"(%9, %3) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %16 = "llvm.add"(%10, %4) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %17 = "llvm.add"(%11, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %18 = "llvm.add"(%12, %6) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %19 = "llvm.add"(%14, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %20 = "llvm.lshr"(%19, %0) : (i64, i64) -> i64
    %21 = "llvm.add"(%20, %15) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %22 = "llvm.lshr"(%21, %0) : (i64, i64) -> i64
    %23 = "llvm.add"(%16, %22) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %24 = "llvm.lshr"(%23, %0) : (i64, i64) -> i64
    %25 = "llvm.add"(%17, %24) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %26 = "llvm.lshr"(%25, %0) : (i64, i64) -> i64
    %27 = "llvm.add"(%18, %26) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %28 = "llvm.lshr"(%27, %0) : (i64, i64) -> i64
    %29 = "llvm.mul"(%28, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %30 = "llvm.add"(%29, %14) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %31 = "llvm.shl"(%15, %0) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %32 = "llvm.add"(%30, %31) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    "llvm.return"(%32) : (i64) -> ()
}

mlir_def agave_serial_field_to_bytes_observe_1 :=
{
  ^bb0(%arg0: i64, %arg1: i64, %arg2: i64, %arg3: i64, %arg4: i64):
    %0 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 13 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 45 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 63 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 38 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 192 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 255 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 4294967040 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = -1099511627776 : i64}> : () -> i64
    %13 = "llvm.lshr"(%arg0, %0) : (i64, i64) -> i64
    %14 = "llvm.lshr"(%arg1, %0) : (i64, i64) -> i64
    %15 = "llvm.lshr"(%arg2, %0) : (i64, i64) -> i64
    %16 = "llvm.lshr"(%arg3, %0) : (i64, i64) -> i64
    %17 = "llvm.lshr"(%arg4, %0) : (i64, i64) -> i64
    %18 = "llvm.and"(%arg0, %1) : (i64, i64) -> i64
    %19 = "llvm.and"(%arg1, %1) : (i64, i64) -> i64
    %20 = "llvm.and"(%arg2, %1) : (i64, i64) -> i64
    %21 = "llvm.and"(%arg3, %1) : (i64, i64) -> i64
    %22 = "llvm.and"(%arg4, %1) : (i64, i64) -> i64
    %23 = "llvm.mul"(%17, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %24 = "llvm.add"(%23, %18) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %25 = "llvm.add"(%19, %13) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %26 = "llvm.add"(%20, %14) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %27 = "llvm.add"(%21, %15) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %28 = "llvm.add"(%22, %16) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %29 = "llvm.add"(%24, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %30 = "llvm.lshr"(%29, %0) : (i64, i64) -> i64
    %31 = "llvm.add"(%30, %25) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %32 = "llvm.lshr"(%31, %0) : (i64, i64) -> i64
    %33 = "llvm.add"(%32, %26) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %34 = "llvm.lshr"(%33, %0) : (i64, i64) -> i64
    %35 = "llvm.add"(%27, %34) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %36 = "llvm.lshr"(%35, %0) : (i64, i64) -> i64
    %37 = "llvm.add"(%28, %36) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %38 = "llvm.lshr"(%37, %0) : (i64, i64) -> i64
    %39 = "llvm.mul"(%38, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %40 = "llvm.add"(%39, %24) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %41 = "llvm.lshr"(%40, %0) : (i64, i64) -> i64
    %42 = "llvm.add"(%41, %25) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %43 = "llvm.lshr"(%42, %0) : (i64, i64) -> i64
    %44 = "llvm.add"(%43, %26) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %45 = "llvm.lshr"(%42, %3) : (i64, i64) -> i64
    %46 = "llvm.lshr"(%42, %4) : (i64, i64) -> i64
    %47 = "llvm.and"(%46, %5) : (i64, i64) -> i64
    %48 = "llvm.shl"(%44, %6) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %49 = "llvm.shl"(%44, %7) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %50 = "llvm.and"(%48, %8) : (i64, i64) -> i64
    %51 = "llvm.or"(%50, %47) <{isDisjoint}> : (i64, i64) -> i64
    %52 = "llvm.shl"(%51, %9) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %53 = "llvm.and"(%45, %10) : (i64, i64) -> i64
    %54 = "llvm.and"(%45, %11) : (i64, i64) -> i64
    %55 = "llvm.and"(%49, %12) : (i64, i64) -> i64
    %56 = "llvm.or"(%54, %55) <{isDisjoint}> : (i64, i64) -> i64
    %57 = "llvm.or"(%56, %52) <{isDisjoint}> : (i64, i64) -> i64
    %58 = "llvm.or"(%57, %53) <{isDisjoint}> : (i64, i64) -> i64
    "llvm.return"(%58) : (i64) -> ()
}

mlir_def agave_serial_field_to_bytes_observe_2 :=
{
  ^bb0(%arg0: i64, %arg1: i64, %arg2: i64, %arg3: i64, %arg4: i64):
    %0 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 50 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 25 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 254 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 255 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 16776960 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = -4294967296 : i64}> : () -> i64
    %12 = "llvm.lshr"(%arg0, %0) : (i64, i64) -> i64
    %13 = "llvm.lshr"(%arg1, %0) : (i64, i64) -> i64
    %14 = "llvm.lshr"(%arg2, %0) : (i64, i64) -> i64
    %15 = "llvm.lshr"(%arg3, %0) : (i64, i64) -> i64
    %16 = "llvm.lshr"(%arg4, %0) : (i64, i64) -> i64
    %17 = "llvm.and"(%arg0, %1) : (i64, i64) -> i64
    %18 = "llvm.and"(%arg1, %1) : (i64, i64) -> i64
    %19 = "llvm.and"(%arg2, %1) : (i64, i64) -> i64
    %20 = "llvm.and"(%arg3, %1) : (i64, i64) -> i64
    %21 = "llvm.and"(%arg4, %1) : (i64, i64) -> i64
    %22 = "llvm.mul"(%16, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %23 = "llvm.add"(%22, %17) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %24 = "llvm.add"(%18, %12) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %25 = "llvm.add"(%19, %13) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %26 = "llvm.add"(%20, %14) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %27 = "llvm.add"(%21, %15) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %28 = "llvm.add"(%23, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %29 = "llvm.lshr"(%28, %0) : (i64, i64) -> i64
    %30 = "llvm.add"(%29, %24) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %31 = "llvm.lshr"(%30, %0) : (i64, i64) -> i64
    %32 = "llvm.add"(%31, %25) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %33 = "llvm.lshr"(%32, %0) : (i64, i64) -> i64
    %34 = "llvm.add"(%33, %26) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %35 = "llvm.lshr"(%34, %0) : (i64, i64) -> i64
    %36 = "llvm.add"(%27, %35) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %37 = "llvm.lshr"(%36, %0) : (i64, i64) -> i64
    %38 = "llvm.mul"(%37, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %39 = "llvm.add"(%38, %23) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %40 = "llvm.lshr"(%39, %0) : (i64, i64) -> i64
    %41 = "llvm.add"(%40, %24) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %42 = "llvm.lshr"(%41, %0) : (i64, i64) -> i64
    %43 = "llvm.add"(%42, %25) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %44 = "llvm.lshr"(%43, %0) : (i64, i64) -> i64
    %45 = "llvm.add"(%44, %26) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %46 = "llvm.lshr"(%43, %3) : (i64, i64) -> i64
    %47 = "llvm.lshr"(%43, %4) : (i64, i64) -> i64
    %48 = "llvm.and"(%47, %5) : (i64, i64) -> i64
    %49 = "llvm.shl"(%45, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %50 = "llvm.shl"(%45, %6) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %51 = "llvm.and"(%49, %7) : (i64, i64) -> i64
    %52 = "llvm.or"(%51, %48) <{isDisjoint}> : (i64, i64) -> i64
    %53 = "llvm.shl"(%52, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %54 = "llvm.and"(%46, %9) : (i64, i64) -> i64
    %55 = "llvm.and"(%46, %10) : (i64, i64) -> i64
    %56 = "llvm.and"(%50, %11) : (i64, i64) -> i64
    %57 = "llvm.or"(%55, %56) <{isDisjoint}> : (i64, i64) -> i64
    %58 = "llvm.or"(%57, %53) <{isDisjoint}> : (i64, i64) -> i64
    %59 = "llvm.or"(%58, %54) <{isDisjoint}> : (i64, i64) -> i64
    "llvm.return"(%59) : (i64) -> ()
}

mlir_def agave_serial_field_to_bytes_observe_3 :=
{
  ^bb0(%arg0: i64, %arg1: i64, %arg2: i64, %arg3: i64, %arg4: i64):
    %0 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 39 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 47 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 12 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 240 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 255 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 9223372036854710272 : i64}> : () -> i64
    %12 = "llvm.lshr"(%arg0, %0) : (i64, i64) -> i64
    %13 = "llvm.lshr"(%arg1, %0) : (i64, i64) -> i64
    %14 = "llvm.lshr"(%arg2, %0) : (i64, i64) -> i64
    %15 = "llvm.lshr"(%arg3, %0) : (i64, i64) -> i64
    %16 = "llvm.lshr"(%arg4, %0) : (i64, i64) -> i64
    %17 = "llvm.and"(%arg0, %1) : (i64, i64) -> i64
    %18 = "llvm.and"(%arg1, %1) : (i64, i64) -> i64
    %19 = "llvm.and"(%arg2, %1) : (i64, i64) -> i64
    %20 = "llvm.and"(%arg3, %1) : (i64, i64) -> i64
    %21 = "llvm.and"(%arg4, %1) : (i64, i64) -> i64
    %22 = "llvm.mul"(%16, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %23 = "llvm.add"(%22, %17) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %24 = "llvm.add"(%18, %12) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %25 = "llvm.add"(%19, %13) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %26 = "llvm.add"(%20, %14) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %27 = "llvm.add"(%21, %15) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %28 = "llvm.add"(%23, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %29 = "llvm.lshr"(%28, %0) : (i64, i64) -> i64
    %30 = "llvm.add"(%29, %24) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %31 = "llvm.lshr"(%30, %0) : (i64, i64) -> i64
    %32 = "llvm.add"(%31, %25) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %33 = "llvm.lshr"(%32, %0) : (i64, i64) -> i64
    %34 = "llvm.add"(%33, %26) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %35 = "llvm.lshr"(%34, %0) : (i64, i64) -> i64
    %36 = "llvm.add"(%35, %27) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %37 = "llvm.lshr"(%36, %0) : (i64, i64) -> i64
    %38 = "llvm.mul"(%37, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %39 = "llvm.add"(%38, %23) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %40 = "llvm.lshr"(%39, %0) : (i64, i64) -> i64
    %41 = "llvm.add"(%40, %24) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %42 = "llvm.lshr"(%41, %0) : (i64, i64) -> i64
    %43 = "llvm.add"(%42, %25) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %44 = "llvm.lshr"(%43, %0) : (i64, i64) -> i64
    %45 = "llvm.add"(%44, %26) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %46 = "llvm.lshr"(%45, %0) : (i64, i64) -> i64
    %47 = "llvm.add"(%46, %27) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %48 = "llvm.lshr"(%45, %3) : (i64, i64) -> i64
    %49 = "llvm.lshr"(%45, %4) : (i64, i64) -> i64
    %50 = "llvm.and"(%49, %5) : (i64, i64) -> i64
    %51 = "llvm.shl"(%47, %6) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %52 = "llvm.shl"(%47, %7) <{overflowFlags = 2 : i32}> : (i64, i64) -> i64
    %53 = "llvm.and"(%51, %8) : (i64, i64) -> i64
    %54 = "llvm.or"(%53, %50) <{isDisjoint}> : (i64, i64) -> i64
    %55 = "llvm.shl"(%54, %9) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %56 = "llvm.and"(%48, %10) : (i64, i64) -> i64
    %57 = "llvm.and"(%52, %11) : (i64, i64) -> i64
    %58 = "llvm.or"(%57, %55) <{isDisjoint}> : (i64, i64) -> i64
    %59 = "llvm.or"(%58, %56) <{isDisjoint}> : (i64, i64) -> i64
    "llvm.return"(%59) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_0 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_1 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg1) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_2 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg2) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_3 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg3) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_4 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_5 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_6 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg1) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_7 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg2) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_8 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg3) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_9 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_10 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_11 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg1) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_12 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg2) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_13 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg3) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_14 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_15 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg0) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_16 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg1) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_17 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg2) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_18 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg3) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

mlir_def agave_avx2_field_split_observe_19 :=
{
  ^bb0(%arg0: vector<4xi64>, %arg1: vector<4xi64>, %arg2: vector<4xi64>, %arg3: vector<4xi64>, %arg4: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %3 = "llvm.bitcast"(%arg4) : (vector<4xi64>) -> vector<8xi32>
    %4 = "llvm.extractelement"(%3, %0) : (vector<8xi32>, i64) -> i32
    %5 = "llvm.zext"(%4) : (i32) -> i64
    %6 = "llvm.extractelement"(%3, %1) : (vector<8xi32>, i64) -> i32
    %7 = "llvm.zext"(%6) : (i32) -> i64
    %8 = "llvm.shl"(%7, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %9 = "llvm.add"(%8, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.return"(%9) : (i64) -> ()
}

end
end Agave.Ed25519.Encoding.RIR
