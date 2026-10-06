; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_avx2_field_reduce64_observe_1.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable
define <4 x i64> @agave_avx2_field_reduce64_observe_1(<4 x i64> %v0, <4 x i64> %v1, <4 x i64> %v2, <4 x i64> %v3, <4 x i64> %v4, <4 x i64> %v5, <4 x i64> %v6, <4 x i64> %v7, <4 x i64> %v8, <4 x i64> %v9) unnamed_addr #0 {
start:
  %_5.i13.i.i = lshr <4 x i64> %v0, splat (i64 26)
  %_6.i.i15.i.i = add <4 x i64> %v1, %_5.i13.i.i
  %_5.i13.i52.i = lshr <4 x i64> %_6.i.i15.i.i, splat (i64 25)
  %_6.i.i15.i53.i = add <4 x i64> %_5.i13.i52.i, %v2
  %_5.i13.i66.i = lshr <4 x i64> %_6.i.i15.i53.i, splat (i64 26)
  %_6.i.i15.i67.i = add <4 x i64> %_5.i13.i66.i, %v3
  %0 = bitcast <4 x i64> %_6.i.i15.i53.i to <8 x i32>
  %1 = and <8 x i32> %0, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %2 = bitcast <4 x i64> %_6.i.i15.i67.i to <8 x i32>
  %3 = and <8 x i32> %2, <i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison>
  %_16.i128.i = shufflevector <8 x i32> %1, <8 x i32> %3, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  %4 = bitcast <8 x i32> %_16.i128.i to <4 x i64>
  ret <4 x i64> %4
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
