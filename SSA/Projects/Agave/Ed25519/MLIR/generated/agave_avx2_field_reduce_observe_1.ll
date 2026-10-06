; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_avx2_field_reduce_observe_1.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable
define <4 x i64> @agave_avx2_field_reduce_observe_1(<4 x i64> %v0, <4 x i64> %v1, <4 x i64> %v2, <4 x i64> %v3, <4 x i64> %v4) unnamed_addr #0 {
start:
  %0 = shufflevector <4 x i64> %v0, <4 x i64> %v1, <4 x i32> <i32 1, i32 4, i32 3, i32 6>
  %1 = bitcast <4 x i64> %0 to <8 x i32>
  %_9.i47.i = lshr <8 x i32> %1, <i32 25, i32 25, i32 26, i32 26, i32 25, i32 25, i32 26, i32 26>
  %2 = bitcast <4 x i64> %v1 to <8 x i32>
  %3 = and <8 x i32> %2, <i32 67108863, i32 67108863, i32 33554431, i32 33554431, i32 67108863, i32 67108863, i32 33554431, i32 33554431>
  %_6.i48.i = add nuw nsw <8 x i32> %_9.i47.i, %3
  %4 = bitcast <8 x i32> %_6.i48.i to <4 x i64>
  ret <4 x i64> %4
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
