; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_avx2_field_reduce_observe_0.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable
define <4 x i64> @agave_avx2_field_reduce_observe_0(<4 x i64> %v0, <4 x i64> %v1, <4 x i64> %v2, <4 x i64> %v3, <4 x i64> %v4) unnamed_addr #0 {
start:
  %0 = bitcast <4 x i64> %v0 to <8 x i32>
  %1 = bitcast <4 x i64> %v4 to <8 x i32>
  %_8.i.i.i = lshr <8 x i32> %0, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i40.i = shufflevector <8 x i32> <i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison>, <8 x i32> %_8.i.i.i, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %2 = bitcast <4 x i64> %v0 to <8 x i32>
  %3 = and <8 x i32> %2, <i32 67108863, i32 67108863, i32 33554431, i32 33554431, i32 67108863, i32 67108863, i32 33554431, i32 33554431>
  %_6.i41.i = add nuw nsw <8 x i32> %_9.i40.i, %3
  %_8.i.i64.i = lshr <8 x i32> %1, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %4 = and <8 x i32> %_8.i.i64.i, <i32 0, i32 0, i32 127, i32 127, i32 0, i32 0, i32 127, i32 127>
  %_76.i.inner = shufflevector <8 x i32> %4, <8 x i32> poison, <8 x i32> <i32 2, i32 0, i32 3, i32 1, i32 6, i32 4, i32 7, i32 5>
  %_76.i = bitcast <8 x i32> %_76.i.inner to <4 x i64>
  %_75.i = mul nuw nsw <4 x i64> %_76.i, splat (i64 19)
  %5 = bitcast <4 x i64> %_75.i to <8 x i32>
  %_78.i = shufflevector <8 x i32> %5, <8 x i32> poison, <8 x i32> <i32 0, i32 2, i32 1, i32 3, i32 4, i32 6, i32 5, i32 7>
  %_6.i.i.i = add nuw nsw <8 x i32> %_6.i41.i, %_78.i
  %6 = bitcast <8 x i32> %_6.i.i.i to <4 x i64>
  ret <4 x i64> %6
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
