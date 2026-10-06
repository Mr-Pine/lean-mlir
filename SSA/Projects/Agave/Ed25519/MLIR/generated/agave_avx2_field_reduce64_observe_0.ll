; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_avx2_field_reduce64_observe_0.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable
define <4 x i64> @agave_avx2_field_reduce64_observe_0(<4 x i64> %v0, <4 x i64> %v1, <4 x i64> %v2, <4 x i64> %v3, <4 x i64> %v4, <4 x i64> %v5, <4 x i64> %v6, <4 x i64> %v7, <4 x i64> %v8, <4 x i64> %v9) unnamed_addr #0 {
start:
  %_5.i13.i.i = lshr <4 x i64> %v0, splat (i64 26)
  %_6.i.i15.i.i = add <4 x i64> %v1, %_5.i13.i.i
  %_6.i.i17.i.i = and <4 x i64> %v0, splat (i64 67108863)
  %_5.i13.i45.i = lshr <4 x i64> %v4, splat (i64 26)
  %_6.i.i15.i46.i = add <4 x i64> %v5, %_5.i13.i45.i
  %_6.i.i17.i55.i = and <4 x i64> %_6.i.i15.i.i, splat (i64 33554431)
  %_5.i13.i59.i = lshr <4 x i64> %_6.i.i15.i46.i, splat (i64 25)
  %_6.i.i15.i60.i = add <4 x i64> %_5.i13.i59.i, %v6
  %_5.i13.i73.i = lshr <4 x i64> %_6.i.i15.i60.i, splat (i64 26)
  %_6.i.i15.i74.i = add <4 x i64> %_5.i13.i73.i, %v7
  %_5.i13.i87.i = lshr <4 x i64> %_6.i.i15.i74.i, splat (i64 25)
  %_6.i.i15.i88.i = add <4 x i64> %_5.i13.i87.i, %v8
  %_5.i13.i101.i = lshr <4 x i64> %_6.i.i15.i88.i, splat (i64 26)
  %_6.i.i15.i102.i = add <4 x i64> %_5.i13.i101.i, %v9
  %_5.i.i = lshr <4 x i64> %_6.i.i15.i102.i, splat (i64 25)
  %_6.i105.i = and <4 x i64> %_5.i.i, splat (i64 67108863)
  %_5.i106.i = lshr <4 x i64> %_6.i.i15.i102.i, splat (i64 51)
  %_9.i.i = mul nuw nsw <4 x i64> %_6.i105.i, splat (i64 19)
  %_9.i113.i = mul nuw nsw <4 x i64> %_5.i106.i, splat (i64 19)
  %_6.i.i115.i = add nuw nsw <4 x i64> %_9.i.i, %_6.i.i17.i.i
  %_6.i.i117.i = add nuw nsw <4 x i64> %_9.i113.i, %_6.i.i17.i55.i
  %_5.i13.i121.i = lshr <4 x i64> %_6.i.i115.i, splat (i64 26)
  %_6.i.i15.i122.i = add nuw nsw <4 x i64> %_6.i.i117.i, %_5.i13.i121.i
  %0 = bitcast <4 x i64> %_6.i.i115.i to <8 x i32>
  %1 = and <8 x i32> %0, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %2 = bitcast <4 x i64> %_6.i.i15.i122.i to <8 x i32>
  %_16.i.i = shufflevector <8 x i32> %1, <8 x i32> %2, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  %3 = bitcast <8 x i32> %_16.i.i to <4 x i64>
  ret <4 x i64> %3
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
