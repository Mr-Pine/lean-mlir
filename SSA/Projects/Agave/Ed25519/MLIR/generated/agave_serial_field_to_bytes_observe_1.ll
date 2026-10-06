; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_serial_field_to_bytes_observe_1.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable
define noundef i64 @agave_serial_field_to_bytes_observe_1(i64 noundef %v0, i64 noundef %v1, i64 noundef %v2, i64 noundef %v3, i64 noundef %v4) unnamed_addr #0 {
start:
  %_98.i = lshr i64 %v0, 51
  %_100.i = lshr i64 %v1, 51
  %_102.i = lshr i64 %v2, 51
  %_104.i = lshr i64 %v3, 51
  %_106.i = lshr i64 %v4, 51
  %0 = and i64 %v0, 2251799813685247
  %1 = and i64 %v1, 2251799813685247
  %2 = and i64 %v2, 2251799813685247
  %3 = and i64 %v3, 2251799813685247
  %4 = and i64 %v4, 2251799813685247
  %_108.i = mul nuw nsw i64 %_106.i, 19
  %5 = add nuw nsw i64 %_108.i, %0
  %6 = add nuw nsw i64 %1, %_98.i
  %7 = add nuw nsw i64 %2, %_100.i
  %8 = add nuw nsw i64 %3, %_102.i
  %9 = add nuw nsw i64 %4, %_104.i
  %_4.i = add nuw nsw i64 %5, 19
  %10 = lshr i64 %_4.i, 51
  %_6.i = add nuw nsw i64 %10, %6
  %11 = lshr i64 %_6.i, 51
  %_8.i = add nuw nsw i64 %11, %7
  %12 = lshr i64 %_8.i, 51
  %_10.i = add nuw nsw i64 %8, %12
  %13 = lshr i64 %_10.i, 51
  %_12.i = add nuw nsw i64 %9, %13
  %14 = lshr i64 %_12.i, 51
  %_14.i = mul nuw nsw i64 %14, 19
  %15 = add nuw nsw i64 %_14.i, %5
  %_15.i = lshr i64 %15, 51
  %16 = add nuw nsw i64 %_15.i, %6
  %_17.i = lshr i64 %16, 51
  %17 = add nuw nsw i64 %_17.i, %7
  %_41.i = lshr i64 %16, 13
  %18 = lshr i64 %16, 45
  %_50.i = and i64 %18, 63
  %19 = shl nuw nsw i64 %17, 6
  %20 = shl i64 %17, 38
  %.masked = and i64 %19, 192
  %_9.sroa.7.0.insert.ext = or disjoint i64 %.masked, %_50.i
  %_9.sroa.7.0.insert.shift = shl nuw nsw i64 %_9.sroa.7.0.insert.ext, 32
  %_9.sroa.0.0.insert.ext = and i64 %_41.i, 255
  %_9.sroa.8.0.insert.insert = and i64 %_41.i, 4294967040
  %21 = and i64 %20, -1099511627776
  %_9.sroa.4.0.insert.mask = or disjoint i64 %_9.sroa.8.0.insert.insert, %21
  %_9.sroa.0.0.insert.mask = or disjoint i64 %_9.sroa.4.0.insert.mask, %_9.sroa.7.0.insert.shift
  %_9.sroa.0.0.insert.insert = or disjoint i64 %_9.sroa.0.0.insert.mask, %_9.sroa.0.0.insert.ext
  ret i64 %_9.sroa.0.0.insert.insert
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
