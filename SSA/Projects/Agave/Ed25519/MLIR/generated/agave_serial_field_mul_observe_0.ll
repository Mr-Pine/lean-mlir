; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_serial_field_mul_observe_0.before-inline.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable
define noundef i64 @agave_serial_field_mul_observe_0(i64 noundef %v0, i64 noundef %v1, i64 noundef %v2, i64 noundef %v3, i64 noundef %v4, i64 noundef %v5, i64 noundef %v6, i64 noundef %v7, i64 noundef %v8, i64 noundef %v9) unnamed_addr #0 {
start:
  %b1_19.i = mul i64 %v6, 19
  %b2_19.i = mul i64 %v7, 19
  %b3_19.i = mul i64 %v8, 19
  %b4_19.i = mul i64 %v9, 19
  %_91.i = zext i64 %v0 to i128
  %_92.i = zext i64 %v5 to i128
  %_17.i = mul nuw i128 %_92.i, %_91.i
  %_93.i = zext i64 %v4 to i128
  %_94.i = zext i64 %b1_19.i to i128
  %_20.i = mul nuw i128 %_93.i, %_94.i
  %_16.i = add i128 %_20.i, %_17.i
  %_95.i = zext i64 %v3 to i128
  %_96.i = zext i64 %b2_19.i to i128
  %_22.i = mul nuw i128 %_95.i, %_96.i
  %_15.i = add i128 %_16.i, %_22.i
  %_97.i = zext i64 %v2 to i128
  %_98.i = zext i64 %b3_19.i to i128
  %_24.i = mul nuw i128 %_97.i, %_98.i
  %_14.i = add i128 %_15.i, %_24.i
  %_99.i = zext i64 %v1 to i128
  %_100.i = zext i64 %b4_19.i to i128
  %_26.i = mul nuw i128 %_99.i, %_100.i
  %c0.i = add i128 %_14.i, %_26.i
  %_32.i = mul nuw i128 %_99.i, %_92.i
  %_101.i = zext i64 %v6 to i128
  %_33.i = mul nuw i128 %_91.i, %_101.i
  %_34.i = mul nuw i128 %_93.i, %_96.i
  %_35.i = mul nuw i128 %_95.i, %_98.i
  %_36.i = mul nuw i128 %_97.i, %_100.i
  %_41.i = mul nuw i128 %_97.i, %_92.i
  %_42.i = mul nuw i128 %_99.i, %_101.i
  %_102.i = zext i64 %v7 to i128
  %_43.i = mul nuw i128 %_91.i, %_102.i
  %_44.i = mul nuw i128 %_93.i, %_98.i
  %_45.i = mul nuw i128 %_95.i, %_100.i
  %_50.i = mul nuw i128 %_95.i, %_92.i
  %_51.i = mul nuw i128 %_97.i, %_101.i
  %_52.i = mul nuw i128 %_99.i, %_102.i
  %_103.i = zext i64 %v8 to i128
  %_53.i = mul nuw i128 %_91.i, %_103.i
  %_54.i = mul nuw i128 %_93.i, %_100.i
  %_59.i = mul nuw i128 %_93.i, %_92.i
  %_60.i = mul nuw i128 %_95.i, %_101.i
  %_61.i = mul nuw i128 %_97.i, %_102.i
  %_62.i = mul nuw i128 %_99.i, %_103.i
  %_104.i = zext i64 %v9 to i128
  %_63.i = mul nuw i128 %_91.i, %_104.i
  %_67.i = lshr i128 %c0.i, 51
  %_65.i = and i128 %_67.i, 18446744073709551615
  %_31.i = add i128 %_34.i, %_33.i
  %_30.i = add i128 %_31.i, %_35.i
  %_29.i = add i128 %_30.i, %_36.i
  %0 = add i128 %_29.i, %_32.i
  %1 = add i128 %0, %_65.i
  %_68.i = trunc i128 %c0.i to i64
  %_71.i = lshr i128 %1, 51
  %_69.i = and i128 %_71.i, 18446744073709551615
  %_40.i = add i128 %_44.i, %_43.i
  %_39.i = add i128 %_40.i, %_45.i
  %_38.i = add i128 %_39.i, %_41.i
  %2 = add i128 %_38.i, %_42.i
  %3 = add i128 %2, %_69.i
  %_76.i = lshr i128 %3, 51
  %_74.i = and i128 %_76.i, 18446744073709551615
  %_49.i = add i128 %_54.i, %_53.i
  %_48.i = add i128 %_49.i, %_50.i
  %_47.i = add i128 %_48.i, %_51.i
  %4 = add i128 %_47.i, %_52.i
  %5 = add i128 %4, %_74.i
  %_81.i = lshr i128 %5, 51
  %_79.i = and i128 %_81.i, 18446744073709551615
  %_58.i = add i128 %_59.i, %_63.i
  %_57.i = add i128 %_58.i, %_60.i
  %_56.i = add i128 %_57.i, %_61.i
  %6 = add i128 %_56.i, %_62.i
  %7 = add i128 %6, %_79.i
  %_85.i = lshr i128 %7, 51
  %carry.i = trunc i128 %_85.i to i64
  %_88.i = mul i64 %carry.i, 19
  %8 = add i64 %_88.i, %_68.i
  %9 = and i64 %8, 2251799813685247
  ret i64 %9
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
