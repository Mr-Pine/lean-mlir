; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_serial_field_mul.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
define void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([40 x i8]) align 8 captures(none) dereferenceable(40) initializes((0, 40)) %_0, ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40) %self, ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40) %_rhs) unnamed_addr #0 {
start:
  %0 = getelementptr inbounds nuw i8, ptr %_rhs, i64 8
  %_6 = load i64, ptr %0, align 8, !noundef !4
  %b1_19 = mul i64 %_6, 19
  %1 = getelementptr inbounds nuw i8, ptr %_rhs, i64 16
  %_8 = load i64, ptr %1, align 8, !noundef !4
  %b2_19 = mul i64 %_8, 19
  %2 = getelementptr inbounds nuw i8, ptr %_rhs, i64 24
  %_10 = load i64, ptr %2, align 8, !noundef !4
  %b3_19 = mul i64 %_10, 19
  %3 = getelementptr inbounds nuw i8, ptr %_rhs, i64 32
  %_12 = load i64, ptr %3, align 8, !noundef !4
  %b4_19 = mul i64 %_12, 19
  %_18 = load i64, ptr %self, align 8, !noundef !4
  %_19 = load i64, ptr %_rhs, align 8, !noundef !4
  %_91 = zext i64 %_18 to i128
  %_92 = zext i64 %_19 to i128
  %_17 = mul nuw i128 %_92, %_91
  %4 = getelementptr inbounds nuw i8, ptr %self, i64 32
  %_21 = load i64, ptr %4, align 8, !noundef !4
  %_93 = zext i64 %_21 to i128
  %_94 = zext i64 %b1_19 to i128
  %_20 = mul nuw i128 %_93, %_94
  %_16 = add i128 %_20, %_17
  %5 = getelementptr inbounds nuw i8, ptr %self, i64 24
  %_23 = load i64, ptr %5, align 8, !noundef !4
  %_95 = zext i64 %_23 to i128
  %_96 = zext i64 %b2_19 to i128
  %_22 = mul nuw i128 %_95, %_96
  %_15 = add i128 %_16, %_22
  %6 = getelementptr inbounds nuw i8, ptr %self, i64 16
  %_25 = load i64, ptr %6, align 8, !noundef !4
  %_97 = zext i64 %_25 to i128
  %_98 = zext i64 %b3_19 to i128
  %_24 = mul nuw i128 %_97, %_98
  %_14 = add i128 %_15, %_24
  %7 = getelementptr inbounds nuw i8, ptr %self, i64 8
  %_27 = load i64, ptr %7, align 8, !noundef !4
  %_99 = zext i64 %_27 to i128
  %_100 = zext i64 %b4_19 to i128
  %_26 = mul nuw i128 %_99, %_100
  %c0 = add i128 %_14, %_26
  %_32 = mul nuw i128 %_99, %_92
  %_101 = zext i64 %_6 to i128
  %_33 = mul nuw i128 %_91, %_101
  %_34 = mul nuw i128 %_93, %_96
  %_35 = mul nuw i128 %_95, %_98
  %_36 = mul nuw i128 %_97, %_100
  %_41 = mul nuw i128 %_97, %_92
  %_42 = mul nuw i128 %_99, %_101
  %_102 = zext i64 %_8 to i128
  %_43 = mul nuw i128 %_91, %_102
  %_44 = mul nuw i128 %_93, %_98
  %_45 = mul nuw i128 %_95, %_100
  %_50 = mul nuw i128 %_95, %_92
  %_51 = mul nuw i128 %_97, %_101
  %_52 = mul nuw i128 %_99, %_102
  %_103 = zext i64 %_10 to i128
  %_53 = mul nuw i128 %_91, %_103
  %_54 = mul nuw i128 %_93, %_100
  %_59 = mul nuw i128 %_93, %_92
  %_60 = mul nuw i128 %_95, %_101
  %_61 = mul nuw i128 %_97, %_102
  %_62 = mul nuw i128 %_99, %_103
  %_104 = zext i64 %_12 to i128
  %_63 = mul nuw i128 %_91, %_104
  %_67 = lshr i128 %c0, 51
  %_65 = and i128 %_67, 18446744073709551615
  %_31 = add i128 %_34, %_33
  %_30 = add i128 %_31, %_35
  %_29 = add i128 %_30, %_36
  %8 = add i128 %_29, %_32
  %9 = add i128 %8, %_65
  %_68 = trunc i128 %c0 to i64
  %10 = and i64 %_68, 2251799813685247
  %_71 = lshr i128 %9, 51
  %_69 = and i128 %_71, 18446744073709551615
  %_40 = add i128 %_44, %_43
  %_39 = add i128 %_40, %_45
  %_38 = add i128 %_39, %_41
  %11 = add i128 %_38, %_42
  %12 = add i128 %11, %_69
  %_73 = trunc i128 %9 to i64
  %13 = and i64 %_73, 2251799813685247
  %_76 = lshr i128 %12, 51
  %_74 = and i128 %_76, 18446744073709551615
  %_49 = add i128 %_54, %_53
  %_48 = add i128 %_49, %_50
  %_47 = add i128 %_48, %_51
  %14 = add i128 %_47, %_52
  %15 = add i128 %14, %_74
  %_78 = trunc i128 %12 to i64
  %16 = and i64 %_78, 2251799813685247
  %_81 = lshr i128 %15, 51
  %_79 = and i128 %_81, 18446744073709551615
  %_58 = add i128 %_59, %_63
  %_57 = add i128 %_58, %_60
  %_56 = add i128 %_57, %_61
  %17 = add i128 %_56, %_62
  %18 = add i128 %17, %_79
  %_83 = trunc i128 %15 to i64
  %19 = and i64 %_83, 2251799813685247
  %_85 = lshr i128 %18, 51
  %carry = trunc i128 %_85 to i64
  %_87 = trunc i128 %18 to i64
  %20 = and i64 %_87, 2251799813685247
  %_88 = mul i64 %carry, 19
  %21 = add i64 %_88, %10
  %_89 = lshr i64 %21, 51
  %22 = add nuw nsw i64 %_89, %13
  %23 = and i64 %21, 2251799813685247
  store i64 %23, ptr %_0, align 8
  %out.sroa.8.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 8
  store i64 %22, ptr %out.sroa.8.0._0.sroa_idx, align 8
  %out.sroa.11.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 16
  store i64 %16, ptr %out.sroa.11.0._0.sroa_idx, align 8
  %out.sroa.12.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 24
  store i64 %19, ptr %out.sroa.12.0._0.sroa_idx, align 8
  %out.sroa.13.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 32
  store i64 %20, ptr %out.sroa.13.0._0.sroa_idx, align 8
  ret void
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{}
