; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_serial_field_square.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable
define void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([40 x i8]) align 8 captures(none) dereferenceable(40) %_0, ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40) %self, i32 noundef %0) unnamed_addr #0 {
start:
  %a.sroa.0.0.copyload = load i64, ptr %self, align 8
  %a.sroa.14.0.self.sroa_idx = getelementptr inbounds nuw i8, ptr %self, i64 8
  %a.sroa.14.0.copyload = load i64, ptr %a.sroa.14.0.self.sroa_idx, align 8
  %a.sroa.23.0.self.sroa_idx = getelementptr inbounds nuw i8, ptr %self, i64 16
  %a.sroa.23.0.copyload = load i64, ptr %a.sroa.23.0.self.sroa_idx, align 8
  %a.sroa.30.0.self.sroa_idx = getelementptr inbounds nuw i8, ptr %self, i64 24
  %a.sroa.30.0.copyload = load i64, ptr %a.sroa.30.0.self.sroa_idx, align 8
  %a.sroa.35.0.self.sroa_idx = getelementptr inbounds nuw i8, ptr %self, i64 32
  %a.sroa.35.0.copyload = load i64, ptr %a.sroa.35.0.self.sroa_idx, align 8
  br label %bb1

bb1:                                              ; preds = %bb1, %start
  %a.sroa.35.0 = phi i64 [ %a.sroa.35.0.copyload, %start ], [ %13, %bb1 ]
  %a.sroa.30.0 = phi i64 [ %a.sroa.30.0.copyload, %start ], [ %12, %bb1 ]
  %a.sroa.23.0 = phi i64 [ %a.sroa.23.0.copyload, %start ], [ %10, %bb1 ]
  %a.sroa.14.0 = phi i64 [ %a.sroa.14.0.copyload, %start ], [ %15, %bb1 ]
  %a.sroa.0.0 = phi i64 [ %a.sroa.0.0.copyload, %start ], [ %16, %bb1 ]
  %k.sroa.0.0 = phi i32 [ %0, %start ], [ %17, %bb1 ]
  %a3_19 = mul i64 %a.sroa.30.0, 19
  %a4_19 = mul i64 %a.sroa.35.0, 19
  %_89 = zext i64 %a.sroa.0.0 to i128
  %_9 = mul nuw i128 %_89, %_89
  %_91 = zext i64 %a.sroa.14.0 to i128
  %_92 = zext i64 %a4_19 to i128
  %_14 = mul nuw i128 %_91, %_92
  %_93 = zext i64 %a.sroa.23.0 to i128
  %_94 = zext i64 %a3_19 to i128
  %_16 = mul nuw i128 %_93, %_94
  %_13 = add i128 %_14, %_16
  %_12 = shl i128 %_13, 1
  %c0 = add i128 %_12, %_9
  %_95 = zext i64 %a.sroa.30.0 to i128
  %_19 = mul nuw i128 %_94, %_95
  %_23 = mul nuw i128 %_89, %_91
  %_26 = mul nuw i128 %_93, %_92
  %_22 = add i128 %_23, %_26
  %_21 = shl i128 %_22, 1
  %1 = add i128 %_21, %_19
  %_29 = mul nuw i128 %_91, %_91
  %_34 = mul nuw i128 %_89, %_93
  %_103 = zext i64 %a.sroa.35.0 to i128
  %_37 = mul nuw i128 %_94, %_103
  %_33 = add i128 %_34, %_37
  %_32 = shl i128 %_33, 1
  %2 = add i128 %_32, %_29
  %_40 = mul nuw i128 %_92, %_103
  %_44 = mul nuw i128 %_89, %_95
  %_47 = mul nuw i128 %_91, %_93
  %_43 = add i128 %_44, %_47
  %_42 = shl i128 %_43, 1
  %3 = add i128 %_42, %_40
  %_51 = mul nuw i128 %_93, %_93
  %_56 = mul nuw i128 %_89, %_103
  %_59 = mul nuw i128 %_91, %_95
  %_55 = add i128 %_56, %_59
  %_54 = shl i128 %_55, 1
  %4 = add i128 %_54, %_51
  %_64 = lshr i128 %c0, 51
  %_62 = and i128 %_64, 18446744073709551615
  %5 = add i128 %1, %_62
  %_65 = trunc i128 %c0 to i64
  %6 = and i64 %_65, 2251799813685247
  %_68 = lshr i128 %5, 51
  %_66 = and i128 %_68, 18446744073709551615
  %7 = add i128 %2, %_66
  %_70 = trunc i128 %5 to i64
  %8 = and i64 %_70, 2251799813685247
  %_73 = lshr i128 %7, 51
  %_71 = and i128 %_73, 18446744073709551615
  %9 = add i128 %3, %_71
  %_75 = trunc i128 %7 to i64
  %10 = and i64 %_75, 2251799813685247
  %_78 = lshr i128 %9, 51
  %_76 = and i128 %_78, 18446744073709551615
  %11 = add i128 %4, %_76
  %_80 = trunc i128 %9 to i64
  %12 = and i64 %_80, 2251799813685247
  %_82 = lshr i128 %11, 51
  %carry = trunc i128 %_82 to i64
  %_84 = trunc i128 %11 to i64
  %13 = and i64 %_84, 2251799813685247
  %_85 = mul i64 %carry, 19
  %14 = add i64 %_85, %6
  %_86 = lshr i64 %14, 51
  %15 = add nuw nsw i64 %_86, %8
  %16 = and i64 %14, 2251799813685247
  %17 = add i32 %k.sroa.0.0, -1
  %18 = icmp eq i32 %17, 0
  br i1 %18, label %bb2, label %bb1

bb2:                                              ; preds = %bb1
  store i64 %16, ptr %_0, align 8
  %a.sroa.14.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 8
  store i64 %15, ptr %a.sroa.14.0._0.sroa_idx, align 8
  %a.sroa.23.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 16
  store i64 %10, ptr %a.sroa.23.0._0.sroa_idx, align 8
  %a.sroa.30.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 24
  store i64 %12, ptr %a.sroa.30.0._0.sroa_idx, align 8
  %a.sroa.35.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 32
  store i64 %13, ptr %a.sroa.35.0._0.sroa_idx, align 8
  ret void
}

attributes #0 = { nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
