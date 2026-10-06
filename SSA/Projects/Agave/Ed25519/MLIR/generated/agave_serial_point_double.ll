; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_serial_point_double.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable
declare void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([40 x i8]) align 8 captures(none) dereferenceable(40), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40), i32 noundef) unnamed_addr #0

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
define void @_RNvMsa_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_15ProjectivePoint6double(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([160 x i8]) align 8 captures(none) dereferenceable(160) initializes((0, 160)) %_0, ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(120) %self) unnamed_addr #1 {
start:
  %X_plus_Y_sq = alloca [40 x i8], align 8
  %X_plus_Y = alloca [40 x i8], align 16
  %ZZ2 = alloca [40 x i8], align 8
  %YY = alloca [40 x i8], align 8
  %XX = alloca [40 x i8], align 8
  call void @llvm.lifetime.start.p0(ptr nonnull %XX)
  call void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %XX, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %self, i32 noundef 1) #4, !alias.scope !4
  call void @llvm.lifetime.start.p0(ptr nonnull %YY)
  %_5 = getelementptr inbounds nuw i8, ptr %self, i64 40
  call void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %YY, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_5, i32 noundef 1) #4, !alias.scope !8
  call void @llvm.lifetime.start.p0(ptr nonnull %ZZ2)
  %_7 = getelementptr inbounds nuw i8, ptr %self, i64 80
  tail call void @llvm.experimental.noalias.scope.decl(metadata !12)
  call void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %ZZ2, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_7, i32 noundef 1) #4, !alias.scope !15
  %0 = load i64, ptr %ZZ2, align 8, !alias.scope !17, !noalias !12, !noundef !18
  %1 = shl i64 %0, 1
  %2 = getelementptr inbounds nuw i8, ptr %ZZ2, i64 8
  %3 = load i64, ptr %2, align 8, !alias.scope !17, !noalias !12, !noundef !18
  %4 = shl i64 %3, 1
  %5 = getelementptr inbounds nuw i8, ptr %ZZ2, i64 16
  %6 = load i64, ptr %5, align 8, !alias.scope !17, !noalias !12, !noundef !18
  %7 = shl i64 %6, 1
  %8 = getelementptr inbounds nuw i8, ptr %ZZ2, i64 24
  %9 = load i64, ptr %8, align 8, !alias.scope !17, !noalias !12, !noundef !18
  %10 = shl i64 %9, 1
  %11 = getelementptr inbounds nuw i8, ptr %ZZ2, i64 32
  %12 = load i64, ptr %11, align 8, !alias.scope !17, !noalias !12, !noundef !18
  %13 = shl i64 %12, 1
  call void @llvm.lifetime.start.p0(ptr nonnull %X_plus_Y)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !19)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !22)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !24)
  %output.sroa.8.0.self.sroa_idx.i = getelementptr inbounds nuw i8, ptr %self, i64 16
  %output.sroa.12.0.self.sroa_idx.i = getelementptr inbounds nuw i8, ptr %self, i64 32
  %output.sroa.12.0.copyload.i = load i64, ptr %output.sroa.12.0.self.sroa_idx.i, align 8, !alias.scope !22, !noalias !26
  %14 = getelementptr inbounds nuw i8, ptr %self, i64 56
  %15 = getelementptr inbounds nuw i8, ptr %self, i64 72
  %_5.4.i.i = load i64, ptr %15, align 8, !alias.scope !27, !noalias !30, !noundef !18
  %16 = add i64 %_5.4.i.i, %output.sroa.12.0.copyload.i
  %17 = load <2 x i64>, ptr %self, align 8, !alias.scope !22, !noalias !26
  %18 = load <2 x i64>, ptr %_5, align 8, !alias.scope !27, !noalias !30
  %19 = add <2 x i64> %18, %17
  store <2 x i64> %19, ptr %X_plus_Y, align 16, !alias.scope !19, !noalias !32
  %output.sroa.8.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %X_plus_Y, i64 16
  %20 = load <2 x i64>, ptr %output.sroa.8.0.self.sroa_idx.i, align 8, !alias.scope !22, !noalias !26
  %21 = load <2 x i64>, ptr %14, align 8, !alias.scope !27, !noalias !30
  %22 = add <2 x i64> %21, %20
  store <2 x i64> %22, ptr %output.sroa.8.0._0.sroa_idx.i, align 16, !alias.scope !19, !noalias !32
  %output.sroa.12.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %X_plus_Y, i64 32
  store i64 %16, ptr %output.sroa.12.0._0.sroa_idx.i, align 16, !alias.scope !19, !noalias !32
  call void @llvm.lifetime.start.p0(ptr nonnull %X_plus_Y_sq)
  call void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %X_plus_Y_sq, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %X_plus_Y, i32 noundef 1) #4, !alias.scope !33
  tail call void @llvm.experimental.noalias.scope.decl(metadata !37)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !40)
  %output.sroa.0.0.copyload.i1 = load i64, ptr %YY, align 8, !alias.scope !37, !noalias !42
  %output.sroa.6.0.self.sroa_idx.i2 = getelementptr inbounds nuw i8, ptr %YY, i64 8
  %output.sroa.6.0.copyload.i3 = load i64, ptr %output.sroa.6.0.self.sroa_idx.i2, align 8, !alias.scope !37, !noalias !42
  %output.sroa.8.0.self.sroa_idx.i4 = getelementptr inbounds nuw i8, ptr %YY, i64 16
  %output.sroa.8.0.copyload.i5 = load i64, ptr %output.sroa.8.0.self.sroa_idx.i4, align 8, !alias.scope !37, !noalias !42
  %output.sroa.10.0.self.sroa_idx.i6 = getelementptr inbounds nuw i8, ptr %YY, i64 24
  %output.sroa.10.0.copyload.i7 = load i64, ptr %output.sroa.10.0.self.sroa_idx.i6, align 8, !alias.scope !37, !noalias !42
  %output.sroa.12.0.self.sroa_idx.i8 = getelementptr inbounds nuw i8, ptr %YY, i64 32
  %output.sroa.12.0.copyload.i9 = load i64, ptr %output.sroa.12.0.self.sroa_idx.i8, align 8, !alias.scope !37, !noalias !42
  %_5.i.i10 = load i64, ptr %XX, align 8, !alias.scope !44, !noalias !47, !noundef !18
  %23 = add i64 %_5.i.i10, %output.sroa.0.0.copyload.i1
  %24 = getelementptr inbounds nuw i8, ptr %XX, i64 8
  %_5.1.i.i11 = load i64, ptr %24, align 8, !alias.scope !44, !noalias !47, !noundef !18
  %25 = add i64 %_5.1.i.i11, %output.sroa.6.0.copyload.i3
  %26 = getelementptr inbounds nuw i8, ptr %XX, i64 16
  %_5.2.i.i12 = load i64, ptr %26, align 8, !alias.scope !44, !noalias !47, !noundef !18
  %27 = add i64 %_5.2.i.i12, %output.sroa.8.0.copyload.i5
  %28 = getelementptr inbounds nuw i8, ptr %XX, i64 24
  %_5.3.i.i13 = load i64, ptr %28, align 8, !alias.scope !44, !noalias !47, !noundef !18
  %29 = add i64 %_5.3.i.i13, %output.sroa.10.0.copyload.i7
  %30 = getelementptr inbounds nuw i8, ptr %XX, i64 32
  %_5.4.i.i14 = load i64, ptr %30, align 8, !alias.scope !44, !noalias !47, !noundef !18
  %31 = add i64 %_5.4.i.i14, %output.sroa.12.0.copyload.i9
  %_5.i = add i64 %output.sroa.0.0.copyload.i1, 36028797018963664
  %_4.i = sub i64 %_5.i, %_5.i.i10
  %_9.i = add i64 %output.sroa.6.0.copyload.i3, 36028797018963952
  %_8.i = sub i64 %_9.i, %_5.1.i.i11
  %_13.i = add i64 %output.sroa.8.0.copyload.i5, 36028797018963952
  %_12.i = sub i64 %_13.i, %_5.2.i.i12
  %_17.i = add i64 %output.sroa.10.0.copyload.i7, 36028797018963952
  %_16.i = sub i64 %_17.i, %_5.3.i.i13
  %_21.i = add i64 %output.sroa.12.0.copyload.i9, 36028797018963952
  %_20.i = sub i64 %_21.i, %_5.4.i.i14
  %_24.i = lshr i64 %_4.i, 51
  %_26.i = lshr i64 %_8.i, 51
  %_28.i = lshr i64 %_12.i, 51
  %_30.i = lshr i64 %_16.i, 51
  %_32.i = lshr i64 %_20.i, 51
  %32 = and i64 %_4.i, 2251799813685247
  %33 = and i64 %_8.i, 2251799813685247
  %34 = and i64 %_12.i, 2251799813685247
  %35 = and i64 %_16.i, 2251799813685247
  %36 = and i64 %_20.i, 2251799813685247
  %_34.i = mul nuw nsw i64 %_32.i, 19
  %37 = add nuw nsw i64 %_34.i, %32
  %38 = add nuw nsw i64 %33, %_24.i
  %39 = add nuw nsw i64 %34, %_26.i
  %40 = add nuw nsw i64 %35, %_28.i
  %41 = add nuw nsw i64 %36, %_30.i
  %_6.i19 = load i64, ptr %X_plus_Y_sq, align 8, !alias.scope !49, !noalias !52, !noundef !18
  %reass.sub = sub i64 %_6.i19, %23
  %_4.i22 = add i64 %reass.sub, 36028797018963664
  %42 = getelementptr inbounds nuw i8, ptr %X_plus_Y_sq, i64 8
  %_10.i23 = load i64, ptr %42, align 8, !alias.scope !49, !noalias !52, !noundef !18
  %reass.sub88 = sub i64 %_10.i23, %25
  %_8.i26 = add i64 %reass.sub88, 36028797018963952
  %43 = getelementptr inbounds nuw i8, ptr %X_plus_Y_sq, i64 16
  %_14.i27 = load i64, ptr %43, align 8, !alias.scope !49, !noalias !52, !noundef !18
  %reass.sub89 = sub i64 %_14.i27, %27
  %_12.i30 = add i64 %reass.sub89, 36028797018963952
  %44 = getelementptr inbounds nuw i8, ptr %X_plus_Y_sq, i64 24
  %_18.i31 = load i64, ptr %44, align 8, !alias.scope !49, !noalias !52, !noundef !18
  %reass.sub90 = sub i64 %_18.i31, %29
  %_16.i34 = add i64 %reass.sub90, 36028797018963952
  %45 = getelementptr inbounds nuw i8, ptr %X_plus_Y_sq, i64 32
  %_22.i35 = load i64, ptr %45, align 8, !alias.scope !49, !noalias !52, !noundef !18
  %reass.sub91 = sub i64 %_22.i35, %31
  %_20.i38 = add i64 %reass.sub91, 36028797018963952
  %_24.i39 = lshr i64 %_4.i22, 51
  %_26.i40 = lshr i64 %_8.i26, 51
  %_28.i41 = lshr i64 %_12.i30, 51
  %_30.i42 = lshr i64 %_16.i34, 51
  %_32.i43 = lshr i64 %_20.i38, 51
  %46 = and i64 %_4.i22, 2251799813685247
  %47 = and i64 %_8.i26, 2251799813685247
  %48 = and i64 %_12.i30, 2251799813685247
  %49 = and i64 %_16.i34, 2251799813685247
  %50 = and i64 %_20.i38, 2251799813685247
  %_34.i44 = mul nuw nsw i64 %_32.i43, 19
  %51 = add nuw nsw i64 %_34.i44, %46
  %52 = add nuw nsw i64 %47, %_24.i39
  %53 = add nuw nsw i64 %48, %_26.i40
  %54 = add nuw nsw i64 %49, %_28.i41
  %55 = add nuw nsw i64 %50, %_30.i42
  %_5.i50 = add i64 %1, 36028797018963664
  %_4.i52 = sub i64 %_5.i50, %37
  %_9.i54 = add i64 %4, 36028797018963952
  %_8.i56 = sub i64 %_9.i54, %38
  %_13.i58 = add i64 %7, 36028797018963952
  %_12.i60 = sub i64 %_13.i58, %39
  %_17.i62 = add i64 %10, 36028797018963952
  %_16.i64 = sub i64 %_17.i62, %40
  %_21.i66 = add i64 %13, 36028797018963952
  %_20.i68 = sub i64 %_21.i66, %41
  %_24.i69 = lshr i64 %_4.i52, 51
  %_26.i70 = lshr i64 %_8.i56, 51
  %_28.i71 = lshr i64 %_12.i60, 51
  %_30.i72 = lshr i64 %_16.i64, 51
  %_32.i73 = lshr i64 %_20.i68, 51
  %56 = and i64 %_4.i52, 2251799813685247
  %57 = and i64 %_8.i56, 2251799813685247
  %58 = and i64 %_12.i60, 2251799813685247
  %59 = and i64 %_16.i64, 2251799813685247
  %60 = and i64 %_20.i68, 2251799813685247
  %_34.i74 = mul nuw nsw i64 %_32.i73, 19
  %61 = add nuw nsw i64 %_34.i74, %56
  %62 = add nuw nsw i64 %_24.i69, %57
  %63 = add nuw nsw i64 %58, %_26.i70
  %64 = add nuw nsw i64 %59, %_28.i71
  %65 = add nuw nsw i64 %60, %_30.i72
  store i64 %51, ptr %_0, align 8
  %_19.sroa.4.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 8
  store i64 %52, ptr %_19.sroa.4.0._0.sroa_idx, align 8
  %_19.sroa.5.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 16
  store i64 %53, ptr %_19.sroa.5.0._0.sroa_idx, align 8
  %_19.sroa.6.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 24
  store i64 %54, ptr %_19.sroa.6.0._0.sroa_idx, align 8
  %_19.sroa.7.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 32
  store i64 %55, ptr %_19.sroa.7.0._0.sroa_idx, align 8
  %66 = getelementptr inbounds nuw i8, ptr %_0, i64 40
  store i64 %23, ptr %66, align 8
  %YY_plus_XX.sroa.5.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 48
  store i64 %25, ptr %YY_plus_XX.sroa.5.0..sroa_idx, align 8
  %YY_plus_XX.sroa.7.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 56
  store i64 %27, ptr %YY_plus_XX.sroa.7.0..sroa_idx, align 8
  %YY_plus_XX.sroa.9.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 64
  store i64 %29, ptr %YY_plus_XX.sroa.9.0..sroa_idx, align 8
  %YY_plus_XX.sroa.11.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 72
  store i64 %31, ptr %YY_plus_XX.sroa.11.0..sroa_idx, align 8
  %67 = getelementptr inbounds nuw i8, ptr %_0, i64 80
  store i64 %37, ptr %67, align 8
  %YY_minus_XX.sroa.5.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 88
  store i64 %38, ptr %YY_minus_XX.sroa.5.0..sroa_idx, align 8
  %YY_minus_XX.sroa.7.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 96
  store i64 %39, ptr %YY_minus_XX.sroa.7.0..sroa_idx, align 8
  %YY_minus_XX.sroa.9.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 104
  store i64 %40, ptr %YY_minus_XX.sroa.9.0..sroa_idx, align 8
  %YY_minus_XX.sroa.11.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 112
  store i64 %41, ptr %YY_minus_XX.sroa.11.0..sroa_idx, align 8
  %68 = getelementptr inbounds nuw i8, ptr %_0, i64 120
  store i64 %61, ptr %68, align 8
  %_22.sroa.4.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 128
  store i64 %62, ptr %_22.sroa.4.0..sroa_idx, align 8
  %_22.sroa.5.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 136
  store i64 %63, ptr %_22.sroa.5.0..sroa_idx, align 8
  %_22.sroa.6.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 144
  store i64 %64, ptr %_22.sroa.6.0..sroa_idx, align 8
  %_22.sroa.7.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 152
  store i64 %65, ptr %_22.sroa.7.0..sroa_idx, align 8
  call void @llvm.lifetime.end.p0(ptr nonnull %X_plus_Y_sq)
  call void @llvm.lifetime.end.p0(ptr nonnull %X_plus_Y)
  call void @llvm.lifetime.end.p0(ptr nonnull %ZZ2)
  call void @llvm.lifetime.end.p0(ptr nonnull %YY)
  call void @llvm.lifetime.end.p0(ptr nonnull %XX)
  ret void
}

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #2

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #2

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite)
declare void @llvm.experimental.noalias.scope.decl(metadata) #3

attributes #0 = { nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #3 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite) }
attributes #4 = { nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{!5, !7}
!5 = distinct !{!5, !6, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement516square: %_0"}
!6 = distinct !{!6, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement516square"}
!7 = distinct !{!7, !6, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement516square: %self"}
!8 = !{!9, !11}
!9 = distinct !{!9, !10, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement516square: %_0"}
!10 = distinct !{!10, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement516square"}
!11 = distinct !{!11, !10, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement516square: %self"}
!12 = !{!13}
!13 = distinct !{!13, !14, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement517square2: %self"}
!14 = distinct !{!14, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement517square2"}
!15 = !{!16, !13}
!16 = distinct !{!16, !14, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement517square2: %square"}
!17 = !{!16}
!18 = !{}
!19 = !{!20}
!20 = distinct !{!20, !21, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %_0"}
!21 = distinct !{!21, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add"}
!22 = !{!23}
!23 = distinct !{!23, !21, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %self"}
!24 = !{!25}
!25 = distinct !{!25, !21, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %_rhs"}
!26 = !{!20, !25}
!27 = !{!28, !25}
!28 = distinct !{!28, !29, !"_RNvXs0_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51INtNtNtCsgxBkk5gSRhY_4core3ops5arith9AddAssignRB16_E10add_assign: %_rhs"}
!29 = distinct !{!29, !"_RNvXs0_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51INtNtNtCsgxBkk5gSRhY_4core3ops5arith9AddAssignRB16_E10add_assign"}
!30 = !{!31, !20, !23}
!31 = distinct !{!31, !29, !"_RNvXs0_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51INtNtNtCsgxBkk5gSRhY_4core3ops5arith9AddAssignRB16_E10add_assign: %self"}
!32 = !{!23, !25}
!33 = !{!34, !36}
!34 = distinct !{!34, !35, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement516square: %_0"}
!35 = distinct !{!35, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement516square"}
!36 = distinct !{!36, !35, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement516square: %self"}
!37 = !{!38}
!38 = distinct !{!38, !39, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %self"}
!39 = distinct !{!39, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add"}
!40 = !{!41}
!41 = distinct !{!41, !39, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %_rhs"}
!42 = !{!43, !41}
!43 = distinct !{!43, !39, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %_0"}
!44 = !{!45, !41}
!45 = distinct !{!45, !46, !"_RNvXs0_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51INtNtNtCsgxBkk5gSRhY_4core3ops5arith9AddAssignRB16_E10add_assign: %_rhs"}
!46 = distinct !{!46, !"_RNvXs0_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51INtNtNtCsgxBkk5gSRhY_4core3ops5arith9AddAssignRB16_E10add_assign"}
!47 = !{!48, !43, !38}
!48 = distinct !{!48, !46, !"_RNvXs0_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51INtNtNtCsgxBkk5gSRhY_4core3ops5arith9AddAssignRB16_E10add_assign: %self"}
!49 = !{!50}
!50 = distinct !{!50, !51, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub: %self"}
!51 = distinct !{!51, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub"}
!52 = !{!53, !54}
!53 = distinct !{!53, !51, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub: %_0"}
!54 = distinct !{!54, !51, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub: %_rhs"}
