; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_serial_point_affine_sub.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
declare void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([40 x i8]) align 8 captures(none) dereferenceable(40) initializes((0, 40)), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40)) unnamed_addr #0

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
define void @_RNvXse_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB5_16AffineNielsPointE3sub(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([160 x i8]) align 8 captures(none) dereferenceable(160) initializes((0, 160)) %_0, ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160) %self, ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(120) %other) unnamed_addr #1 {
start:
  %Txy2d = alloca [40 x i8], align 8
  %MP = alloca [40 x i8], align 8
  %PM = alloca [40 x i8], align 8
  %Y_minus_X = alloca [40 x i8], align 8
  %Y_plus_X = alloca [40 x i8], align 8
  call void @llvm.lifetime.start.p0(ptr nonnull %Y_plus_X)
  %_4 = getelementptr inbounds nuw i8, ptr %self, i64 40
  tail call void @llvm.experimental.noalias.scope.decl(metadata !4)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !7)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !9)
  %output.sroa.0.0.copyload.i = load i64, ptr %_4, align 8, !alias.scope !7, !noalias !11
  %output.sroa.6.0.self.sroa_idx.i = getelementptr inbounds nuw i8, ptr %self, i64 48
  %output.sroa.6.0.copyload.i = load i64, ptr %output.sroa.6.0.self.sroa_idx.i, align 8, !alias.scope !7, !noalias !11
  %output.sroa.8.0.self.sroa_idx.i = getelementptr inbounds nuw i8, ptr %self, i64 56
  %output.sroa.8.0.copyload.i = load i64, ptr %output.sroa.8.0.self.sroa_idx.i, align 8, !alias.scope !7, !noalias !11
  %output.sroa.10.0.self.sroa_idx.i = getelementptr inbounds nuw i8, ptr %self, i64 64
  %output.sroa.10.0.copyload.i = load i64, ptr %output.sroa.10.0.self.sroa_idx.i, align 8, !alias.scope !7, !noalias !11
  %output.sroa.12.0.self.sroa_idx.i = getelementptr inbounds nuw i8, ptr %self, i64 72
  %output.sroa.12.0.copyload.i = load i64, ptr %output.sroa.12.0.self.sroa_idx.i, align 8, !alias.scope !7, !noalias !11
  %_5.i.i = load i64, ptr %self, align 8, !alias.scope !12, !noalias !15, !noundef !17
  %0 = add i64 %_5.i.i, %output.sroa.0.0.copyload.i
  %1 = getelementptr inbounds nuw i8, ptr %self, i64 8
  %_5.1.i.i = load i64, ptr %1, align 8, !alias.scope !12, !noalias !15, !noundef !17
  %2 = add i64 %_5.1.i.i, %output.sroa.6.0.copyload.i
  %3 = getelementptr inbounds nuw i8, ptr %self, i64 16
  %_5.2.i.i = load i64, ptr %3, align 8, !alias.scope !12, !noalias !15, !noundef !17
  %4 = add i64 %_5.2.i.i, %output.sroa.8.0.copyload.i
  %5 = getelementptr inbounds nuw i8, ptr %self, i64 24
  %_5.3.i.i = load i64, ptr %5, align 8, !alias.scope !12, !noalias !15, !noundef !17
  %6 = add i64 %_5.3.i.i, %output.sroa.10.0.copyload.i
  %7 = getelementptr inbounds nuw i8, ptr %self, i64 32
  %_5.4.i.i = load i64, ptr %7, align 8, !alias.scope !12, !noalias !15, !noundef !17
  %8 = add i64 %_5.4.i.i, %output.sroa.12.0.copyload.i
  store i64 %0, ptr %Y_plus_X, align 8, !alias.scope !4, !noalias !18
  %output.sroa.6.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %Y_plus_X, i64 8
  store i64 %2, ptr %output.sroa.6.0._0.sroa_idx.i, align 8, !alias.scope !4, !noalias !18
  %output.sroa.8.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %Y_plus_X, i64 16
  store i64 %4, ptr %output.sroa.8.0._0.sroa_idx.i, align 8, !alias.scope !4, !noalias !18
  %output.sroa.10.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %Y_plus_X, i64 24
  store i64 %6, ptr %output.sroa.10.0._0.sroa_idx.i, align 8, !alias.scope !4, !noalias !18
  %output.sroa.12.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %Y_plus_X, i64 32
  store i64 %8, ptr %output.sroa.12.0._0.sroa_idx.i, align 8, !alias.scope !4, !noalias !18
  call void @llvm.lifetime.start.p0(ptr nonnull %Y_minus_X)
  %_5.i = add i64 %output.sroa.0.0.copyload.i, 36028797018963664
  %_4.i = sub i64 %_5.i, %_5.i.i
  %_9.i = add i64 %output.sroa.6.0.copyload.i, 36028797018963952
  %_8.i = sub i64 %_9.i, %_5.1.i.i
  %_13.i = add i64 %output.sroa.8.0.copyload.i, 36028797018963952
  %_12.i = sub i64 %_13.i, %_5.2.i.i
  %_17.i = add i64 %output.sroa.10.0.copyload.i, 36028797018963952
  %_16.i = sub i64 %_17.i, %_5.3.i.i
  %_21.i = add i64 %output.sroa.12.0.copyload.i, 36028797018963952
  %_20.i = sub i64 %_21.i, %_5.4.i.i
  %_24.i = lshr i64 %_4.i, 51
  %_26.i = lshr i64 %_8.i, 51
  %_28.i = lshr i64 %_12.i, 51
  %_30.i = lshr i64 %_16.i, 51
  %_32.i = lshr i64 %_20.i, 51
  %9 = and i64 %_4.i, 2251799813685247
  %10 = and i64 %_8.i, 2251799813685247
  %11 = and i64 %_12.i, 2251799813685247
  %12 = and i64 %_16.i, 2251799813685247
  %13 = and i64 %_20.i, 2251799813685247
  %_34.i = mul nuw nsw i64 %_32.i, 19
  %14 = add nuw nsw i64 %_34.i, %9
  %15 = add nuw nsw i64 %10, %_24.i
  %16 = add nuw nsw i64 %11, %_26.i
  %17 = add nuw nsw i64 %12, %_28.i
  %18 = add nuw nsw i64 %13, %_30.i
  store i64 %14, ptr %Y_minus_X, align 8, !alias.scope !19, !noalias !22
  %_3.sroa.9.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %Y_minus_X, i64 8
  store i64 %15, ptr %_3.sroa.9.0._0.sroa_idx.i, align 8, !alias.scope !19, !noalias !22
  %_3.sroa.15.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %Y_minus_X, i64 16
  store i64 %16, ptr %_3.sroa.15.0._0.sroa_idx.i, align 8, !alias.scope !19, !noalias !22
  %_3.sroa.21.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %Y_minus_X, i64 24
  store i64 %17, ptr %_3.sroa.21.0._0.sroa_idx.i, align 8, !alias.scope !19, !noalias !22
  %_3.sroa.27.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %Y_minus_X, i64 32
  store i64 %18, ptr %_3.sroa.27.0._0.sroa_idx.i, align 8, !alias.scope !19, !noalias !22
  call void @llvm.lifetime.start.p0(ptr nonnull %PM)
  %_11 = getelementptr inbounds nuw i8, ptr %other, i64 40
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %PM, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %Y_plus_X, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_11) #4
  call void @llvm.lifetime.start.p0(ptr nonnull %MP)
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %MP, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %Y_minus_X, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %other) #4
  call void @llvm.lifetime.start.p0(ptr nonnull %Txy2d)
  %_16 = getelementptr inbounds nuw i8, ptr %self, i64 120
  %_17 = getelementptr inbounds nuw i8, ptr %other, i64 80
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %Txy2d, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_16, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_17) #4
  %_19 = getelementptr inbounds nuw i8, ptr %self, i64 80
  %output.sroa.0.0.copyload.i1 = load i64, ptr %_19, align 8, !alias.scope !25, !noalias !28
  %output.sroa.6.0.self.sroa_idx.i2 = getelementptr inbounds nuw i8, ptr %self, i64 88
  %output.sroa.6.0.copyload.i3 = load i64, ptr %output.sroa.6.0.self.sroa_idx.i2, align 8, !alias.scope !25, !noalias !28
  %output.sroa.8.0.self.sroa_idx.i4 = getelementptr inbounds nuw i8, ptr %self, i64 96
  %output.sroa.8.0.copyload.i5 = load i64, ptr %output.sroa.8.0.self.sroa_idx.i4, align 8, !alias.scope !25, !noalias !28
  %output.sroa.10.0.self.sroa_idx.i6 = getelementptr inbounds nuw i8, ptr %self, i64 104
  %output.sroa.10.0.copyload.i7 = load i64, ptr %output.sroa.10.0.self.sroa_idx.i6, align 8, !alias.scope !25, !noalias !28
  %output.sroa.12.0.self.sroa_idx.i8 = getelementptr inbounds nuw i8, ptr %self, i64 112
  %output.sroa.12.0.copyload.i9 = load i64, ptr %output.sroa.12.0.self.sroa_idx.i8, align 8, !alias.scope !25, !noalias !28
  %19 = shl i64 %output.sroa.0.0.copyload.i1, 1
  %20 = shl i64 %output.sroa.6.0.copyload.i3, 1
  %21 = shl i64 %output.sroa.8.0.copyload.i5, 1
  %22 = shl i64 %output.sroa.10.0.copyload.i7, 1
  %23 = shl i64 %output.sroa.12.0.copyload.i9, 1
  tail call void @llvm.experimental.noalias.scope.decl(metadata !31)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !34)
  %_6.i19 = load i64, ptr %PM, align 8, !alias.scope !31, !noalias !36, !noundef !17
  %_5.i20 = add i64 %_6.i19, 36028797018963664
  %_7.i21 = load i64, ptr %MP, align 8, !alias.scope !34, !noalias !38, !noundef !17
  %_4.i22 = sub i64 %_5.i20, %_7.i21
  %24 = getelementptr inbounds nuw i8, ptr %PM, i64 8
  %_10.i23 = load i64, ptr %24, align 8, !alias.scope !31, !noalias !36, !noundef !17
  %_9.i24 = add i64 %_10.i23, 36028797018963952
  %25 = getelementptr inbounds nuw i8, ptr %MP, i64 8
  %_11.i25 = load i64, ptr %25, align 8, !alias.scope !34, !noalias !38, !noundef !17
  %_8.i26 = sub i64 %_9.i24, %_11.i25
  %26 = getelementptr inbounds nuw i8, ptr %PM, i64 16
  %_14.i27 = load i64, ptr %26, align 8, !alias.scope !31, !noalias !36, !noundef !17
  %_13.i28 = add i64 %_14.i27, 36028797018963952
  %27 = getelementptr inbounds nuw i8, ptr %MP, i64 16
  %_15.i29 = load i64, ptr %27, align 8, !alias.scope !34, !noalias !38, !noundef !17
  %_12.i30 = sub i64 %_13.i28, %_15.i29
  %28 = getelementptr inbounds nuw i8, ptr %PM, i64 24
  %_18.i31 = load i64, ptr %28, align 8, !alias.scope !31, !noalias !36, !noundef !17
  %_17.i32 = add i64 %_18.i31, 36028797018963952
  %29 = getelementptr inbounds nuw i8, ptr %MP, i64 24
  %_19.i33 = load i64, ptr %29, align 8, !alias.scope !34, !noalias !38, !noundef !17
  %_16.i34 = sub i64 %_17.i32, %_19.i33
  %30 = getelementptr inbounds nuw i8, ptr %PM, i64 32
  %_22.i35 = load i64, ptr %30, align 8, !alias.scope !31, !noalias !36, !noundef !17
  %_21.i36 = add i64 %_22.i35, 36028797018963952
  %31 = getelementptr inbounds nuw i8, ptr %MP, i64 32
  %_23.i37 = load i64, ptr %31, align 8, !alias.scope !34, !noalias !38, !noundef !17
  %_20.i38 = sub i64 %_21.i36, %_23.i37
  %_24.i39 = lshr i64 %_4.i22, 51
  %_26.i40 = lshr i64 %_8.i26, 51
  %_28.i41 = lshr i64 %_12.i30, 51
  %_30.i42 = lshr i64 %_16.i34, 51
  %_32.i43 = lshr i64 %_20.i38, 51
  %32 = and i64 %_4.i22, 2251799813685247
  %33 = and i64 %_8.i26, 2251799813685247
  %34 = and i64 %_12.i30, 2251799813685247
  %35 = and i64 %_16.i34, 2251799813685247
  %36 = and i64 %_20.i38, 2251799813685247
  %_34.i44 = mul nuw nsw i64 %_32.i43, 19
  %37 = add nuw nsw i64 %_34.i44, %32
  %38 = add nuw nsw i64 %33, %_24.i39
  %39 = add nuw nsw i64 %34, %_26.i40
  %40 = add nuw nsw i64 %35, %_28.i41
  %41 = add nuw nsw i64 %36, %_30.i42
  %42 = add i64 %_7.i21, %_6.i19
  %43 = add i64 %_11.i25, %_10.i23
  %44 = add i64 %_15.i29, %_14.i27
  %45 = add i64 %_19.i33, %_18.i31
  %46 = add i64 %_23.i37, %_22.i35
  %_5.i68 = add i64 %19, 36028797018963664
  %_7.i69 = load i64, ptr %Txy2d, align 8, !alias.scope !39, !noalias !42, !noundef !17
  %_4.i70 = sub i64 %_5.i68, %_7.i69
  %_9.i72 = add i64 %20, 36028797018963952
  %47 = getelementptr inbounds nuw i8, ptr %Txy2d, i64 8
  %_11.i73 = load i64, ptr %47, align 8, !alias.scope !39, !noalias !42, !noundef !17
  %_8.i74 = sub i64 %_9.i72, %_11.i73
  %_13.i76 = add i64 %21, 36028797018963952
  %48 = getelementptr inbounds nuw i8, ptr %Txy2d, i64 16
  %_15.i77 = load i64, ptr %48, align 8, !alias.scope !39, !noalias !42, !noundef !17
  %_12.i78 = sub i64 %_13.i76, %_15.i77
  %_17.i80 = add i64 %22, 36028797018963952
  %49 = getelementptr inbounds nuw i8, ptr %Txy2d, i64 24
  %_19.i81 = load i64, ptr %49, align 8, !alias.scope !39, !noalias !42, !noundef !17
  %_16.i82 = sub i64 %_17.i80, %_19.i81
  %_21.i84 = add i64 %23, 36028797018963952
  %50 = getelementptr inbounds nuw i8, ptr %Txy2d, i64 32
  %_23.i85 = load i64, ptr %50, align 8, !alias.scope !39, !noalias !42, !noundef !17
  %_20.i86 = sub i64 %_21.i84, %_23.i85
  %_24.i87 = lshr i64 %_4.i70, 51
  %_26.i88 = lshr i64 %_8.i74, 51
  %_28.i89 = lshr i64 %_12.i78, 51
  %_30.i90 = lshr i64 %_16.i82, 51
  %_32.i91 = lshr i64 %_20.i86, 51
  %51 = and i64 %_4.i70, 2251799813685247
  %52 = and i64 %_8.i74, 2251799813685247
  %53 = and i64 %_12.i78, 2251799813685247
  %54 = and i64 %_16.i82, 2251799813685247
  %55 = and i64 %_20.i86, 2251799813685247
  %_34.i92 = mul nuw nsw i64 %_32.i91, 19
  %56 = add nuw nsw i64 %_34.i92, %51
  %57 = add nuw nsw i64 %52, %_24.i87
  %58 = add nuw nsw i64 %53, %_26.i88
  %59 = add nuw nsw i64 %54, %_28.i89
  %60 = add nuw nsw i64 %55, %_30.i90
  %61 = add i64 %_7.i69, %19
  %62 = add i64 %_11.i73, %20
  %63 = add i64 %_15.i77, %21
  %64 = add i64 %_19.i81, %22
  %65 = add i64 %_23.i85, %23
  store i64 %37, ptr %_0, align 8
  %_21.sroa.4.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 8
  store i64 %38, ptr %_21.sroa.4.0._0.sroa_idx, align 8
  %_21.sroa.5.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 16
  store i64 %39, ptr %_21.sroa.5.0._0.sroa_idx, align 8
  %_21.sroa.6.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 24
  store i64 %40, ptr %_21.sroa.6.0._0.sroa_idx, align 8
  %_21.sroa.7.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 32
  store i64 %41, ptr %_21.sroa.7.0._0.sroa_idx, align 8
  %66 = getelementptr inbounds nuw i8, ptr %_0, i64 40
  store i64 %42, ptr %66, align 8
  %_24.sroa.4.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 48
  store i64 %43, ptr %_24.sroa.4.0..sroa_idx, align 8
  %_24.sroa.5.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 56
  store i64 %44, ptr %_24.sroa.5.0..sroa_idx, align 8
  %_24.sroa.6.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 64
  store i64 %45, ptr %_24.sroa.6.0..sroa_idx, align 8
  %_24.sroa.7.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 72
  store i64 %46, ptr %_24.sroa.7.0..sroa_idx, align 8
  %67 = getelementptr inbounds nuw i8, ptr %_0, i64 80
  store i64 %56, ptr %67, align 8
  %_27.sroa.4.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 88
  store i64 %57, ptr %_27.sroa.4.0..sroa_idx, align 8
  %_27.sroa.5.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 96
  store i64 %58, ptr %_27.sroa.5.0..sroa_idx, align 8
  %_27.sroa.6.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 104
  store i64 %59, ptr %_27.sroa.6.0..sroa_idx, align 8
  %_27.sroa.7.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 112
  store i64 %60, ptr %_27.sroa.7.0..sroa_idx, align 8
  %68 = getelementptr inbounds nuw i8, ptr %_0, i64 120
  store i64 %61, ptr %68, align 8
  %_30.sroa.4.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 128
  store i64 %62, ptr %_30.sroa.4.0..sroa_idx, align 8
  %_30.sroa.5.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 136
  store i64 %63, ptr %_30.sroa.5.0..sroa_idx, align 8
  %_30.sroa.6.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 144
  store i64 %64, ptr %_30.sroa.6.0..sroa_idx, align 8
  %_30.sroa.7.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 152
  store i64 %65, ptr %_30.sroa.7.0..sroa_idx, align 8
  call void @llvm.lifetime.end.p0(ptr nonnull %Txy2d)
  call void @llvm.lifetime.end.p0(ptr nonnull %MP)
  call void @llvm.lifetime.end.p0(ptr nonnull %PM)
  call void @llvm.lifetime.end.p0(ptr nonnull %Y_minus_X)
  call void @llvm.lifetime.end.p0(ptr nonnull %Y_plus_X)
  ret void
}

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #2

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #2

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite)
declare void @llvm.experimental.noalias.scope.decl(metadata) #3

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #3 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite) }
attributes #4 = { nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{!5}
!5 = distinct !{!5, !6, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %_0"}
!6 = distinct !{!6, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add"}
!7 = !{!8}
!8 = distinct !{!8, !6, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %self"}
!9 = !{!10}
!10 = distinct !{!10, !6, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %_rhs"}
!11 = !{!5, !10}
!12 = !{!13, !10}
!13 = distinct !{!13, !14, !"_RNvXs0_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51INtNtNtCsgxBkk5gSRhY_4core3ops5arith9AddAssignRB16_E10add_assign: %_rhs"}
!14 = distinct !{!14, !"_RNvXs0_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51INtNtNtCsgxBkk5gSRhY_4core3ops5arith9AddAssignRB16_E10add_assign"}
!15 = !{!16, !5, !8}
!16 = distinct !{!16, !14, !"_RNvXs0_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51INtNtNtCsgxBkk5gSRhY_4core3ops5arith9AddAssignRB16_E10add_assign: %self"}
!17 = !{}
!18 = !{!8, !10}
!19 = !{!20}
!20 = distinct !{!20, !21, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub: %_0"}
!21 = distinct !{!21, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub"}
!22 = !{!23, !24}
!23 = distinct !{!23, !21, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub: %self"}
!24 = distinct !{!24, !21, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub: %_rhs"}
!25 = !{!26}
!26 = distinct !{!26, !27, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %self"}
!27 = distinct !{!27, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add"}
!28 = !{!29, !30}
!29 = distinct !{!29, !27, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %_0"}
!30 = distinct !{!30, !27, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %_rhs"}
!31 = !{!32}
!32 = distinct !{!32, !33, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub: %self"}
!33 = distinct !{!33, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub"}
!34 = !{!35}
!35 = distinct !{!35, !33, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub: %_rhs"}
!36 = !{!37, !35}
!37 = distinct !{!37, !33, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub: %_0"}
!38 = !{!37, !32}
!39 = !{!40}
!40 = distinct !{!40, !41, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub: %_rhs"}
!41 = distinct !{!41, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub"}
!42 = !{!43, !44}
!43 = distinct !{!43, !41, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub: %_0"}
!44 = distinct !{!44, !41, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub: %self"}
