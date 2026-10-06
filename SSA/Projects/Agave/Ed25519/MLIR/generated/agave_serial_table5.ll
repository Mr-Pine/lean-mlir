; ModuleID = '/home/nine/Documents/anza-code/.lmf-rir-ed25519/SSA/Projects/Agave/Ed25519/MLIR/generated/agave_serial_table5.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%"backend::serial::curve_models::ProjectiveNielsPoint" = type { %"backend::serial::u64::field::FieldElement51", %"backend::serial::u64::field::FieldElement51", %"backend::serial::u64::field::FieldElement51", %"backend::serial::u64::field::FieldElement51" }
%"backend::serial::u64::field::FieldElement51" = type { [5 x i64] }

@alloc_6e6f5bdc2dd4f9d83a28bc96071152e7 = internal unnamed_addr constant [40 x i8] c"Y\F1\B2&\94\9B\06\00z\DD*vPP\03\00R\80\03\C0D\CF\03\00wy@\C7\8Cs\06\00\FFm\C5\9Dm@\02\00", align 8

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
declare void @_RNvMsa_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_15ProjectivePoint6double(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([160 x i8]) align 8 captures(none) dereferenceable(160) initializes((0, 160)), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(120)) unnamed_addr #0

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
define void @_RNvXs0_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable5NtNtNtNtB7_7backend6serial12curve_models20ProjectiveNielsPointEINtNtCsgxBkk5gSRhY_4core7convert4FromRNtNtB7_7edwards12EdwardsPointE4from(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([1280 x i8]) align 8 captures(none) dereferenceable(1280) %_0, ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160) %A) unnamed_addr #0 {
start:
  %_5.i = alloca [120 x i8], align 8
  %_3.i4 = alloca [160 x i8], align 8
  %_11 = alloca [160 x i8], align 8
  %_9 = alloca [160 x i8], align 8
  %_7 = alloca [160 x i8], align 8
  %A2 = alloca [160 x i8], align 8
  %_3 = alloca [160 x i8], align 8
  %Ai = alloca [1280 x i8], align 8
  call void @llvm.lifetime.start.p0(ptr nonnull %_3)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !4)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !7)
  %_3.i = getelementptr inbounds nuw i8, ptr %A, i64 40
  tail call void @llvm.experimental.noalias.scope.decl(metadata !9)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !12)
  %output.sroa.0.0.copyload.i.i = load i64, ptr %_3.i, align 8, !alias.scope !14, !noalias !15
  %output.sroa.6.0.self.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %A, i64 48
  %output.sroa.6.0.copyload.i.i = load i64, ptr %output.sroa.6.0.self.sroa_idx.i.i, align 8, !alias.scope !14, !noalias !15
  %output.sroa.8.0.self.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %A, i64 56
  %output.sroa.8.0.copyload.i.i = load i64, ptr %output.sroa.8.0.self.sroa_idx.i.i, align 8, !alias.scope !14, !noalias !15
  %output.sroa.10.0.self.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %A, i64 64
  %output.sroa.10.0.copyload.i.i = load i64, ptr %output.sroa.10.0.self.sroa_idx.i.i, align 8, !alias.scope !14, !noalias !15
  %output.sroa.12.0.self.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %A, i64 72
  %output.sroa.12.0.copyload.i.i = load i64, ptr %output.sroa.12.0.self.sroa_idx.i.i, align 8, !alias.scope !14, !noalias !15
  %_5.i.i.i = load i64, ptr %A, align 8, !alias.scope !17, !noalias !20, !noundef !22
  %0 = add i64 %_5.i.i.i, %output.sroa.0.0.copyload.i.i
  %1 = getelementptr inbounds nuw i8, ptr %A, i64 8
  %_5.1.i.i.i = load i64, ptr %1, align 8, !alias.scope !17, !noalias !20, !noundef !22
  %2 = add i64 %_5.1.i.i.i, %output.sroa.6.0.copyload.i.i
  %3 = getelementptr inbounds nuw i8, ptr %A, i64 16
  %_5.2.i.i.i = load i64, ptr %3, align 8, !alias.scope !17, !noalias !20, !noundef !22
  %4 = add i64 %_5.2.i.i.i, %output.sroa.8.0.copyload.i.i
  %5 = getelementptr inbounds nuw i8, ptr %A, i64 24
  %_5.3.i.i.i = load i64, ptr %5, align 8, !alias.scope !17, !noalias !20, !noundef !22
  %6 = add i64 %_5.3.i.i.i, %output.sroa.10.0.copyload.i.i
  %7 = getelementptr inbounds nuw i8, ptr %A, i64 32
  %_5.4.i.i.i = load i64, ptr %7, align 8, !alias.scope !17, !noalias !20, !noundef !22
  %8 = add i64 %_5.4.i.i.i, %output.sroa.12.0.copyload.i.i
  %_5.i.i = add i64 %output.sroa.0.0.copyload.i.i, 36028797018963664
  %_4.i.i = sub i64 %_5.i.i, %_5.i.i.i
  %_9.i.i = add i64 %output.sroa.6.0.copyload.i.i, 36028797018963952
  %_8.i.i = sub i64 %_9.i.i, %_5.1.i.i.i
  %_13.i.i = add i64 %output.sroa.8.0.copyload.i.i, 36028797018963952
  %_12.i.i = sub i64 %_13.i.i, %_5.2.i.i.i
  %_17.i.i = add i64 %output.sroa.10.0.copyload.i.i, 36028797018963952
  %_16.i.i = sub i64 %_17.i.i, %_5.3.i.i.i
  %_21.i.i = add i64 %output.sroa.12.0.copyload.i.i, 36028797018963952
  %_20.i.i = sub i64 %_21.i.i, %_5.4.i.i.i
  %_24.i.i = lshr i64 %_4.i.i, 51
  %_26.i.i = lshr i64 %_8.i.i, 51
  %_28.i.i = lshr i64 %_12.i.i, 51
  %_30.i.i = lshr i64 %_16.i.i, 51
  %_32.i.i = lshr i64 %_20.i.i, 51
  %9 = and i64 %_4.i.i, 2251799813685247
  %10 = and i64 %_8.i.i, 2251799813685247
  %11 = and i64 %_12.i.i, 2251799813685247
  %12 = and i64 %_16.i.i, 2251799813685247
  %13 = and i64 %_20.i.i, 2251799813685247
  %_34.i.i = mul nuw nsw i64 %_32.i.i, 19
  %14 = add nuw nsw i64 %_34.i.i, %9
  %15 = add nuw nsw i64 %10, %_24.i.i
  %16 = add nuw nsw i64 %11, %_26.i.i
  %17 = add nuw nsw i64 %12, %_28.i.i
  %18 = add nuw nsw i64 %13, %_30.i.i
  %19 = getelementptr inbounds nuw i8, ptr %A, i64 80
  %20 = getelementptr inbounds nuw i8, ptr %_3, i64 80
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %20, ptr noundef nonnull readonly align 8 dereferenceable(40) %19, i64 40, i1 false), !alias.scope !23
  %_10.i = getelementptr inbounds nuw i8, ptr %A, i64 120
  %21 = getelementptr inbounds nuw i8, ptr %_3, i64 120
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %21, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_10.i, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(40) @alloc_6e6f5bdc2dd4f9d83a28bc96071152e7) #6
  store i64 %0, ptr %_3, align 8, !alias.scope !4, !noalias !7
  %_2.sroa.4.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %_3, i64 8
  store i64 %2, ptr %_2.sroa.4.0._0.sroa_idx.i, align 8, !alias.scope !4, !noalias !7
  %_2.sroa.5.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %_3, i64 16
  store i64 %4, ptr %_2.sroa.5.0._0.sroa_idx.i, align 8, !alias.scope !4, !noalias !7
  %_2.sroa.6.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %_3, i64 24
  store i64 %6, ptr %_2.sroa.6.0._0.sroa_idx.i, align 8, !alias.scope !4, !noalias !7
  %_2.sroa.7.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %_3, i64 32
  store i64 %8, ptr %_2.sroa.7.0._0.sroa_idx.i, align 8, !alias.scope !4, !noalias !7
  %22 = getelementptr inbounds nuw i8, ptr %_3, i64 40
  store i64 %14, ptr %22, align 8, !alias.scope !4, !noalias !7
  %_5.sroa.4.0..sroa_idx.i = getelementptr inbounds nuw i8, ptr %_3, i64 48
  store i64 %15, ptr %_5.sroa.4.0..sroa_idx.i, align 8, !alias.scope !4, !noalias !7
  %_5.sroa.5.0..sroa_idx.i = getelementptr inbounds nuw i8, ptr %_3, i64 56
  store i64 %16, ptr %_5.sroa.5.0..sroa_idx.i, align 8, !alias.scope !4, !noalias !7
  %_5.sroa.6.0..sroa_idx.i = getelementptr inbounds nuw i8, ptr %_3, i64 64
  store i64 %17, ptr %_5.sroa.6.0..sroa_idx.i, align 8, !alias.scope !4, !noalias !7
  %_5.sroa.7.0..sroa_idx.i = getelementptr inbounds nuw i8, ptr %_3, i64 72
  store i64 %18, ptr %_5.sroa.7.0..sroa_idx.i, align 8, !alias.scope !4, !noalias !7
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(160) %Ai, ptr noundef nonnull align 8 dereferenceable(160) %_3, i64 160, i1 false)
  %23 = getelementptr inbounds nuw i8, ptr %Ai, i64 160
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(160) %23, ptr noundef nonnull align 8 dereferenceable(160) %_3, i64 160, i1 false)
  %24 = getelementptr inbounds nuw i8, ptr %Ai, i64 320
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(160) %24, ptr noundef nonnull align 8 dereferenceable(160) %_3, i64 160, i1 false)
  %25 = getelementptr inbounds nuw i8, ptr %Ai, i64 480
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(160) %25, ptr noundef nonnull align 8 dereferenceable(160) %_3, i64 160, i1 false)
  %26 = getelementptr inbounds nuw i8, ptr %Ai, i64 640
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(160) %26, ptr noundef nonnull align 8 dereferenceable(160) %_3, i64 160, i1 false)
  %27 = getelementptr inbounds nuw i8, ptr %Ai, i64 800
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(160) %27, ptr noundef nonnull align 8 dereferenceable(160) %_3, i64 160, i1 false)
  %28 = getelementptr inbounds nuw i8, ptr %Ai, i64 960
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(160) %28, ptr noundef nonnull align 8 dereferenceable(160) %_3, i64 160, i1 false)
  %29 = getelementptr inbounds nuw i8, ptr %Ai, i64 1120
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(160) %29, ptr noundef nonnull align 8 dereferenceable(160) %_3, i64 160, i1 false)
  call void @llvm.lifetime.end.p0(ptr nonnull %_3)
  call void @llvm.lifetime.start.p0(ptr nonnull %A2)
  call void @llvm.lifetime.start.p0(ptr nonnull %_3.i4), !noalias !24
  call void @llvm.lifetime.start.p0(ptr nonnull %_5.i), !noalias !24
  %30 = getelementptr inbounds nuw i8, ptr %_5.i, i64 40
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %30, ptr noundef nonnull readonly align 8 dereferenceable(40) %_3.i, i64 40, i1 false), !noalias !28
  %31 = getelementptr inbounds nuw i8, ptr %_5.i, i64 80
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %31, ptr noundef nonnull readonly align 8 dereferenceable(40) %19, i64 40, i1 false), !noalias !28
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %_5.i, ptr noundef nonnull readonly align 8 dereferenceable(160) %A, i64 40, i1 false), !noalias !28
  call void @_RNvMsa_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_15ProjectivePoint6double(ptr noalias nofree noundef nonnull sret([160 x i8]) align 8 captures(none) dereferenceable(160) %_3.i4, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(120) %_5.i) #6, !noalias !24
  %_4.i.i5 = getelementptr inbounds nuw i8, ptr %_3.i4, i64 120
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(160) %A2, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_3.i4, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_4.i.i5) #6, !alias.scope !29, !noalias !33
  %_6.i.i = getelementptr inbounds nuw i8, ptr %_3.i4, i64 40
  %_7.i.i = getelementptr inbounds nuw i8, ptr %_3.i4, i64 80
  %32 = getelementptr inbounds nuw i8, ptr %A2, i64 40
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %32, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_6.i.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_7.i.i) #6, !alias.scope !29, !noalias !33
  %33 = getelementptr inbounds nuw i8, ptr %A2, i64 80
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %33, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_7.i.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_4.i.i5) #6, !alias.scope !29, !noalias !33
  %34 = getelementptr inbounds nuw i8, ptr %A2, i64 120
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %34, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_3.i4, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_6.i.i) #6, !alias.scope !29, !noalias !33
  call void @llvm.lifetime.end.p0(ptr nonnull %_5.i), !noalias !24
  call void @llvm.lifetime.end.p0(ptr nonnull %_3.i4), !noalias !24
  %_4.i = getelementptr inbounds nuw i8, ptr %_11, i64 120
  %_6.i = getelementptr inbounds nuw i8, ptr %_11, i64 40
  %_7.i = getelementptr inbounds nuw i8, ptr %_11, i64 80
  %35 = getelementptr inbounds nuw i8, ptr %_9, i64 40
  %36 = getelementptr inbounds nuw i8, ptr %_9, i64 80
  %37 = getelementptr inbounds nuw i8, ptr %_9, i64 120
  %output.sroa.6.0.self.sroa_idx.i.i8 = getelementptr inbounds nuw i8, ptr %_9, i64 48
  %output.sroa.8.0.self.sroa_idx.i.i10 = getelementptr inbounds nuw i8, ptr %_9, i64 56
  %output.sroa.10.0.self.sroa_idx.i.i12 = getelementptr inbounds nuw i8, ptr %_9, i64 64
  %output.sroa.12.0.self.sroa_idx.i.i14 = getelementptr inbounds nuw i8, ptr %_9, i64 72
  %38 = getelementptr inbounds nuw i8, ptr %_9, i64 8
  %39 = getelementptr inbounds nuw i8, ptr %_9, i64 16
  %40 = getelementptr inbounds nuw i8, ptr %_9, i64 24
  %41 = getelementptr inbounds nuw i8, ptr %_9, i64 32
  %42 = getelementptr inbounds nuw i8, ptr %_7, i64 80
  %43 = getelementptr inbounds nuw i8, ptr %_7, i64 120
  %_2.sroa.4.0._0.sroa_idx.i38 = getelementptr inbounds nuw i8, ptr %_7, i64 8
  %_2.sroa.5.0._0.sroa_idx.i39 = getelementptr inbounds nuw i8, ptr %_7, i64 16
  %_2.sroa.6.0._0.sroa_idx.i40 = getelementptr inbounds nuw i8, ptr %_7, i64 24
  %_2.sroa.7.0._0.sroa_idx.i41 = getelementptr inbounds nuw i8, ptr %_7, i64 32
  %44 = getelementptr inbounds nuw i8, ptr %_7, i64 40
  %_5.sroa.4.0..sroa_idx.i42 = getelementptr inbounds nuw i8, ptr %_7, i64 48
  %_5.sroa.5.0..sroa_idx.i43 = getelementptr inbounds nuw i8, ptr %_7, i64 56
  %_5.sroa.6.0..sroa_idx.i44 = getelementptr inbounds nuw i8, ptr %_7, i64 64
  %_5.sroa.7.0..sroa_idx.i45 = getelementptr inbounds nuw i8, ptr %_7, i64 72
  br label %bb9

bb10:                                             ; preds = %bb9
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(1280) %_0, ptr noundef nonnull align 8 dereferenceable(1280) %Ai, i64 1280, i1 false)
  call void @llvm.lifetime.end.p0(ptr nonnull %A2)
  ret void

bb9:                                              ; preds = %bb9, %start
  %iter.sroa.0.046 = phi i64 [ 0, %start ], [ %45, %bb9 ]
  %45 = add nuw nsw i64 %iter.sroa.0.046, 1
  call void @llvm.lifetime.start.p0(ptr nonnull %_7)
  call void @llvm.lifetime.start.p0(ptr nonnull %_9)
  call void @llvm.lifetime.start.p0(ptr nonnull %_11)
  %_13 = getelementptr inbounds nuw %"backend::serial::curve_models::ProjectiveNielsPoint", ptr %Ai, i64 %iter.sroa.0.046
  call void @_RNvXsb_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB5_20ProjectiveNielsPointE3add(ptr noalias nofree noundef nonnull sret([160 x i8]) align 8 captures(none) dereferenceable(160) %_11, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %A2, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_13) #6
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(160) %_9, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_11, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_4.i) #6, !alias.scope !34
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %35, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_6.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_7.i) #6, !alias.scope !34
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %36, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_7.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_4.i) #6, !alias.scope !34
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %37, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_11, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_6.i) #6, !alias.scope !34
  tail call void @llvm.experimental.noalias.scope.decl(metadata !38)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !41)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !43)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !46)
  %output.sroa.0.0.copyload.i.i7 = load i64, ptr %35, align 8, !alias.scope !48, !noalias !49
  %output.sroa.6.0.copyload.i.i9 = load i64, ptr %output.sroa.6.0.self.sroa_idx.i.i8, align 8, !alias.scope !48, !noalias !49
  %output.sroa.8.0.copyload.i.i11 = load i64, ptr %output.sroa.8.0.self.sroa_idx.i.i10, align 8, !alias.scope !48, !noalias !49
  %output.sroa.10.0.copyload.i.i13 = load i64, ptr %output.sroa.10.0.self.sroa_idx.i.i12, align 8, !alias.scope !48, !noalias !49
  %output.sroa.12.0.copyload.i.i15 = load i64, ptr %output.sroa.12.0.self.sroa_idx.i.i14, align 8, !alias.scope !48, !noalias !49
  %_5.i.i.i16 = load i64, ptr %_9, align 8, !alias.scope !51, !noalias !54, !noundef !22
  %46 = add i64 %_5.i.i.i16, %output.sroa.0.0.copyload.i.i7
  %_5.1.i.i.i17 = load i64, ptr %38, align 8, !alias.scope !51, !noalias !54, !noundef !22
  %47 = add i64 %_5.1.i.i.i17, %output.sroa.6.0.copyload.i.i9
  %_5.2.i.i.i18 = load i64, ptr %39, align 8, !alias.scope !51, !noalias !54, !noundef !22
  %48 = add i64 %_5.2.i.i.i18, %output.sroa.8.0.copyload.i.i11
  %_5.3.i.i.i19 = load i64, ptr %40, align 8, !alias.scope !51, !noalias !54, !noundef !22
  %49 = add i64 %_5.3.i.i.i19, %output.sroa.10.0.copyload.i.i13
  %_5.4.i.i.i20 = load i64, ptr %41, align 8, !alias.scope !51, !noalias !54, !noundef !22
  %50 = add i64 %_5.4.i.i.i20, %output.sroa.12.0.copyload.i.i15
  %_5.i.i21 = add i64 %output.sroa.0.0.copyload.i.i7, 36028797018963664
  %_4.i.i22 = sub i64 %_5.i.i21, %_5.i.i.i16
  %_9.i.i23 = add i64 %output.sroa.6.0.copyload.i.i9, 36028797018963952
  %_8.i.i24 = sub i64 %_9.i.i23, %_5.1.i.i.i17
  %_13.i.i25 = add i64 %output.sroa.8.0.copyload.i.i11, 36028797018963952
  %_12.i.i26 = sub i64 %_13.i.i25, %_5.2.i.i.i18
  %_17.i.i27 = add i64 %output.sroa.10.0.copyload.i.i13, 36028797018963952
  %_16.i.i28 = sub i64 %_17.i.i27, %_5.3.i.i.i19
  %_21.i.i29 = add i64 %output.sroa.12.0.copyload.i.i15, 36028797018963952
  %_20.i.i30 = sub i64 %_21.i.i29, %_5.4.i.i.i20
  %_24.i.i31 = lshr i64 %_4.i.i22, 51
  %_26.i.i32 = lshr i64 %_8.i.i24, 51
  %_28.i.i33 = lshr i64 %_12.i.i26, 51
  %_30.i.i34 = lshr i64 %_16.i.i28, 51
  %_32.i.i35 = lshr i64 %_20.i.i30, 51
  %51 = and i64 %_4.i.i22, 2251799813685247
  %52 = and i64 %_8.i.i24, 2251799813685247
  %53 = and i64 %_12.i.i26, 2251799813685247
  %54 = and i64 %_16.i.i28, 2251799813685247
  %55 = and i64 %_20.i.i30, 2251799813685247
  %_34.i.i36 = mul nuw nsw i64 %_32.i.i35, 19
  %56 = add nuw nsw i64 %_34.i.i36, %51
  %57 = add nuw nsw i64 %52, %_24.i.i31
  %58 = add nuw nsw i64 %53, %_26.i.i32
  %59 = add nuw nsw i64 %54, %_28.i.i33
  %60 = add nuw nsw i64 %55, %_30.i.i34
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %42, ptr noundef nonnull readonly align 8 dereferenceable(40) %36, i64 40, i1 false), !alias.scope !56
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %43, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %37, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(40) @alloc_6e6f5bdc2dd4f9d83a28bc96071152e7) #6
  store i64 %46, ptr %_7, align 8, !alias.scope !38, !noalias !41
  store i64 %47, ptr %_2.sroa.4.0._0.sroa_idx.i38, align 8, !alias.scope !38, !noalias !41
  store i64 %48, ptr %_2.sroa.5.0._0.sroa_idx.i39, align 8, !alias.scope !38, !noalias !41
  store i64 %49, ptr %_2.sroa.6.0._0.sroa_idx.i40, align 8, !alias.scope !38, !noalias !41
  store i64 %50, ptr %_2.sroa.7.0._0.sroa_idx.i41, align 8, !alias.scope !38, !noalias !41
  store i64 %56, ptr %44, align 8, !alias.scope !38, !noalias !41
  store i64 %57, ptr %_5.sroa.4.0..sroa_idx.i42, align 8, !alias.scope !38, !noalias !41
  store i64 %58, ptr %_5.sroa.5.0..sroa_idx.i43, align 8, !alias.scope !38, !noalias !41
  store i64 %59, ptr %_5.sroa.6.0..sroa_idx.i44, align 8, !alias.scope !38, !noalias !41
  store i64 %60, ptr %_5.sroa.7.0..sroa_idx.i45, align 8, !alias.scope !38, !noalias !41
  %61 = getelementptr inbounds nuw %"backend::serial::curve_models::ProjectiveNielsPoint", ptr %Ai, i64 %45
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(160) %61, ptr noundef nonnull align 8 dereferenceable(160) %_7, i64 160, i1 false)
  call void @llvm.lifetime.end.p0(ptr nonnull %_7)
  call void @llvm.lifetime.end.p0(ptr nonnull %_11)
  call void @llvm.lifetime.end.p0(ptr nonnull %_9)
  %exitcond.not = icmp eq i64 %45, 7
  br i1 %exitcond.not, label %bb10, label %bb9
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
declare void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([40 x i8]) align 8 captures(none) dereferenceable(40) initializes((0, 40)), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40)) unnamed_addr #1

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
declare void @_RNvXsb_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB5_20ProjectiveNielsPointE3add(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([160 x i8]) align 8 captures(none) dereferenceable(160) initializes((0, 160)), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160)) unnamed_addr #2

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #3

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #4

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #3

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite)
declare void @llvm.experimental.noalias.scope.decl(metadata) #5

attributes #0 = { nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #4 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #5 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite) }
attributes #6 = { nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{!5}
!5 = distinct !{!5, !6, !"_RNvMsg_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint19as_projective_niels: %_0"}
!6 = distinct !{!6, !"_RNvMsg_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint19as_projective_niels"}
!7 = !{!8}
!8 = distinct !{!8, !6, !"_RNvMsg_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint19as_projective_niels: %self"}
!9 = !{!10}
!10 = distinct !{!10, !11, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %self"}
!11 = distinct !{!11, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add"}
!12 = !{!13}
!13 = distinct !{!13, !11, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %_rhs"}
!14 = !{!10, !8}
!15 = !{!16, !13, !5}
!16 = distinct !{!16, !11, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %_0"}
!17 = !{!18, !13, !8}
!18 = distinct !{!18, !19, !"_RNvXs0_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51INtNtNtCsgxBkk5gSRhY_4core3ops5arith9AddAssignRB16_E10add_assign: %_rhs"}
!19 = distinct !{!19, !"_RNvXs0_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51INtNtNtCsgxBkk5gSRhY_4core3ops5arith9AddAssignRB16_E10add_assign"}
!20 = !{!21, !16, !10, !5}
!21 = distinct !{!21, !19, !"_RNvXs0_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51INtNtNtCsgxBkk5gSRhY_4core3ops5arith9AddAssignRB16_E10add_assign: %self"}
!22 = !{}
!23 = !{!5, !8}
!24 = !{!25, !27}
!25 = distinct !{!25, !26, !"_RNvMsh_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint6double: %_0"}
!26 = distinct !{!26, !"_RNvMsh_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint6double"}
!27 = distinct !{!27, !26, !"_RNvMsh_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint6double: %self"}
!28 = !{!25}
!29 = !{!30, !32}
!30 = distinct !{!30, !31, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended: %_0"}
!31 = distinct !{!31, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended"}
!32 = distinct !{!32, !31, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended: %self"}
!33 = !{!27}
!34 = !{!35, !37}
!35 = distinct !{!35, !36, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended: %_0"}
!36 = distinct !{!36, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended"}
!37 = distinct !{!37, !36, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended: %self"}
!38 = !{!39}
!39 = distinct !{!39, !40, !"_RNvMsg_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint19as_projective_niels: %_0"}
!40 = distinct !{!40, !"_RNvMsg_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint19as_projective_niels"}
!41 = !{!42}
!42 = distinct !{!42, !40, !"_RNvMsg_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint19as_projective_niels: %self"}
!43 = !{!44}
!44 = distinct !{!44, !45, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %self"}
!45 = distinct !{!45, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add"}
!46 = !{!47}
!47 = distinct !{!47, !45, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %_rhs"}
!48 = !{!44, !42}
!49 = !{!50, !47, !39}
!50 = distinct !{!50, !45, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %_0"}
!51 = !{!52, !47, !42}
!52 = distinct !{!52, !53, !"_RNvXs0_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51INtNtNtCsgxBkk5gSRhY_4core3ops5arith9AddAssignRB16_E10add_assign: %_rhs"}
!53 = distinct !{!53, !"_RNvXs0_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51INtNtNtCsgxBkk5gSRhY_4core3ops5arith9AddAssignRB16_E10add_assign"}
!54 = !{!55, !50, !44, !39}
!55 = distinct !{!55, !53, !"_RNvXs0_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51INtNtNtCsgxBkk5gSRhY_4core3ops5arith9AddAssignRB16_E10add_assign: %self"}
!56 = !{!39, !42}
