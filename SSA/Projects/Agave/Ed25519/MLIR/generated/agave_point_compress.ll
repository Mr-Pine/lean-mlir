; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_point_compress.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree noinline norecurse nounwind nonlazybind willreturn memory(inaccessiblemem: readwrite) uwtable
declare noundef i8 @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519(i8 noundef) unnamed_addr #0

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable
declare hidden fastcc void @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement518pow22501(ptr dead_on_unwind noalias nofree noundef nonnull writable writeonly align 8 captures(none) dereferenceable(80) initializes((0, 80)), ptr noalias nofree noundef nonnull readonly align 8 captures(none) dereferenceable(40)) unnamed_addr #1

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable
declare void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([40 x i8]) align 8 captures(none) dereferenceable(40), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40), i32 noundef) unnamed_addr #1

; Function Attrs: nofree norecurse nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
define void @_RNvMsg_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint8compress(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([32 x i8]) align 1 captures(none) dereferenceable(32) initializes((0, 32)) %_0, ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160) %self) unnamed_addr #2 {
start:
  %t20.i.i = alloca [40 x i8], align 8
  %_4.i.i = alloca [80 x i8], align 8
  %t3.i.i = alloca [40 x i8], align 8
  %t19.i.i = alloca [40 x i8], align 8
  %recip.i = alloca [40 x i8], align 8
  %_2 = alloca [80 x i8], align 8
  call void @llvm.lifetime.start.p0(ptr nonnull %_2)
  call void @llvm.lifetime.start.p0(ptr nonnull %recip.i), !noalias !4
  %_3.i = getelementptr inbounds nuw i8, ptr %self, i64 80
  call void @llvm.lifetime.start.p0(ptr nonnull %_4.i.i), !noalias !8
  call fastcc void @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement518pow22501(ptr noalias nofree noundef align 8 captures(none) dereferenceable(80) %_4.i.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_3.i) #6, !noalias !12
  call void @llvm.lifetime.start.p0(ptr nonnull %t19.i.i), !noalias !8
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %t19.i.i, ptr noundef nonnull align 8 dereferenceable(40) %_4.i.i, i64 40, i1 false), !noalias !8
  call void @llvm.lifetime.start.p0(ptr nonnull %t3.i.i), !noalias !8
  %0 = getelementptr inbounds nuw i8, ptr %_4.i.i, i64 40
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %t3.i.i, ptr noundef nonnull align 8 dereferenceable(40) %0, i64 40, i1 false), !noalias !8
  call void @llvm.lifetime.end.p0(ptr nonnull %_4.i.i), !noalias !8
  call void @llvm.lifetime.start.p0(ptr nonnull %t20.i.i), !noalias !8
  call void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %t20.i.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %t19.i.i, i32 noundef 5) #6, !noalias !8
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %recip.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %t20.i.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %t3.i.i) #6, !noalias !13
  call void @llvm.lifetime.end.p0(ptr nonnull %t20.i.i), !noalias !8
  call void @llvm.lifetime.end.p0(ptr nonnull %t3.i.i), !noalias !8
  call void @llvm.lifetime.end.p0(ptr nonnull %t19.i.i), !noalias !8
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(80) %_2, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %self, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %recip.i) #6
  %_8.i = getelementptr inbounds nuw i8, ptr %self, i64 40
  %1 = getelementptr inbounds nuw i8, ptr %_2, i64 40
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %1, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_8.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %recip.i) #6
  call void @llvm.lifetime.end.p0(ptr nonnull %recip.i), !noalias !4
  %_5.sroa.0.0.copyload = load i64, ptr %1, align 8
  %_5.sroa.4.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_2, i64 48
  %_5.sroa.4.0.copyload = load i64, ptr %_5.sroa.4.0..sroa_idx, align 8
  %_5.sroa.5.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_2, i64 56
  %_5.sroa.5.0.copyload = load i64, ptr %_5.sroa.5.0..sroa_idx, align 8
  %_5.sroa.6.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_2, i64 64
  %_5.sroa.6.0.copyload = load i64, ptr %_5.sroa.6.0..sroa_idx, align 8
  %_5.sroa.7.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_2, i64 72
  %_5.sroa.7.0.copyload = load i64, ptr %_5.sroa.7.0..sroa_idx, align 8
  %_98.i = lshr i64 %_5.sroa.0.0.copyload, 51
  %_100.i = lshr i64 %_5.sroa.4.0.copyload, 51
  %_102.i = lshr i64 %_5.sroa.5.0.copyload, 51
  %_104.i = lshr i64 %_5.sroa.6.0.copyload, 51
  %_106.i = lshr i64 %_5.sroa.7.0.copyload, 51
  %2 = and i64 %_5.sroa.0.0.copyload, 2251799813685247
  %3 = and i64 %_5.sroa.4.0.copyload, 2251799813685247
  %4 = and i64 %_5.sroa.5.0.copyload, 2251799813685247
  %5 = and i64 %_5.sroa.6.0.copyload, 2251799813685247
  %6 = and i64 %_5.sroa.7.0.copyload, 2251799813685247
  %_108.i = mul nuw nsw i64 %_106.i, 19
  %7 = add nuw nsw i64 %_108.i, %2
  %8 = add nuw nsw i64 %3, %_98.i
  %9 = add nuw nsw i64 %4, %_100.i
  %10 = add nuw nsw i64 %5, %_102.i
  %11 = add nuw nsw i64 %6, %_104.i
  %_4.i = add nuw nsw i64 %7, 19
  %12 = lshr i64 %_4.i, 51
  %_6.i = add nuw nsw i64 %12, %8
  %13 = lshr i64 %_6.i, 51
  %_8.i1 = add nuw nsw i64 %13, %9
  %14 = lshr i64 %_8.i1, 51
  %_10.i = add nuw nsw i64 %14, %10
  %15 = lshr i64 %_10.i, 51
  %_12.i = add nuw nsw i64 %15, %11
  %16 = lshr i64 %_12.i, 51
  %_14.i = mul nuw nsw i64 %16, 19
  %17 = add nuw nsw i64 %_14.i, %7
  %_15.i = lshr i64 %17, 51
  %18 = add nuw nsw i64 %_15.i, %8
  %_17.i = lshr i64 %18, 51
  %19 = add nuw nsw i64 %_17.i, %9
  %20 = and i64 %18, 2251799813685247
  %_19.i = lshr i64 %19, 51
  %21 = add nuw nsw i64 %_19.i, %10
  %22 = and i64 %19, 2251799813685247
  %_21.i = lshr i64 %21, 51
  %23 = add nuw nsw i64 %_21.i, %11
  %24 = and i64 %21, 2251799813685247
  %25 = and i64 %23, 2251799813685247
  %26 = trunc i64 %17 to i8
  %_24.i = lshr i64 %17, 8
  %27 = trunc i64 %_24.i to i8
  %_26.i = lshr i64 %17, 16
  %28 = trunc i64 %_26.i to i8
  %_28.i = lshr i64 %17, 24
  %29 = trunc i64 %_28.i to i8
  %_30.i = lshr i64 %17, 32
  %30 = trunc i64 %_30.i to i8
  %_32.i = lshr i64 %17, 40
  %31 = trunc i64 %_32.i to i8
  %32 = lshr i64 %17, 48
  %_35.i = and i64 %32, 7
  %_37.i = shl nuw nsw i64 %20, 3
  %_34.i = or disjoint i64 %_37.i, %_35.i
  %33 = trunc i64 %_34.i to i8
  %_39.i = lshr i64 %18, 5
  %34 = trunc i64 %_39.i to i8
  %_41.i = lshr i64 %18, 13
  %35 = trunc i64 %_41.i to i8
  %_43.i = lshr i64 %18, 21
  %36 = trunc i64 %_43.i to i8
  %_45.i = lshr i64 %18, 29
  %37 = trunc i64 %_45.i to i8
  %_47.i = lshr i64 %18, 37
  %38 = trunc i64 %_47.i to i8
  %_50.i = lshr i64 %20, 45
  %_52.i = shl nuw nsw i64 %22, 6
  %_49.i = or disjoint i64 %_52.i, %_50.i
  %39 = trunc i64 %_49.i to i8
  %_54.i = lshr i64 %19, 2
  %40 = trunc i64 %_54.i to i8
  %_56.i = lshr i64 %19, 10
  %41 = trunc i64 %_56.i to i8
  %_58.i = lshr i64 %19, 18
  %42 = trunc i64 %_58.i to i8
  %_60.i = lshr i64 %19, 26
  %43 = trunc i64 %_60.i to i8
  %_62.i = lshr i64 %19, 34
  %44 = trunc i64 %_62.i to i8
  %_64.i = lshr i64 %19, 42
  %45 = trunc i64 %_64.i to i8
  %_67.i = lshr i64 %22, 50
  %_69.i = shl nuw nsw i64 %24, 1
  %_66.i = or disjoint i64 %_69.i, %_67.i
  %46 = trunc i64 %_66.i to i8
  %_71.i = lshr i64 %21, 7
  %47 = trunc i64 %_71.i to i8
  %_73.i = lshr i64 %21, 15
  %48 = trunc i64 %_73.i to i8
  %_75.i = lshr i64 %21, 23
  %49 = trunc i64 %_75.i to i8
  %_77.i = lshr i64 %21, 31
  %50 = trunc i64 %_77.i to i8
  %_79.i = lshr i64 %21, 39
  %51 = trunc i64 %_79.i to i8
  %_82.i = lshr i64 %24, 47
  %_84.i = shl nuw nsw i64 %25, 4
  %_81.i = or disjoint i64 %_84.i, %_82.i
  %52 = trunc i64 %_81.i to i8
  %_86.i = lshr i64 %23, 4
  %53 = trunc i64 %_86.i to i8
  %_88.i = lshr i64 %23, 12
  %54 = trunc i64 %_88.i to i8
  %_90.i = lshr i64 %23, 20
  %55 = trunc i64 %_90.i to i8
  %_92.i = lshr i64 %23, 28
  %56 = trunc i64 %_92.i to i8
  %_94.i = lshr i64 %23, 36
  %57 = trunc i64 %_94.i to i8
  %_96.i = lshr i64 %25, 44
  %58 = trunc nuw nsw i64 %_96.i to i8
  %limbs.sroa.0.0.copyload.i4 = load i64, ptr %_2, align 8, !alias.scope !14, !noalias !17
  %limbs.sroa.19.0.self.sroa_idx.i5 = getelementptr inbounds nuw i8, ptr %_2, i64 8
  %limbs.sroa.19.0.copyload.i6 = load i64, ptr %limbs.sroa.19.0.self.sroa_idx.i5, align 8, !alias.scope !14, !noalias !17
  %limbs.sroa.37.0.self.sroa_idx.i7 = getelementptr inbounds nuw i8, ptr %_2, i64 16
  %limbs.sroa.37.0.copyload.i8 = load i64, ptr %limbs.sroa.37.0.self.sroa_idx.i7, align 8, !alias.scope !14, !noalias !17
  %limbs.sroa.56.0.self.sroa_idx.i9 = getelementptr inbounds nuw i8, ptr %_2, i64 24
  %limbs.sroa.56.0.copyload.i10 = load i64, ptr %limbs.sroa.56.0.self.sroa_idx.i9, align 8, !alias.scope !14, !noalias !17
  %limbs.sroa.74.0.self.sroa_idx.i11 = getelementptr inbounds nuw i8, ptr %_2, i64 32
  %limbs.sroa.74.0.copyload.i12 = load i64, ptr %limbs.sroa.74.0.self.sroa_idx.i11, align 8, !alias.scope !14, !noalias !17
  %_98.i13 = lshr i64 %limbs.sroa.0.0.copyload.i4, 51
  %_100.i14 = lshr i64 %limbs.sroa.19.0.copyload.i6, 51
  %_102.i15 = lshr i64 %limbs.sroa.37.0.copyload.i8, 51
  %_104.i16 = lshr i64 %limbs.sroa.56.0.copyload.i10, 51
  %_106.i17 = lshr i64 %limbs.sroa.74.0.copyload.i12, 51
  %59 = and i64 %limbs.sroa.0.0.copyload.i4, 2251799813685247
  %60 = and i64 %limbs.sroa.19.0.copyload.i6, 2251799813685247
  %61 = and i64 %limbs.sroa.37.0.copyload.i8, 2251799813685247
  %62 = and i64 %limbs.sroa.56.0.copyload.i10, 2251799813685247
  %63 = and i64 %limbs.sroa.74.0.copyload.i12, 2251799813685247
  %_108.i18 = mul nuw nsw i64 %_106.i17, 19
  %64 = add nuw nsw i64 %_108.i18, %59
  %65 = add nuw nsw i64 %60, %_98.i13
  %66 = add nuw nsw i64 %61, %_100.i14
  %67 = add nuw nsw i64 %62, %_102.i15
  %68 = add nuw nsw i64 %63, %_104.i16
  %_4.i19 = add nuw nsw i64 %64, 19
  %69 = lshr i64 %_4.i19, 51
  %_6.i20 = add nuw nsw i64 %65, %69
  %70 = lshr i64 %_6.i20, 51
  %_8.i21 = add nuw nsw i64 %66, %70
  %71 = lshr i64 %_8.i21, 51
  %_10.i22 = add nuw nsw i64 %67, %71
  %72 = lshr i64 %_10.i22, 51
  %_12.i23 = add nuw nsw i64 %68, %72
  %73 = lshr i64 %_12.i23, 51
  %74 = add nuw nsw i64 %73, %64
  %75 = trunc i64 %74 to i8
  %_4.i2 = and i8 %75, 1
  %_6.i3 = tail call noundef i8 @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519(i8 noundef %_4.i2) #7
  %_6 = shl i8 %_6.i3, 7
  %76 = or disjoint i8 %_6, %58
  store i8 %26, ptr %_0, align 1
  %_4.sroa.4.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 1
  store i8 %27, ptr %_4.sroa.4.0._0.sroa_idx, align 1
  %_4.sroa.5.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 2
  store i8 %28, ptr %_4.sroa.5.0._0.sroa_idx, align 1
  %_4.sroa.6.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 3
  store i8 %29, ptr %_4.sroa.6.0._0.sroa_idx, align 1
  %_4.sroa.7.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 4
  store i8 %30, ptr %_4.sroa.7.0._0.sroa_idx, align 1
  %_4.sroa.8.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 5
  store i8 %31, ptr %_4.sroa.8.0._0.sroa_idx, align 1
  %_4.sroa.9.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 6
  store i8 %33, ptr %_4.sroa.9.0._0.sroa_idx, align 1
  %_4.sroa.10.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 7
  store i8 %34, ptr %_4.sroa.10.0._0.sroa_idx, align 1
  %_4.sroa.11.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 8
  store i8 %35, ptr %_4.sroa.11.0._0.sroa_idx, align 1
  %_4.sroa.12.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 9
  store i8 %36, ptr %_4.sroa.12.0._0.sroa_idx, align 1
  %_4.sroa.13.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 10
  store i8 %37, ptr %_4.sroa.13.0._0.sroa_idx, align 1
  %_4.sroa.14.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 11
  store i8 %38, ptr %_4.sroa.14.0._0.sroa_idx, align 1
  %_4.sroa.15.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 12
  store i8 %39, ptr %_4.sroa.15.0._0.sroa_idx, align 1
  %_4.sroa.16.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 13
  store i8 %40, ptr %_4.sroa.16.0._0.sroa_idx, align 1
  %_4.sroa.17.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 14
  store i8 %41, ptr %_4.sroa.17.0._0.sroa_idx, align 1
  %_4.sroa.18.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 15
  store i8 %42, ptr %_4.sroa.18.0._0.sroa_idx, align 1
  %_4.sroa.19.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 16
  store i8 %43, ptr %_4.sroa.19.0._0.sroa_idx, align 1
  %_4.sroa.20.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 17
  store i8 %44, ptr %_4.sroa.20.0._0.sroa_idx, align 1
  %_4.sroa.21.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 18
  store i8 %45, ptr %_4.sroa.21.0._0.sroa_idx, align 1
  %_4.sroa.22.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 19
  store i8 %46, ptr %_4.sroa.22.0._0.sroa_idx, align 1
  %_4.sroa.23.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 20
  store i8 %47, ptr %_4.sroa.23.0._0.sroa_idx, align 1
  %_4.sroa.24.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 21
  store i8 %48, ptr %_4.sroa.24.0._0.sroa_idx, align 1
  %_4.sroa.25.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 22
  store i8 %49, ptr %_4.sroa.25.0._0.sroa_idx, align 1
  %_4.sroa.26.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 23
  store i8 %50, ptr %_4.sroa.26.0._0.sroa_idx, align 1
  %_4.sroa.27.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 24
  store i8 %51, ptr %_4.sroa.27.0._0.sroa_idx, align 1
  %_4.sroa.28.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 25
  store i8 %52, ptr %_4.sroa.28.0._0.sroa_idx, align 1
  %_4.sroa.29.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 26
  store i8 %53, ptr %_4.sroa.29.0._0.sroa_idx, align 1
  %_4.sroa.30.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 27
  store i8 %54, ptr %_4.sroa.30.0._0.sroa_idx, align 1
  %_4.sroa.31.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 28
  store i8 %55, ptr %_4.sroa.31.0._0.sroa_idx, align 1
  %_4.sroa.32.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 29
  store i8 %56, ptr %_4.sroa.32.0._0.sroa_idx, align 1
  %_4.sroa.33.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 30
  store i8 %57, ptr %_4.sroa.33.0._0.sroa_idx, align 1
  %_4.sroa.34.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 31
  store i8 %76, ptr %_4.sroa.34.0._0.sroa_idx, align 1
  call void @llvm.lifetime.end.p0(ptr nonnull %_2)
  ret void
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
declare void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([40 x i8]) align 8 captures(none) dereferenceable(40) initializes((0, 40)), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40)) unnamed_addr #3

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #4

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #5

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #4

attributes #0 = { mustprogress nofree noinline norecurse nounwind nonlazybind willreturn memory(inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { nofree norecurse nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #4 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #5 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #6 = { nounwind }
attributes #7 = { noinline nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{!5, !7}
!5 = distinct !{!5, !6, !"_RNvMsg_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint9to_affine: %_0"}
!6 = distinct !{!6, !"_RNvMsg_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint9to_affine"}
!7 = distinct !{!7, !6, !"_RNvMsg_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint9to_affine: %self"}
!8 = !{!9, !11, !5, !7}
!9 = distinct !{!9, !10, !"_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement516invert: %t21"}
!10 = distinct !{!10, !"_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement516invert"}
!11 = distinct !{!11, !10, !"_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement516invert: %self"}
!12 = !{!9, !5}
!13 = !{!11, !5, !7}
!14 = !{!15}
!15 = distinct !{!15, !16, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes: %self"}
!16 = distinct !{!16, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes"}
!17 = !{!18}
!18 = distinct !{!18, !16, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes: %s"}
