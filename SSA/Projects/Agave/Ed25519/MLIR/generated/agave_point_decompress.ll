; ModuleID = '/home/nine/Documents/anza-code/.lmf-rir-ed25519/SSA/Projects/Agave/Ed25519/MLIR/generated/agave_point_decompress.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_781589f30b7aca1e8db8c1d787298044 = internal unnamed_addr constant [40 x i8] c"\A3xY\13\CAM\03\00\BDn\15;(\A8\01\00)\C0\01`\A2\E7\05\00\BB<\A0c\C69\07\00\FF\B6\E2\CE6 \05\00", align 8

; Function Attrs: mustprogress nofree noinline norecurse nounwind nonlazybind willreturn memory(inaccessiblemem: readwrite) uwtable
declare noundef i8 @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519(i8 noundef) unnamed_addr #0

; Function Attrs: nofree norecurse nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
declare hidden fastcc void @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement5112sqrt_ratio_i(ptr dead_on_unwind noalias nofree noundef nonnull writable writeonly align 8 captures(none) dereferenceable(48) initializes((0, 1), (8, 48)), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40), ptr noalias nofree noundef nonnull readonly align 8 captures(none) dereferenceable(40)) unnamed_addr #1

; Function Attrs: nofree norecurse nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
define void @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_18CompressedEdwardsY10decompress(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([168 x i8]) align 8 captures(none) dereferenceable(168) initializes((0, 8)) %_0, ptr noalias nofree noundef readonly captures(none) dereferenceable(32) %self) unnamed_addr #1 {
start:
  %_17.i = alloca [48 x i8], align 8
  %_12.i = alloca [40 x i8], align 16
  %v.i = alloca [40 x i8], align 16
  %u.i = alloca [40 x i8], align 8
  %YY.i = alloca [40 x i8], align 16
  %Y.i = alloca [40 x i8], align 8
  %_6 = alloca [160 x i8], align 8
  %_5.sroa.0 = alloca [80 x i8], align 8
  %Y = alloca [40 x i8], align 8
  %X = alloca [40 x i8], align 16
  call void @llvm.lifetime.start.p0(ptr nonnull %_5.sroa.0)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !4)
  call void @llvm.lifetime.start.p0(ptr nonnull %Y.i), !noalias !7
  tail call void @llvm.experimental.noalias.scope.decl(metadata !9)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !12)
  %_10.i.i.i = load i64, ptr %self, align 1, !alias.scope !14, !noalias !17
  %_3.i.i = and i64 %_10.i.i.i, 2251799813685247
  %0 = getelementptr inbounds nuw i8, ptr %self, i64 6
  %_10.i1.i.i = load i64, ptr %0, align 1, !alias.scope !18, !noalias !17
  %_7.i.i = lshr i64 %_10.i1.i.i, 3
  %_6.i.i = and i64 %_7.i.i, 2251799813685247
  %1 = getelementptr inbounds nuw i8, ptr %self, i64 12
  %_10.i2.i.i = load i64, ptr %1, align 1, !alias.scope !21, !noalias !17
  %_10.i.i = lshr i64 %_10.i2.i.i, 6
  %_9.i.i = and i64 %_10.i.i, 2251799813685247
  %2 = getelementptr inbounds nuw i8, ptr %self, i64 19
  %_10.i3.i.i = load i64, ptr %2, align 1, !alias.scope !24, !noalias !17
  %_13.i.i = lshr i64 %_10.i3.i.i, 1
  %_12.i.i = and i64 %_13.i.i, 2251799813685247
  %3 = getelementptr inbounds nuw i8, ptr %self, i64 24
  %_10.i4.i.i = load i64, ptr %3, align 1, !alias.scope !27, !noalias !17
  %_16.i.i = lshr i64 %_10.i4.i.i, 12
  %_15.i.i = and i64 %_16.i.i, 2251799813685247
  store i64 %_3.i.i, ptr %Y.i, align 8, !alias.scope !9, !noalias !30
  %_2.sroa.4.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %Y.i, i64 8
  store i64 %_6.i.i, ptr %_2.sroa.4.0._0.sroa_idx.i.i, align 8, !alias.scope !9, !noalias !30
  %_2.sroa.5.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %Y.i, i64 16
  store i64 %_9.i.i, ptr %_2.sroa.5.0._0.sroa_idx.i.i, align 8, !alias.scope !9, !noalias !30
  %_2.sroa.6.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %Y.i, i64 24
  store i64 %_12.i.i, ptr %_2.sroa.6.0._0.sroa_idx.i.i, align 8, !alias.scope !9, !noalias !30
  %_2.sroa.7.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %Y.i, i64 32
  store i64 %_15.i.i, ptr %_2.sroa.7.0._0.sroa_idx.i.i, align 8, !alias.scope !9, !noalias !30
  call void @llvm.lifetime.start.p0(ptr nonnull %YY.i), !noalias !7
  call void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %YY.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %Y.i, i32 noundef 1) #8, !alias.scope !31, !noalias !7
  call void @llvm.lifetime.start.p0(ptr nonnull %u.i), !noalias !7
  tail call void @llvm.experimental.noalias.scope.decl(metadata !35)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !38)
  %4 = getelementptr inbounds nuw i8, ptr %YY.i, i64 8
  %5 = getelementptr inbounds nuw i8, ptr %YY.i, i64 24
  %_3.sroa.9.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %u.i, i64 8
  %6 = load <2 x i64>, ptr %YY.i, align 16, !alias.scope !38, !noalias !40
  %7 = load <2 x i64>, ptr %4, align 8, !alias.scope !38, !noalias !40
  %8 = add <2 x i64> %6, <i64 36028797018963663, i64 36028797018963952>
  %9 = add <2 x i64> %7, splat (i64 36028797018963952)
  %10 = lshr <2 x i64> %8, splat (i64 51)
  %11 = extractelement <2 x i64> %8, i64 0
  %12 = and i64 %11, 2251799813685247
  %13 = and <2 x i64> %9, splat (i64 2251799813685247)
  %14 = add nuw nsw <2 x i64> %13, %10
  store <2 x i64> %14, ptr %_3.sroa.9.0._0.sroa_idx.i.i, align 8, !alias.scope !35, !noalias !42
  %_3.sroa.21.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %u.i, i64 24
  %15 = load <2 x i64>, ptr %5, align 8, !alias.scope !38, !noalias !40
  %16 = add <2 x i64> %15, splat (i64 36028797018963952)
  %17 = extractelement <2 x i64> %16, i64 1
  %_32.i.i = lshr i64 %17, 51
  %18 = and <2 x i64> %16, splat (i64 2251799813685247)
  %_34.i.i = mul nuw nsw i64 %_32.i.i, 19
  %19 = shufflevector <2 x i64> %9, <2 x i64> %16, <2 x i32> <i32 1, i32 2>
  %20 = lshr <2 x i64> %19, splat (i64 51)
  %21 = add nuw nsw i64 %_34.i.i, %12
  %22 = add nuw nsw <2 x i64> %18, %20
  store i64 %21, ptr %u.i, align 8, !alias.scope !35, !noalias !42
  store <2 x i64> %22, ptr %_3.sroa.21.0._0.sroa_idx.i.i, align 8, !alias.scope !35, !noalias !42
  call void @llvm.lifetime.start.p0(ptr nonnull %v.i), !noalias !7
  call void @llvm.lifetime.start.p0(ptr nonnull %_12.i), !noalias !7
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %_12.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %YY.i, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(40) @alloc_781589f30b7aca1e8db8c1d787298044) #8, !noalias !7
  tail call void @llvm.experimental.noalias.scope.decl(metadata !43)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !46)
  %output.sroa.8.0.self.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %_12.i, i64 16
  %output.sroa.12.0.self.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %_12.i, i64 32
  %output.sroa.12.0.copyload.i.i = load i64, ptr %output.sroa.12.0.self.sroa_idx.i.i, align 16, !alias.scope !46, !noalias !48
  %23 = load <2 x i64>, ptr %_12.i, align 16, !alias.scope !46, !noalias !48
  %24 = add <2 x i64> %23, <i64 1, i64 0>
  store <2 x i64> %24, ptr %v.i, align 16, !alias.scope !43, !noalias !50
  %output.sroa.8.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %v.i, i64 16
  %25 = load <2 x i64>, ptr %output.sroa.8.0.self.sroa_idx.i.i, align 16, !alias.scope !46, !noalias !48
  store <2 x i64> %25, ptr %output.sroa.8.0._0.sroa_idx.i.i, align 16, !alias.scope !43, !noalias !50
  %output.sroa.12.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %v.i, i64 32
  store i64 %output.sroa.12.0.copyload.i.i, ptr %output.sroa.12.0._0.sroa_idx.i.i, align 16, !alias.scope !43, !noalias !50
  call void @llvm.lifetime.end.p0(ptr nonnull %_12.i), !noalias !7
  call void @llvm.lifetime.start.p0(ptr nonnull %_17.i), !noalias !7
  call fastcc void @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement5112sqrt_ratio_i(ptr noalias nofree noundef align 8 captures(none) dereferenceable(48) %_17.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %u.i, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(40) %v.i) #8, !noalias !7
  %is_valid_y_coord.i = load i8, ptr %_17.i, align 8, !noalias !7, !noundef !51
  %26 = getelementptr inbounds nuw i8, ptr %_17.i, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %_5.sroa.0, ptr noundef nonnull align 8 dereferenceable(40) %26, i64 40, i1 false), !noalias !4
  call void @llvm.lifetime.end.p0(ptr nonnull %_17.i), !noalias !7
  %_5.sroa.0.40..sroa_idx18 = getelementptr inbounds nuw i8, ptr %_5.sroa.0, i64 40
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %_5.sroa.0.40..sroa_idx18, ptr noundef nonnull align 8 dereferenceable(40) %Y.i, i64 40, i1 false), !noalias !4
  call void @llvm.lifetime.end.p0(ptr nonnull %v.i), !noalias !7
  call void @llvm.lifetime.end.p0(ptr nonnull %u.i), !noalias !7
  call void @llvm.lifetime.end.p0(ptr nonnull %YY.i), !noalias !7
  call void @llvm.lifetime.end.p0(ptr nonnull %Y.i), !noalias !7
  call void @llvm.lifetime.start.p0(ptr nonnull %X)
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 16 dereferenceable(40) %X, ptr noundef nonnull align 8 dereferenceable(40) %_5.sroa.0, i64 40, i1 false)
  call void @llvm.lifetime.start.p0(ptr nonnull %Y)
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %Y, ptr noundef nonnull align 8 dereferenceable(40) %_5.sroa.0.40..sroa_idx18, i64 40, i1 false)
  call void @llvm.lifetime.end.p0(ptr nonnull %_5.sroa.0)
  %27 = icmp eq i8 %is_valid_y_coord.i, 0
  br i1 %27, label %bb5, label %bb2

bb2:                                              ; preds = %start
  call void @llvm.lifetime.start.p0(ptr nonnull %_6)
  %28 = getelementptr inbounds nuw i8, ptr %self, i64 31
  %self.val = load i8, ptr %28, align 1, !noundef !51
  tail call void @llvm.experimental.noalias.scope.decl(metadata !52)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !55)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !57)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !59)
  %_6.i = lshr i8 %self.val, 7
  %_13.i = tail call noundef i8 @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519(i8 noundef %_6.i) #9
  %output.sroa.6.0.self.sroa_idx.i.i2 = getelementptr inbounds nuw i8, ptr %X, i64 8
  %output.sroa.10.0.self.sroa_idx.i.i6 = getelementptr inbounds nuw i8, ptr %X, i64 24
  %_11.i.i = zext i8 %_13.i to i64
  %_10.i.i10 = sub nsw i64 0, %_11.i.i
  %output.sroa.0.0.copyload.i.i1 = load i64, ptr %X, align 16, !alias.scope !61, !noalias !64
  %29 = load <2 x i64>, ptr %X, align 16, !alias.scope !61, !noalias !64
  %30 = load <2 x i64>, ptr %output.sroa.6.0.self.sroa_idx.i.i2, align 8, !alias.scope !61, !noalias !64
  %_3.i.i.i = sub i64 2251799813684944, %output.sroa.0.0.copyload.i.i1
  %31 = sub <2 x i64> <i64 36028797018963664, i64 36028797018963952>, %29
  %32 = sub <2 x i64> splat (i64 36028797018963952), %30
  %33 = lshr <2 x i64> %31, splat (i64 51)
  %34 = and i64 %_3.i.i.i, 2251799813685247
  %35 = and <2 x i64> %32, splat (i64 2251799813685247)
  %36 = add nuw nsw <2 x i64> %35, %33
  %37 = xor <2 x i64> %36, %30
  %38 = insertelement <2 x i64> poison, i64 %_10.i.i10, i64 0
  %39 = shufflevector <2 x i64> %38, <2 x i64> poison, <2 x i32> zeroinitializer
  %40 = and <2 x i64> %37, %39
  %41 = xor <2 x i64> %40, %30
  store <2 x i64> %41, ptr %output.sroa.6.0.self.sroa_idx.i.i2, align 8, !alias.scope !66, !noalias !69
  %42 = load <2 x i64>, ptr %output.sroa.10.0.self.sroa_idx.i.i6, align 8, !alias.scope !61, !noalias !64
  %43 = sub <2 x i64> splat (i64 36028797018963952), %42
  %44 = extractelement <2 x i64> %43, i64 1
  %_21.i.i.i = lshr i64 %44, 51
  %45 = and <2 x i64> %43, splat (i64 2251799813685247)
  %_23.i.i.i = mul nuw nsw i64 %_21.i.i.i, 19
  %46 = shufflevector <2 x i64> %32, <2 x i64> %43, <2 x i32> <i32 1, i32 2>
  %47 = lshr <2 x i64> %46, splat (i64 51)
  %48 = add nuw nsw i64 %_23.i.i.i, %34
  %49 = add nuw nsw <2 x i64> %45, %47
  %_13.i.i11 = xor i64 %48, %output.sroa.0.0.copyload.i.i1
  %_12.i.i12 = and i64 %_13.i.i11, %_10.i.i10
  %50 = xor i64 %_12.i.i12, %output.sroa.0.0.copyload.i.i1
  store i64 %50, ptr %X, align 16, !alias.scope !66, !noalias !69
  %51 = xor <2 x i64> %49, %42
  %52 = and <2 x i64> %51, %39
  %53 = xor <2 x i64> %52, %42
  store <2 x i64> %53, ptr %output.sroa.10.0.self.sroa_idx.i.i6, align 8, !alias.scope !66, !noalias !69
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(160) %_6, ptr noundef nonnull align 16 dereferenceable(40) %X, i64 40, i1 false), !alias.scope !71, !noalias !72
  %54 = getelementptr inbounds nuw i8, ptr %_6, i64 120
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %54, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %X, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %Y) #8, !alias.scope !73, !noalias !59
  %55 = getelementptr inbounds nuw i8, ptr %_6, i64 40
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %55, ptr noundef nonnull readonly align 8 dereferenceable(40) %Y, i64 40, i1 false), !alias.scope !74, !noalias !75
  %56 = getelementptr inbounds nuw i8, ptr %_6, i64 80
  store i64 1, ptr %56, align 8, !alias.scope !76, !noalias !77
  %Z.sroa.4.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_6, i64 88
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 8 dereferenceable(32) %Z.sroa.4.0..sroa_idx, i8 0, i64 32, i1 false)
  %57 = getelementptr inbounds nuw i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(160) %57, ptr noundef nonnull align 8 dereferenceable(160) %_6, i64 160, i1 false)
  call void @llvm.lifetime.end.p0(ptr nonnull %_6)
  br label %bb5

bb5:                                              ; preds = %bb2, %start
  %.sink = phi i64 [ 1, %bb2 ], [ 0, %start ]
  store i64 %.sink, ptr %_0, align 8
  call void @llvm.lifetime.end.p0(ptr nonnull %Y)
  call void @llvm.lifetime.end.p0(ptr nonnull %X)
  ret void
}

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable
declare void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([40 x i8]) align 8 captures(none) dereferenceable(40), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40), i32 noundef) unnamed_addr #2

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
declare void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([40 x i8]) align 8 captures(none) dereferenceable(40) initializes((0, 40)), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40)) unnamed_addr #3

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #4

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #5

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #4

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr writeonly captures(none), i8, i64, i1 immarg) #6

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite)
declare void @llvm.experimental.noalias.scope.decl(metadata) #7

attributes #0 = { mustprogress nofree noinline norecurse nounwind nonlazybind willreturn memory(inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nofree norecurse nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #4 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #5 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #6 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #7 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite) }
attributes #8 = { nounwind }
attributes #9 = { noinline nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{!5}
!5 = distinct !{!5, !6, !"_RNvNtNtCsjK63O35OHGN_14solana_ed255197edwards10decompress6step_1: %repr"}
!6 = distinct !{!6, !"_RNvNtNtCsjK63O35OHGN_14solana_ed255197edwards10decompress6step_1"}
!7 = !{!8, !5}
!8 = distinct !{!8, !6, !"_RNvNtNtCsjK63O35OHGN_14solana_ed255197edwards10decompress6step_1: %_0"}
!9 = !{!10}
!10 = distinct !{!10, !11, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement5110from_bytes: %_0"}
!11 = distinct !{!11, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement5110from_bytes"}
!12 = !{!13}
!13 = distinct !{!13, !11, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement5110from_bytes: %bytes"}
!14 = !{!15, !13, !5}
!15 = distinct !{!15, !16, !"_RNvNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB7_14FieldElement5110from_bytes8load8_at: %input.0"}
!16 = distinct !{!16, !"_RNvNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB7_14FieldElement5110from_bytes8load8_at"}
!17 = !{!10, !8}
!18 = !{!19, !13, !5}
!19 = distinct !{!19, !20, !"_RNvNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB7_14FieldElement5110from_bytes8load8_at: %input.0"}
!20 = distinct !{!20, !"_RNvNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB7_14FieldElement5110from_bytes8load8_at"}
!21 = !{!22, !13, !5}
!22 = distinct !{!22, !23, !"_RNvNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB7_14FieldElement5110from_bytes8load8_at: %input.0"}
!23 = distinct !{!23, !"_RNvNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB7_14FieldElement5110from_bytes8load8_at"}
!24 = !{!25, !13, !5}
!25 = distinct !{!25, !26, !"_RNvNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB7_14FieldElement5110from_bytes8load8_at: %input.0"}
!26 = distinct !{!26, !"_RNvNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB7_14FieldElement5110from_bytes8load8_at"}
!27 = !{!28, !13, !5}
!28 = distinct !{!28, !29, !"_RNvNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB7_14FieldElement5110from_bytes8load8_at: %input.0"}
!29 = distinct !{!29, !"_RNvNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB7_14FieldElement5110from_bytes8load8_at"}
!30 = !{!13, !8, !5}
!31 = !{!32, !34}
!32 = distinct !{!32, !33, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement516square: %_0"}
!33 = distinct !{!33, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement516square"}
!34 = distinct !{!34, !33, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement516square: %self"}
!35 = !{!36}
!36 = distinct !{!36, !37, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub: %_0"}
!37 = distinct !{!37, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub"}
!38 = !{!39}
!39 = distinct !{!39, !37, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub: %self"}
!40 = !{!36, !41, !8, !5}
!41 = distinct !{!41, !37, !"_RNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Sub3sub: %_rhs"}
!42 = !{!39, !41, !8, !5}
!43 = !{!44}
!44 = distinct !{!44, !45, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %_0"}
!45 = distinct !{!45, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add"}
!46 = !{!47}
!47 = distinct !{!47, !45, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %self"}
!48 = !{!44, !49, !8, !5}
!49 = distinct !{!49, !45, !"_RNvXs1_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Add3add: %_rhs"}
!50 = !{!47, !49, !8, !5}
!51 = !{}
!52 = !{!53}
!53 = distinct !{!53, !54, !"_RNvNtNtCsjK63O35OHGN_14solana_ed255197edwards10decompress6step_2: %_0"}
!54 = distinct !{!54, !"_RNvNtNtCsjK63O35OHGN_14solana_ed255197edwards10decompress6step_2"}
!55 = !{!56}
!56 = distinct !{!56, !54, !"_RNvNtNtCsjK63O35OHGN_14solana_ed255197edwards10decompress6step_2: %X"}
!57 = !{!58}
!58 = distinct !{!58, !54, !"_RNvNtNtCsjK63O35OHGN_14solana_ed255197edwards10decompress6step_2: %Y"}
!59 = !{!60}
!60 = distinct !{!60, !54, !"_RNvNtNtCsjK63O35OHGN_14solana_ed255197edwards10decompress6step_2: %Z"}
!61 = !{!62, !56}
!62 = distinct !{!62, !63, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Neg3neg: %self"}
!63 = distinct !{!63, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Neg3neg"}
!64 = !{!65, !53, !58, !60}
!65 = distinct !{!65, !63, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Neg3neg: %_0"}
!66 = !{!67, !56}
!67 = distinct !{!67, !68, !"_RNvXs7_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51NtCsh8VEmffyqhs_6subtle23ConditionallySelectable18conditional_assign: %self"}
!68 = distinct !{!68, !"_RNvXs7_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51NtCsh8VEmffyqhs_6subtle23ConditionallySelectable18conditional_assign"}
!69 = !{!70, !53, !58, !60}
!70 = distinct !{!70, !68, !"_RNvXs7_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51NtCsh8VEmffyqhs_6subtle23ConditionallySelectable18conditional_assign: %other"}
!71 = !{!53, !56}
!72 = !{!58, !60}
!73 = !{!53, !56, !58}
!74 = !{!53, !58}
!75 = !{!56, !60}
!76 = !{!53, !60}
!77 = !{!56, !58}
