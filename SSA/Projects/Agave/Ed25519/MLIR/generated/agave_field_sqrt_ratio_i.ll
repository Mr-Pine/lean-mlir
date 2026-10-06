; ModuleID = '/home/nine/Documents/anza-code/.lmf-rir-ed25519/SSA/Projects/Agave/Ed25519/MLIR/generated/agave_field_sqrt_ratio_i.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_4a840e2d409aa262ab906382f915ac1f = internal unnamed_addr constant [40 x i8] c"\B0\A0\0EJ'\1B\06\00\9D\18\8F\FC\A5\D5\00\00`\0C\BD\9C^\EF\07\00\9EL\80\A6\95\85\07\00\1D\FC\04H2\B8\02\00", align 8

; Function Attrs: mustprogress nofree noinline norecurse nounwind nonlazybind willreturn memory(inaccessiblemem: readwrite) uwtable
declare noundef i8 @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519(i8 noundef) unnamed_addr #0

; Function Attrs: nofree norecurse nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
define hidden fastcc void @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement5112sqrt_ratio_i(ptr dead_on_unwind noalias nofree noundef nonnull writable writeonly align 8 captures(none) dereferenceable(48) initializes((0, 1), (8, 48)) %_0, ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40) %u, ptr noalias nofree noundef nonnull readonly align 8 captures(none) dereferenceable(40) %v) unnamed_addr #1 {
start:
  %_9.i28 = alloca [32 x i8], align 1
  %_5.i29 = alloca [32 x i8], align 1
  %_9.i1 = alloca [32 x i8], align 1
  %_5.i2 = alloca [32 x i8], align 1
  %_9.i = alloca [32 x i8], align 1
  %_5.i = alloca [32 x i8], align 1
  %t20.i = alloca [40 x i8], align 8
  %_3.i = alloca [80 x i8], align 8
  %t19.i = alloca [40 x i8], align 8
  %r_prime = alloca [40 x i8], align 16
  %_34 = alloca [40 x i8], align 8
  %_32 = alloca [40 x i8], align 8
  %_21 = alloca [40 x i8], align 8
  %check = alloca [40 x i8], align 8
  %_17 = alloca [40 x i8], align 8
  %_15 = alloca [40 x i8], align 8
  %_12 = alloca [40 x i8], align 8
  %r = alloca [40 x i8], align 16
  %_8 = alloca [40 x i8], align 8
  %v7 = alloca [40 x i8], align 8
  %_5 = alloca [40 x i8], align 8
  %v3 = alloca [40 x i8], align 8
  call void @llvm.lifetime.start.p0(ptr nonnull %v3)
  call void @llvm.lifetime.start.p0(ptr nonnull %_5)
  call void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %_5, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %v, i32 noundef 1) #8, !alias.scope !4
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %v3, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_5, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %v) #8
  call void @llvm.lifetime.end.p0(ptr nonnull %_5)
  call void @llvm.lifetime.start.p0(ptr nonnull %v7)
  call void @llvm.lifetime.start.p0(ptr nonnull %_8)
  call void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %_8, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %v3, i32 noundef 1) #8, !alias.scope !8
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %v7, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_8, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %v) #8
  call void @llvm.lifetime.end.p0(ptr nonnull %_8)
  call void @llvm.lifetime.start.p0(ptr nonnull %_12)
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %_12, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %u, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %v3) #8
  call void @llvm.lifetime.start.p0(ptr nonnull %_15)
  call void @llvm.lifetime.start.p0(ptr nonnull %_17)
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %_17, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %u, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %v7) #8
  call void @llvm.lifetime.start.p0(ptr nonnull %_3.i), !noalias !12
  call fastcc void @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement518pow22501(ptr noalias nofree noundef align 8 captures(none) dereferenceable(80) %_3.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_17) #8, !noalias !16
  call void @llvm.lifetime.start.p0(ptr nonnull %t19.i), !noalias !12
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %t19.i, ptr noundef nonnull align 8 dereferenceable(40) %_3.i, i64 40, i1 false), !noalias !12
  call void @llvm.lifetime.end.p0(ptr nonnull %_3.i), !noalias !12
  call void @llvm.lifetime.start.p0(ptr nonnull %t20.i), !noalias !12
  call void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %t20.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %t19.i, i32 noundef 2) #8, !noalias !12
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %_15, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_17, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %t20.i) #8
  call void @llvm.lifetime.end.p0(ptr nonnull %t20.i), !noalias !12
  call void @llvm.lifetime.end.p0(ptr nonnull %t19.i), !noalias !12
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %r, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_12, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_15) #8
  call void @llvm.lifetime.end.p0(ptr nonnull %_17)
  call void @llvm.lifetime.end.p0(ptr nonnull %_15)
  call void @llvm.lifetime.end.p0(ptr nonnull %_12)
  call void @llvm.lifetime.start.p0(ptr nonnull %check)
  call void @llvm.lifetime.start.p0(ptr nonnull %_21)
  call void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %_21, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %r, i32 noundef 1) #8
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %check, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %v, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_21) #8
  call void @llvm.lifetime.end.p0(ptr nonnull %_21)
  call void @llvm.lifetime.start.p0(ptr nonnull %_5.i), !noalias !17
  tail call void @llvm.experimental.noalias.scope.decl(metadata !21)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !24)
  %limbs.sroa.0.0.copyload.i = load i64, ptr %check, align 8, !alias.scope !24, !noalias !26
  %limbs.sroa.19.0.self.sroa_idx.i = getelementptr inbounds nuw i8, ptr %check, i64 8
  %limbs.sroa.19.0.copyload.i = load i64, ptr %limbs.sroa.19.0.self.sroa_idx.i, align 8, !alias.scope !24, !noalias !26
  %limbs.sroa.37.0.self.sroa_idx.i = getelementptr inbounds nuw i8, ptr %check, i64 16
  %limbs.sroa.37.0.copyload.i = load i64, ptr %limbs.sroa.37.0.self.sroa_idx.i, align 8, !alias.scope !24, !noalias !26
  %limbs.sroa.56.0.self.sroa_idx.i = getelementptr inbounds nuw i8, ptr %check, i64 24
  %limbs.sroa.56.0.copyload.i = load i64, ptr %limbs.sroa.56.0.self.sroa_idx.i, align 8, !alias.scope !24, !noalias !26
  %limbs.sroa.74.0.self.sroa_idx.i = getelementptr inbounds nuw i8, ptr %check, i64 32
  %limbs.sroa.74.0.copyload.i = load i64, ptr %limbs.sroa.74.0.self.sroa_idx.i, align 8, !alias.scope !24, !noalias !26
  %_98.i = lshr i64 %limbs.sroa.0.0.copyload.i, 51
  %_100.i = lshr i64 %limbs.sroa.19.0.copyload.i, 51
  %_102.i = lshr i64 %limbs.sroa.37.0.copyload.i, 51
  %_104.i = lshr i64 %limbs.sroa.56.0.copyload.i, 51
  %_106.i = lshr i64 %limbs.sroa.74.0.copyload.i, 51
  %0 = and i64 %limbs.sroa.0.0.copyload.i, 2251799813685247
  %1 = and i64 %limbs.sroa.19.0.copyload.i, 2251799813685247
  %2 = and i64 %limbs.sroa.37.0.copyload.i, 2251799813685247
  %3 = and i64 %limbs.sroa.56.0.copyload.i, 2251799813685247
  %4 = and i64 %limbs.sroa.74.0.copyload.i, 2251799813685247
  %_108.i = mul nuw nsw i64 %_106.i, 19
  %5 = add nuw nsw i64 %_108.i, %0
  %6 = add nuw nsw i64 %1, %_98.i
  %7 = add nuw nsw i64 %2, %_100.i
  %8 = add nuw nsw i64 %3, %_102.i
  %9 = add nuw nsw i64 %4, %_104.i
  %_4.i84 = add nuw nsw i64 %5, 19
  %10 = lshr i64 %_4.i84, 51
  %_6.i85 = add nuw nsw i64 %10, %6
  %11 = lshr i64 %_6.i85, 51
  %_8.i86 = add nuw nsw i64 %11, %7
  %12 = lshr i64 %_8.i86, 51
  %_10.i87 = add nuw nsw i64 %12, %8
  %13 = lshr i64 %_10.i87, 51
  %_12.i88 = add nuw nsw i64 %13, %9
  %14 = lshr i64 %_12.i88, 51
  %_14.i89 = mul nuw nsw i64 %14, 19
  %15 = add nuw nsw i64 %_14.i89, %5
  %_15.i90 = lshr i64 %15, 51
  %16 = add nuw nsw i64 %_15.i90, %6
  %_17.i91 = lshr i64 %16, 51
  %17 = add nuw nsw i64 %_17.i91, %7
  %18 = and i64 %16, 2251799813685247
  %_19.i92 = lshr i64 %17, 51
  %19 = add nuw nsw i64 %_19.i92, %8
  %20 = and i64 %17, 2251799813685247
  %_21.i93 = lshr i64 %19, 51
  %21 = add nuw nsw i64 %_21.i93, %9
  %22 = and i64 %19, 2251799813685247
  %23 = and i64 %21, 2251799813685247
  %24 = trunc i64 %15 to i8
  store i8 %24, ptr %_5.i, align 1, !alias.scope !21, !noalias !27
  %_24.i94 = lshr i64 %15, 8
  %25 = getelementptr inbounds nuw i8, ptr %_5.i, i64 1
  %26 = trunc i64 %_24.i94 to i8
  store i8 %26, ptr %25, align 1, !alias.scope !21, !noalias !27
  %_26.i95 = lshr i64 %15, 16
  %27 = getelementptr inbounds nuw i8, ptr %_5.i, i64 2
  %28 = trunc i64 %_26.i95 to i8
  store i8 %28, ptr %27, align 1, !alias.scope !21, !noalias !27
  %_28.i96 = lshr i64 %15, 24
  %29 = getelementptr inbounds nuw i8, ptr %_5.i, i64 3
  %30 = trunc i64 %_28.i96 to i8
  store i8 %30, ptr %29, align 1, !alias.scope !21, !noalias !27
  %_30.i97 = lshr i64 %15, 32
  %31 = getelementptr inbounds nuw i8, ptr %_5.i, i64 4
  %32 = trunc i64 %_30.i97 to i8
  store i8 %32, ptr %31, align 1, !alias.scope !21, !noalias !27
  %_32.i = lshr i64 %15, 40
  %33 = getelementptr inbounds nuw i8, ptr %_5.i, i64 5
  %34 = trunc i64 %_32.i to i8
  store i8 %34, ptr %33, align 1, !alias.scope !21, !noalias !27
  %35 = lshr i64 %15, 48
  %_35.i = and i64 %35, 7
  %_37.i = shl nuw nsw i64 %18, 3
  %_34.i = or disjoint i64 %_37.i, %_35.i
  %36 = getelementptr inbounds nuw i8, ptr %_5.i, i64 6
  %37 = trunc i64 %_34.i to i8
  store i8 %37, ptr %36, align 1, !alias.scope !21, !noalias !27
  %_39.i = lshr i64 %16, 5
  %38 = getelementptr inbounds nuw i8, ptr %_5.i, i64 7
  %39 = trunc i64 %_39.i to i8
  store i8 %39, ptr %38, align 1, !alias.scope !21, !noalias !27
  %_41.i = lshr i64 %16, 13
  %40 = getelementptr inbounds nuw i8, ptr %_5.i, i64 8
  %41 = trunc i64 %_41.i to i8
  store i8 %41, ptr %40, align 1, !alias.scope !21, !noalias !27
  %_43.i = lshr i64 %16, 21
  %42 = getelementptr inbounds nuw i8, ptr %_5.i, i64 9
  %43 = trunc i64 %_43.i to i8
  store i8 %43, ptr %42, align 1, !alias.scope !21, !noalias !27
  %_45.i = lshr i64 %16, 29
  %44 = getelementptr inbounds nuw i8, ptr %_5.i, i64 10
  %45 = trunc i64 %_45.i to i8
  store i8 %45, ptr %44, align 1, !alias.scope !21, !noalias !27
  %_47.i = lshr i64 %16, 37
  %46 = getelementptr inbounds nuw i8, ptr %_5.i, i64 11
  %47 = trunc i64 %_47.i to i8
  store i8 %47, ptr %46, align 1, !alias.scope !21, !noalias !27
  %_50.i = lshr i64 %18, 45
  %_52.i = shl nuw nsw i64 %20, 6
  %_49.i = or disjoint i64 %_52.i, %_50.i
  %48 = getelementptr inbounds nuw i8, ptr %_5.i, i64 12
  %49 = trunc i64 %_49.i to i8
  store i8 %49, ptr %48, align 1, !alias.scope !21, !noalias !27
  %_54.i = lshr i64 %17, 2
  %50 = getelementptr inbounds nuw i8, ptr %_5.i, i64 13
  %51 = trunc i64 %_54.i to i8
  store i8 %51, ptr %50, align 1, !alias.scope !21, !noalias !27
  %_56.i = lshr i64 %17, 10
  %52 = getelementptr inbounds nuw i8, ptr %_5.i, i64 14
  %53 = trunc i64 %_56.i to i8
  store i8 %53, ptr %52, align 1, !alias.scope !21, !noalias !27
  %_58.i = lshr i64 %17, 18
  %54 = getelementptr inbounds nuw i8, ptr %_5.i, i64 15
  %55 = trunc i64 %_58.i to i8
  store i8 %55, ptr %54, align 1, !alias.scope !21, !noalias !27
  %_60.i = lshr i64 %17, 26
  %56 = getelementptr inbounds nuw i8, ptr %_5.i, i64 16
  %57 = trunc i64 %_60.i to i8
  store i8 %57, ptr %56, align 1, !alias.scope !21, !noalias !27
  %_62.i = lshr i64 %17, 34
  %58 = getelementptr inbounds nuw i8, ptr %_5.i, i64 17
  %59 = trunc i64 %_62.i to i8
  store i8 %59, ptr %58, align 1, !alias.scope !21, !noalias !27
  %_64.i = lshr i64 %17, 42
  %60 = getelementptr inbounds nuw i8, ptr %_5.i, i64 18
  %61 = trunc i64 %_64.i to i8
  store i8 %61, ptr %60, align 1, !alias.scope !21, !noalias !27
  %_67.i = lshr i64 %20, 50
  %_69.i = shl nuw nsw i64 %22, 1
  %_66.i = or disjoint i64 %_69.i, %_67.i
  %62 = getelementptr inbounds nuw i8, ptr %_5.i, i64 19
  %63 = trunc i64 %_66.i to i8
  store i8 %63, ptr %62, align 1, !alias.scope !21, !noalias !27
  %_71.i = lshr i64 %19, 7
  %64 = getelementptr inbounds nuw i8, ptr %_5.i, i64 20
  %65 = trunc i64 %_71.i to i8
  store i8 %65, ptr %64, align 1, !alias.scope !21, !noalias !27
  %_73.i = lshr i64 %19, 15
  %66 = getelementptr inbounds nuw i8, ptr %_5.i, i64 21
  %67 = trunc i64 %_73.i to i8
  store i8 %67, ptr %66, align 1, !alias.scope !21, !noalias !27
  %_75.i = lshr i64 %19, 23
  %68 = getelementptr inbounds nuw i8, ptr %_5.i, i64 22
  %69 = trunc i64 %_75.i to i8
  store i8 %69, ptr %68, align 1, !alias.scope !21, !noalias !27
  %_77.i = lshr i64 %19, 31
  %70 = getelementptr inbounds nuw i8, ptr %_5.i, i64 23
  %71 = trunc i64 %_77.i to i8
  store i8 %71, ptr %70, align 1, !alias.scope !21, !noalias !27
  %_79.i = lshr i64 %19, 39
  %72 = getelementptr inbounds nuw i8, ptr %_5.i, i64 24
  %73 = trunc i64 %_79.i to i8
  store i8 %73, ptr %72, align 1, !alias.scope !21, !noalias !27
  %_82.i = lshr i64 %22, 47
  %_84.i = shl nuw nsw i64 %23, 4
  %_81.i = or disjoint i64 %_84.i, %_82.i
  %74 = getelementptr inbounds nuw i8, ptr %_5.i, i64 25
  %75 = trunc i64 %_81.i to i8
  store i8 %75, ptr %74, align 1, !alias.scope !21, !noalias !27
  %_86.i = lshr i64 %21, 4
  %76 = getelementptr inbounds nuw i8, ptr %_5.i, i64 26
  %77 = trunc i64 %_86.i to i8
  store i8 %77, ptr %76, align 1, !alias.scope !21, !noalias !27
  %_88.i = lshr i64 %21, 12
  %78 = getelementptr inbounds nuw i8, ptr %_5.i, i64 27
  %79 = trunc i64 %_88.i to i8
  store i8 %79, ptr %78, align 1, !alias.scope !21, !noalias !27
  %_90.i = lshr i64 %21, 20
  %80 = getelementptr inbounds nuw i8, ptr %_5.i, i64 28
  %81 = trunc i64 %_90.i to i8
  store i8 %81, ptr %80, align 1, !alias.scope !21, !noalias !27
  %_92.i = lshr i64 %21, 28
  %82 = getelementptr inbounds nuw i8, ptr %_5.i, i64 29
  %83 = trunc i64 %_92.i to i8
  store i8 %83, ptr %82, align 1, !alias.scope !21, !noalias !27
  %_94.i = lshr i64 %21, 36
  %84 = getelementptr inbounds nuw i8, ptr %_5.i, i64 30
  %85 = trunc i64 %_94.i to i8
  store i8 %85, ptr %84, align 1, !alias.scope !21, !noalias !27
  %_96.i = lshr i64 %23, 44
  %86 = getelementptr inbounds nuw i8, ptr %_5.i, i64 31
  %87 = trunc nuw nsw i64 %_96.i to i8
  store i8 %87, ptr %86, align 1, !alias.scope !21, !noalias !27
  call void @llvm.lifetime.start.p0(ptr nonnull %_9.i), !noalias !17
  call void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes(ptr noalias nofree noundef nonnull sret([32 x i8]) align 1 captures(none) dereferenceable(32) %_9.i, ptr noalias nofree noundef nonnull readonly align 8 captures(none) dereferenceable(40) %u) #8, !noalias !28
  %_0.i = call fastcc noundef i8 @_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519(ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) %_5.i, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) %_9.i) #9
  call void @llvm.lifetime.end.p0(ptr nonnull %_9.i), !noalias !17
  call void @llvm.lifetime.end.p0(ptr nonnull %_5.i), !noalias !17
  %output.sroa.6.0.self.sroa_idx.i = getelementptr inbounds nuw i8, ptr %u, i64 8
  call void @llvm.lifetime.start.p0(ptr nonnull %_5.i2), !noalias !29
  store i8 %24, ptr %_5.i2, align 1, !alias.scope !33, !noalias !36
  %88 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 1
  store i8 %26, ptr %88, align 1, !alias.scope !33, !noalias !36
  %89 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 2
  store i8 %28, ptr %89, align 1, !alias.scope !33, !noalias !36
  %90 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 3
  store i8 %30, ptr %90, align 1, !alias.scope !33, !noalias !36
  %91 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 4
  store i8 %32, ptr %91, align 1, !alias.scope !33, !noalias !36
  %92 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 5
  store i8 %34, ptr %92, align 1, !alias.scope !33, !noalias !36
  %93 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 6
  store i8 %37, ptr %93, align 1, !alias.scope !33, !noalias !36
  %94 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 7
  store i8 %39, ptr %94, align 1, !alias.scope !33, !noalias !36
  %95 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 8
  store i8 %41, ptr %95, align 1, !alias.scope !33, !noalias !36
  %96 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 9
  store i8 %43, ptr %96, align 1, !alias.scope !33, !noalias !36
  %97 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 10
  store i8 %45, ptr %97, align 1, !alias.scope !33, !noalias !36
  %98 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 11
  store i8 %47, ptr %98, align 1, !alias.scope !33, !noalias !36
  %99 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 12
  store i8 %49, ptr %99, align 1, !alias.scope !33, !noalias !36
  %100 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 13
  store i8 %51, ptr %100, align 1, !alias.scope !33, !noalias !36
  %101 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 14
  store i8 %53, ptr %101, align 1, !alias.scope !33, !noalias !36
  %102 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 15
  store i8 %55, ptr %102, align 1, !alias.scope !33, !noalias !36
  %103 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 16
  store i8 %57, ptr %103, align 1, !alias.scope !33, !noalias !36
  %104 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 17
  store i8 %59, ptr %104, align 1, !alias.scope !33, !noalias !36
  %105 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 18
  store i8 %61, ptr %105, align 1, !alias.scope !33, !noalias !36
  %106 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 19
  store i8 %63, ptr %106, align 1, !alias.scope !33, !noalias !36
  %107 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 20
  store i8 %65, ptr %107, align 1, !alias.scope !33, !noalias !36
  %108 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 21
  store i8 %67, ptr %108, align 1, !alias.scope !33, !noalias !36
  %109 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 22
  store i8 %69, ptr %109, align 1, !alias.scope !33, !noalias !36
  %110 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 23
  store i8 %71, ptr %110, align 1, !alias.scope !33, !noalias !36
  %111 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 24
  store i8 %73, ptr %111, align 1, !alias.scope !33, !noalias !36
  %112 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 25
  store i8 %75, ptr %112, align 1, !alias.scope !33, !noalias !36
  %113 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 26
  store i8 %77, ptr %113, align 1, !alias.scope !33, !noalias !36
  %114 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 27
  store i8 %79, ptr %114, align 1, !alias.scope !33, !noalias !36
  %115 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 28
  store i8 %81, ptr %115, align 1, !alias.scope !33, !noalias !36
  %116 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 29
  store i8 %83, ptr %116, align 1, !alias.scope !33, !noalias !36
  %117 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 30
  store i8 %85, ptr %117, align 1, !alias.scope !33, !noalias !36
  %118 = getelementptr inbounds nuw i8, ptr %_5.i2, i64 31
  store i8 %87, ptr %118, align 1, !alias.scope !33, !noalias !36
  call void @llvm.lifetime.start.p0(ptr nonnull %_9.i1), !noalias !29
  %119 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 1
  %120 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 2
  %121 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 3
  %122 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 4
  %123 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 5
  %124 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 6
  %125 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 7
  %126 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 8
  %127 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 9
  %128 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 10
  %129 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 11
  %130 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 12
  %131 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 13
  %132 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 14
  %133 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 15
  %134 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 16
  %135 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 17
  %136 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 18
  %137 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 19
  %138 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 20
  %139 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 21
  %140 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 22
  %141 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 23
  %142 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 24
  %143 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 25
  %144 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 26
  %145 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 27
  %146 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 28
  %147 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 29
  %148 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 30
  %149 = getelementptr inbounds nuw i8, ptr %_9.i1, i64 31
  %output.sroa.6.0._0.sroa_idx.i24 = getelementptr inbounds nuw i8, ptr %_34, i64 8
  %150 = load <4 x i64>, ptr %u, align 8, !alias.scope !38, !noalias !41
  %151 = load <4 x i64>, ptr %output.sroa.6.0.self.sroa_idx.i, align 8, !alias.scope !38, !noalias !41
  %152 = sub <4 x i64> <i64 36028797018963664, i64 36028797018963952, i64 36028797018963952, i64 36028797018963952>, %150
  %153 = sub <4 x i64> splat (i64 36028797018963952), %151
  %154 = lshr <4 x i64> %152, splat (i64 51)
  %155 = extractelement <4 x i64> %153, i64 3
  %_21.i.i = lshr i64 %155, 51
  %156 = extractelement <4 x i64> %152, i64 0
  %157 = and i64 %156, 2251799813685247
  %158 = and <4 x i64> %153, splat (i64 2251799813685247)
  %_23.i.i = mul nuw nsw i64 %_21.i.i, 19
  %159 = add nuw nsw i64 %_23.i.i, %157
  %160 = add nuw nsw <4 x i64> %158, %154
  %_98.i107 = lshr i64 %159, 51
  %161 = extractelement <4 x i64> %160, i64 0
  %_100.i108 = lshr i64 %161, 51
  %162 = extractelement <4 x i64> %160, i64 1
  %_102.i109 = lshr i64 %162, 51
  %163 = extractelement <4 x i64> %160, i64 2
  %_104.i110 = lshr i64 %163, 51
  %164 = extractelement <4 x i64> %160, i64 3
  %_106.i111 = lshr i64 %164, 51
  %165 = and i64 %159, 2251799813685247
  %166 = and i64 %161, 2251799813685247
  %167 = and i64 %162, 2251799813685247
  %168 = and i64 %163, 2251799813685247
  %169 = and i64 %164, 2251799813685247
  %_108.i112 = mul nuw nsw i64 %_106.i111, 19
  %170 = add nuw nsw i64 %_108.i112, %165
  %171 = add nuw nsw i64 %_98.i107, %166
  %172 = add nuw nsw i64 %167, %_100.i108
  %173 = add nuw nsw i64 %168, %_102.i109
  %174 = add nuw nsw i64 %169, %_104.i110
  %_4.i113 = add nuw nsw i64 %170, 19
  %175 = lshr i64 %_4.i113, 51
  %_6.i114 = add nuw nsw i64 %175, %171
  %176 = lshr i64 %_6.i114, 51
  %_8.i115 = add nuw nsw i64 %176, %172
  %177 = lshr i64 %_8.i115, 51
  %_10.i116 = add nuw nsw i64 %177, %173
  %178 = lshr i64 %_10.i116, 51
  %_12.i117 = add nuw nsw i64 %178, %174
  %179 = lshr i64 %_12.i117, 51
  %_14.i118 = mul nuw nsw i64 %179, 19
  %180 = add nuw nsw i64 %_14.i118, %170
  %_15.i119 = lshr i64 %180, 51
  %181 = add nuw nsw i64 %_15.i119, %171
  %_17.i120 = lshr i64 %181, 51
  %182 = add nuw nsw i64 %_17.i120, %172
  %183 = and i64 %181, 2251799813685247
  %_19.i121 = lshr i64 %182, 51
  %184 = add nuw nsw i64 %_19.i121, %173
  %185 = and i64 %182, 2251799813685247
  %_21.i122 = lshr i64 %184, 51
  %186 = add nuw nsw i64 %_21.i122, %174
  %187 = and i64 %184, 2251799813685247
  %188 = and i64 %186, 2251799813685247
  %189 = trunc i64 %180 to i8
  store i8 %189, ptr %_9.i1, align 1, !alias.scope !43, !noalias !46
  %_24.i123 = lshr i64 %180, 8
  %190 = trunc i64 %_24.i123 to i8
  store i8 %190, ptr %119, align 1, !alias.scope !43, !noalias !46
  %_26.i124 = lshr i64 %180, 16
  %191 = trunc i64 %_26.i124 to i8
  store i8 %191, ptr %120, align 1, !alias.scope !43, !noalias !46
  %_28.i125 = lshr i64 %180, 24
  %192 = trunc i64 %_28.i125 to i8
  store i8 %192, ptr %121, align 1, !alias.scope !43, !noalias !46
  %_30.i126 = lshr i64 %180, 32
  %193 = trunc i64 %_30.i126 to i8
  store i8 %193, ptr %122, align 1, !alias.scope !43, !noalias !46
  %_32.i127 = lshr i64 %180, 40
  %194 = trunc i64 %_32.i127 to i8
  store i8 %194, ptr %123, align 1, !alias.scope !43, !noalias !46
  %195 = lshr i64 %180, 48
  %_35.i128 = and i64 %195, 7
  %_37.i129 = shl nuw nsw i64 %183, 3
  %_34.i130 = or disjoint i64 %_37.i129, %_35.i128
  %196 = trunc i64 %_34.i130 to i8
  store i8 %196, ptr %124, align 1, !alias.scope !43, !noalias !46
  %_39.i131 = lshr i64 %181, 5
  %197 = trunc i64 %_39.i131 to i8
  store i8 %197, ptr %125, align 1, !alias.scope !43, !noalias !46
  %_41.i132 = lshr i64 %181, 13
  %198 = trunc i64 %_41.i132 to i8
  store i8 %198, ptr %126, align 1, !alias.scope !43, !noalias !46
  %_43.i133 = lshr i64 %181, 21
  %199 = trunc i64 %_43.i133 to i8
  store i8 %199, ptr %127, align 1, !alias.scope !43, !noalias !46
  %_45.i134 = lshr i64 %181, 29
  %200 = trunc i64 %_45.i134 to i8
  store i8 %200, ptr %128, align 1, !alias.scope !43, !noalias !46
  %_47.i135 = lshr i64 %181, 37
  %201 = trunc i64 %_47.i135 to i8
  store i8 %201, ptr %129, align 1, !alias.scope !43, !noalias !46
  %_50.i136 = lshr i64 %183, 45
  %_52.i137 = shl nuw nsw i64 %185, 6
  %_49.i138 = or disjoint i64 %_52.i137, %_50.i136
  %202 = trunc i64 %_49.i138 to i8
  store i8 %202, ptr %130, align 1, !alias.scope !43, !noalias !46
  %_54.i139 = lshr i64 %182, 2
  %203 = trunc i64 %_54.i139 to i8
  store i8 %203, ptr %131, align 1, !alias.scope !43, !noalias !46
  %_56.i140 = lshr i64 %182, 10
  %204 = trunc i64 %_56.i140 to i8
  store i8 %204, ptr %132, align 1, !alias.scope !43, !noalias !46
  %_58.i141 = lshr i64 %182, 18
  %205 = trunc i64 %_58.i141 to i8
  store i8 %205, ptr %133, align 1, !alias.scope !43, !noalias !46
  %_60.i142 = lshr i64 %182, 26
  %206 = trunc i64 %_60.i142 to i8
  store i8 %206, ptr %134, align 1, !alias.scope !43, !noalias !46
  %_62.i143 = lshr i64 %182, 34
  %207 = trunc i64 %_62.i143 to i8
  store i8 %207, ptr %135, align 1, !alias.scope !43, !noalias !46
  %_64.i144 = lshr i64 %182, 42
  %208 = trunc i64 %_64.i144 to i8
  store i8 %208, ptr %136, align 1, !alias.scope !43, !noalias !46
  %_67.i145 = lshr i64 %185, 50
  %_69.i146 = shl nuw nsw i64 %187, 1
  %_66.i147 = or disjoint i64 %_69.i146, %_67.i145
  %209 = trunc i64 %_66.i147 to i8
  store i8 %209, ptr %137, align 1, !alias.scope !43, !noalias !46
  %_71.i148 = lshr i64 %184, 7
  %210 = trunc i64 %_71.i148 to i8
  store i8 %210, ptr %138, align 1, !alias.scope !43, !noalias !46
  %_73.i149 = lshr i64 %184, 15
  %211 = trunc i64 %_73.i149 to i8
  store i8 %211, ptr %139, align 1, !alias.scope !43, !noalias !46
  %_75.i150 = lshr i64 %184, 23
  %212 = trunc i64 %_75.i150 to i8
  store i8 %212, ptr %140, align 1, !alias.scope !43, !noalias !46
  %_77.i151 = lshr i64 %184, 31
  %213 = trunc i64 %_77.i151 to i8
  store i8 %213, ptr %141, align 1, !alias.scope !43, !noalias !46
  %_79.i152 = lshr i64 %184, 39
  %214 = trunc i64 %_79.i152 to i8
  store i8 %214, ptr %142, align 1, !alias.scope !43, !noalias !46
  %_82.i153 = lshr i64 %187, 47
  %_84.i154 = shl nuw nsw i64 %188, 4
  %_81.i155 = or disjoint i64 %_84.i154, %_82.i153
  %215 = trunc i64 %_81.i155 to i8
  store i8 %215, ptr %143, align 1, !alias.scope !43, !noalias !46
  %_86.i156 = lshr i64 %186, 4
  %216 = trunc i64 %_86.i156 to i8
  store i8 %216, ptr %144, align 1, !alias.scope !43, !noalias !46
  %_88.i157 = lshr i64 %186, 12
  %217 = trunc i64 %_88.i157 to i8
  store i8 %217, ptr %145, align 1, !alias.scope !43, !noalias !46
  %_90.i158 = lshr i64 %186, 20
  %218 = trunc i64 %_90.i158 to i8
  store i8 %218, ptr %146, align 1, !alias.scope !43, !noalias !46
  %_92.i159 = lshr i64 %186, 28
  %219 = trunc i64 %_92.i159 to i8
  store i8 %219, ptr %147, align 1, !alias.scope !43, !noalias !46
  %_94.i160 = lshr i64 %186, 36
  %220 = trunc i64 %_94.i160 to i8
  store i8 %220, ptr %148, align 1, !alias.scope !43, !noalias !46
  %_96.i161 = lshr i64 %188, 44
  %221 = trunc nuw nsw i64 %_96.i161 to i8
  store i8 %221, ptr %149, align 1, !alias.scope !43, !noalias !46
  %_0.i3 = call fastcc noundef i8 @_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519(ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) %_5.i2, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) %_9.i1) #9
  call void @llvm.lifetime.end.p0(ptr nonnull %_9.i1), !noalias !29
  call void @llvm.lifetime.end.p0(ptr nonnull %_5.i2), !noalias !29
  call void @llvm.lifetime.start.p0(ptr nonnull %_32)
  call void @llvm.lifetime.start.p0(ptr nonnull %_34)
  store i64 %159, ptr %_34, align 8, !alias.scope !48, !noalias !51
  store <4 x i64> %160, ptr %output.sroa.6.0._0.sroa_idx.i24, align 8, !alias.scope !48, !noalias !51
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %_32, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_34, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(40) @alloc_4a840e2d409aa262ab906382f915ac1f) #8
  call void @llvm.lifetime.start.p0(ptr nonnull %_5.i29), !noalias !53
  tail call void @llvm.experimental.noalias.scope.decl(metadata !57)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !60)
  %limbs.sroa.0.0.copyload.i290 = load i64, ptr %check, align 8, !alias.scope !60, !noalias !62
  %limbs.sroa.19.0.copyload.i292 = load i64, ptr %limbs.sroa.19.0.self.sroa_idx.i, align 8, !alias.scope !60, !noalias !62
  %limbs.sroa.37.0.copyload.i294 = load i64, ptr %limbs.sroa.37.0.self.sroa_idx.i, align 8, !alias.scope !60, !noalias !62
  %limbs.sroa.56.0.copyload.i296 = load i64, ptr %limbs.sroa.56.0.self.sroa_idx.i, align 8, !alias.scope !60, !noalias !62
  %limbs.sroa.74.0.copyload.i298 = load i64, ptr %limbs.sroa.74.0.self.sroa_idx.i, align 8, !alias.scope !60, !noalias !62
  %_98.i299 = lshr i64 %limbs.sroa.0.0.copyload.i290, 51
  %_100.i300 = lshr i64 %limbs.sroa.19.0.copyload.i292, 51
  %_102.i301 = lshr i64 %limbs.sroa.37.0.copyload.i294, 51
  %_104.i302 = lshr i64 %limbs.sroa.56.0.copyload.i296, 51
  %_106.i303 = lshr i64 %limbs.sroa.74.0.copyload.i298, 51
  %222 = and i64 %limbs.sroa.0.0.copyload.i290, 2251799813685247
  %223 = and i64 %limbs.sroa.19.0.copyload.i292, 2251799813685247
  %224 = and i64 %limbs.sroa.37.0.copyload.i294, 2251799813685247
  %225 = and i64 %limbs.sroa.56.0.copyload.i296, 2251799813685247
  %226 = and i64 %limbs.sroa.74.0.copyload.i298, 2251799813685247
  %_108.i304 = mul nuw nsw i64 %_106.i303, 19
  %227 = add nuw nsw i64 %_108.i304, %222
  %228 = add nuw nsw i64 %223, %_98.i299
  %229 = add nuw nsw i64 %224, %_100.i300
  %230 = add nuw nsw i64 %225, %_102.i301
  %231 = add nuw nsw i64 %226, %_104.i302
  %_4.i305 = add nuw nsw i64 %227, 19
  %232 = lshr i64 %_4.i305, 51
  %_6.i306 = add nuw nsw i64 %232, %228
  %233 = lshr i64 %_6.i306, 51
  %_8.i307 = add nuw nsw i64 %233, %229
  %234 = lshr i64 %_8.i307, 51
  %_10.i308 = add nuw nsw i64 %234, %230
  %235 = lshr i64 %_10.i308, 51
  %_12.i309 = add nuw nsw i64 %235, %231
  %236 = lshr i64 %_12.i309, 51
  %_14.i310 = mul nuw nsw i64 %236, 19
  %237 = add nuw nsw i64 %_14.i310, %227
  %_15.i311 = lshr i64 %237, 51
  %238 = add nuw nsw i64 %_15.i311, %228
  %_17.i312 = lshr i64 %238, 51
  %239 = add nuw nsw i64 %_17.i312, %229
  %240 = and i64 %238, 2251799813685247
  %_19.i313 = lshr i64 %239, 51
  %241 = add nuw nsw i64 %_19.i313, %230
  %242 = and i64 %239, 2251799813685247
  %_21.i314 = lshr i64 %241, 51
  %243 = add nuw nsw i64 %_21.i314, %231
  %244 = and i64 %241, 2251799813685247
  %245 = and i64 %243, 2251799813685247
  %246 = trunc i64 %237 to i8
  store i8 %246, ptr %_5.i29, align 1, !alias.scope !57, !noalias !63
  %_24.i315 = lshr i64 %237, 8
  %247 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 1
  %248 = trunc i64 %_24.i315 to i8
  store i8 %248, ptr %247, align 1, !alias.scope !57, !noalias !63
  %_26.i316 = lshr i64 %237, 16
  %249 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 2
  %250 = trunc i64 %_26.i316 to i8
  store i8 %250, ptr %249, align 1, !alias.scope !57, !noalias !63
  %_28.i317 = lshr i64 %237, 24
  %251 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 3
  %252 = trunc i64 %_28.i317 to i8
  store i8 %252, ptr %251, align 1, !alias.scope !57, !noalias !63
  %_30.i318 = lshr i64 %237, 32
  %253 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 4
  %254 = trunc i64 %_30.i318 to i8
  store i8 %254, ptr %253, align 1, !alias.scope !57, !noalias !63
  %_32.i319 = lshr i64 %237, 40
  %255 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 5
  %256 = trunc i64 %_32.i319 to i8
  store i8 %256, ptr %255, align 1, !alias.scope !57, !noalias !63
  %257 = lshr i64 %237, 48
  %_35.i320 = and i64 %257, 7
  %_37.i321 = shl nuw nsw i64 %240, 3
  %_34.i322 = or disjoint i64 %_37.i321, %_35.i320
  %258 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 6
  %259 = trunc i64 %_34.i322 to i8
  store i8 %259, ptr %258, align 1, !alias.scope !57, !noalias !63
  %_39.i323 = lshr i64 %238, 5
  %260 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 7
  %261 = trunc i64 %_39.i323 to i8
  store i8 %261, ptr %260, align 1, !alias.scope !57, !noalias !63
  %_41.i324 = lshr i64 %238, 13
  %262 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 8
  %263 = trunc i64 %_41.i324 to i8
  store i8 %263, ptr %262, align 1, !alias.scope !57, !noalias !63
  %_43.i325 = lshr i64 %238, 21
  %264 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 9
  %265 = trunc i64 %_43.i325 to i8
  store i8 %265, ptr %264, align 1, !alias.scope !57, !noalias !63
  %_45.i326 = lshr i64 %238, 29
  %266 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 10
  %267 = trunc i64 %_45.i326 to i8
  store i8 %267, ptr %266, align 1, !alias.scope !57, !noalias !63
  %_47.i327 = lshr i64 %238, 37
  %268 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 11
  %269 = trunc i64 %_47.i327 to i8
  store i8 %269, ptr %268, align 1, !alias.scope !57, !noalias !63
  %_50.i328 = lshr i64 %240, 45
  %_52.i329 = shl nuw nsw i64 %242, 6
  %_49.i330 = or disjoint i64 %_52.i329, %_50.i328
  %270 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 12
  %271 = trunc i64 %_49.i330 to i8
  store i8 %271, ptr %270, align 1, !alias.scope !57, !noalias !63
  %_54.i331 = lshr i64 %239, 2
  %272 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 13
  %273 = trunc i64 %_54.i331 to i8
  store i8 %273, ptr %272, align 1, !alias.scope !57, !noalias !63
  %_56.i332 = lshr i64 %239, 10
  %274 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 14
  %275 = trunc i64 %_56.i332 to i8
  store i8 %275, ptr %274, align 1, !alias.scope !57, !noalias !63
  %_58.i333 = lshr i64 %239, 18
  %276 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 15
  %277 = trunc i64 %_58.i333 to i8
  store i8 %277, ptr %276, align 1, !alias.scope !57, !noalias !63
  %_60.i334 = lshr i64 %239, 26
  %278 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 16
  %279 = trunc i64 %_60.i334 to i8
  store i8 %279, ptr %278, align 1, !alias.scope !57, !noalias !63
  %_62.i335 = lshr i64 %239, 34
  %280 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 17
  %281 = trunc i64 %_62.i335 to i8
  store i8 %281, ptr %280, align 1, !alias.scope !57, !noalias !63
  %_64.i336 = lshr i64 %239, 42
  %282 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 18
  %283 = trunc i64 %_64.i336 to i8
  store i8 %283, ptr %282, align 1, !alias.scope !57, !noalias !63
  %_67.i337 = lshr i64 %242, 50
  %_69.i338 = shl nuw nsw i64 %244, 1
  %_66.i339 = or disjoint i64 %_69.i338, %_67.i337
  %284 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 19
  %285 = trunc i64 %_66.i339 to i8
  store i8 %285, ptr %284, align 1, !alias.scope !57, !noalias !63
  %_71.i340 = lshr i64 %241, 7
  %286 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 20
  %287 = trunc i64 %_71.i340 to i8
  store i8 %287, ptr %286, align 1, !alias.scope !57, !noalias !63
  %_73.i341 = lshr i64 %241, 15
  %288 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 21
  %289 = trunc i64 %_73.i341 to i8
  store i8 %289, ptr %288, align 1, !alias.scope !57, !noalias !63
  %_75.i342 = lshr i64 %241, 23
  %290 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 22
  %291 = trunc i64 %_75.i342 to i8
  store i8 %291, ptr %290, align 1, !alias.scope !57, !noalias !63
  %_77.i343 = lshr i64 %241, 31
  %292 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 23
  %293 = trunc i64 %_77.i343 to i8
  store i8 %293, ptr %292, align 1, !alias.scope !57, !noalias !63
  %_79.i344 = lshr i64 %241, 39
  %294 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 24
  %295 = trunc i64 %_79.i344 to i8
  store i8 %295, ptr %294, align 1, !alias.scope !57, !noalias !63
  %_82.i345 = lshr i64 %244, 47
  %_84.i346 = shl nuw nsw i64 %245, 4
  %_81.i347 = or disjoint i64 %_84.i346, %_82.i345
  %296 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 25
  %297 = trunc i64 %_81.i347 to i8
  store i8 %297, ptr %296, align 1, !alias.scope !57, !noalias !63
  %_86.i348 = lshr i64 %243, 4
  %298 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 26
  %299 = trunc i64 %_86.i348 to i8
  store i8 %299, ptr %298, align 1, !alias.scope !57, !noalias !63
  %_88.i349 = lshr i64 %243, 12
  %300 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 27
  %301 = trunc i64 %_88.i349 to i8
  store i8 %301, ptr %300, align 1, !alias.scope !57, !noalias !63
  %_90.i350 = lshr i64 %243, 20
  %302 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 28
  %303 = trunc i64 %_90.i350 to i8
  store i8 %303, ptr %302, align 1, !alias.scope !57, !noalias !63
  %_92.i351 = lshr i64 %243, 28
  %304 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 29
  %305 = trunc i64 %_92.i351 to i8
  store i8 %305, ptr %304, align 1, !alias.scope !57, !noalias !63
  %_94.i352 = lshr i64 %243, 36
  %306 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 30
  %307 = trunc i64 %_94.i352 to i8
  store i8 %307, ptr %306, align 1, !alias.scope !57, !noalias !63
  %_96.i353 = lshr i64 %245, 44
  %308 = getelementptr inbounds nuw i8, ptr %_5.i29, i64 31
  %309 = trunc nuw nsw i64 %_96.i353 to i8
  store i8 %309, ptr %308, align 1, !alias.scope !57, !noalias !63
  call void @llvm.lifetime.start.p0(ptr nonnull %_9.i28), !noalias !53
  tail call void @llvm.experimental.noalias.scope.decl(metadata !64)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !67)
  %limbs.sroa.0.0.copyload.i226 = load i64, ptr %_32, align 8, !alias.scope !67, !noalias !69
  %limbs.sroa.19.0.self.sroa_idx.i227 = getelementptr inbounds nuw i8, ptr %_32, i64 8
  %limbs.sroa.19.0.copyload.i228 = load i64, ptr %limbs.sroa.19.0.self.sroa_idx.i227, align 8, !alias.scope !67, !noalias !69
  %limbs.sroa.37.0.self.sroa_idx.i229 = getelementptr inbounds nuw i8, ptr %_32, i64 16
  %limbs.sroa.37.0.copyload.i230 = load i64, ptr %limbs.sroa.37.0.self.sroa_idx.i229, align 8, !alias.scope !67, !noalias !69
  %limbs.sroa.56.0.self.sroa_idx.i231 = getelementptr inbounds nuw i8, ptr %_32, i64 24
  %limbs.sroa.56.0.copyload.i232 = load i64, ptr %limbs.sroa.56.0.self.sroa_idx.i231, align 8, !alias.scope !67, !noalias !69
  %limbs.sroa.74.0.self.sroa_idx.i233 = getelementptr inbounds nuw i8, ptr %_32, i64 32
  %limbs.sroa.74.0.copyload.i234 = load i64, ptr %limbs.sroa.74.0.self.sroa_idx.i233, align 8, !alias.scope !67, !noalias !69
  %_98.i235 = lshr i64 %limbs.sroa.0.0.copyload.i226, 51
  %_100.i236 = lshr i64 %limbs.sroa.19.0.copyload.i228, 51
  %_102.i237 = lshr i64 %limbs.sroa.37.0.copyload.i230, 51
  %_104.i238 = lshr i64 %limbs.sroa.56.0.copyload.i232, 51
  %_106.i239 = lshr i64 %limbs.sroa.74.0.copyload.i234, 51
  %310 = and i64 %limbs.sroa.0.0.copyload.i226, 2251799813685247
  %311 = and i64 %limbs.sroa.19.0.copyload.i228, 2251799813685247
  %312 = and i64 %limbs.sroa.37.0.copyload.i230, 2251799813685247
  %313 = and i64 %limbs.sroa.56.0.copyload.i232, 2251799813685247
  %314 = and i64 %limbs.sroa.74.0.copyload.i234, 2251799813685247
  %_108.i240 = mul nuw nsw i64 %_106.i239, 19
  %315 = add nuw nsw i64 %_108.i240, %310
  %316 = add nuw nsw i64 %311, %_98.i235
  %317 = add nuw nsw i64 %312, %_100.i236
  %318 = add nuw nsw i64 %313, %_102.i237
  %319 = add nuw nsw i64 %314, %_104.i238
  %_4.i241 = add nuw nsw i64 %315, 19
  %320 = lshr i64 %_4.i241, 51
  %_6.i242 = add nuw nsw i64 %320, %316
  %321 = lshr i64 %_6.i242, 51
  %_8.i243 = add nuw nsw i64 %321, %317
  %322 = lshr i64 %_8.i243, 51
  %_10.i244 = add nuw nsw i64 %322, %318
  %323 = lshr i64 %_10.i244, 51
  %_12.i245 = add nuw nsw i64 %323, %319
  %324 = lshr i64 %_12.i245, 51
  %_14.i246 = mul nuw nsw i64 %324, 19
  %325 = add nuw nsw i64 %_14.i246, %315
  %_15.i247 = lshr i64 %325, 51
  %326 = add nuw nsw i64 %_15.i247, %316
  %_17.i248 = lshr i64 %326, 51
  %327 = add nuw nsw i64 %_17.i248, %317
  %328 = and i64 %326, 2251799813685247
  %_19.i249 = lshr i64 %327, 51
  %329 = add nuw nsw i64 %_19.i249, %318
  %330 = and i64 %327, 2251799813685247
  %_21.i250 = lshr i64 %329, 51
  %331 = add nuw nsw i64 %_21.i250, %319
  %332 = and i64 %329, 2251799813685247
  %333 = and i64 %331, 2251799813685247
  %334 = trunc i64 %325 to i8
  store i8 %334, ptr %_9.i28, align 1, !alias.scope !64, !noalias !70
  %_24.i251 = lshr i64 %325, 8
  %335 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 1
  %336 = trunc i64 %_24.i251 to i8
  store i8 %336, ptr %335, align 1, !alias.scope !64, !noalias !70
  %_26.i252 = lshr i64 %325, 16
  %337 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 2
  %338 = trunc i64 %_26.i252 to i8
  store i8 %338, ptr %337, align 1, !alias.scope !64, !noalias !70
  %_28.i253 = lshr i64 %325, 24
  %339 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 3
  %340 = trunc i64 %_28.i253 to i8
  store i8 %340, ptr %339, align 1, !alias.scope !64, !noalias !70
  %_30.i254 = lshr i64 %325, 32
  %341 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 4
  %342 = trunc i64 %_30.i254 to i8
  store i8 %342, ptr %341, align 1, !alias.scope !64, !noalias !70
  %_32.i255 = lshr i64 %325, 40
  %343 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 5
  %344 = trunc i64 %_32.i255 to i8
  store i8 %344, ptr %343, align 1, !alias.scope !64, !noalias !70
  %345 = lshr i64 %325, 48
  %_35.i256 = and i64 %345, 7
  %_37.i257 = shl nuw nsw i64 %328, 3
  %_34.i258 = or disjoint i64 %_37.i257, %_35.i256
  %346 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 6
  %347 = trunc i64 %_34.i258 to i8
  store i8 %347, ptr %346, align 1, !alias.scope !64, !noalias !70
  %_39.i259 = lshr i64 %326, 5
  %348 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 7
  %349 = trunc i64 %_39.i259 to i8
  store i8 %349, ptr %348, align 1, !alias.scope !64, !noalias !70
  %_41.i260 = lshr i64 %326, 13
  %350 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 8
  %351 = trunc i64 %_41.i260 to i8
  store i8 %351, ptr %350, align 1, !alias.scope !64, !noalias !70
  %_43.i261 = lshr i64 %326, 21
  %352 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 9
  %353 = trunc i64 %_43.i261 to i8
  store i8 %353, ptr %352, align 1, !alias.scope !64, !noalias !70
  %_45.i262 = lshr i64 %326, 29
  %354 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 10
  %355 = trunc i64 %_45.i262 to i8
  store i8 %355, ptr %354, align 1, !alias.scope !64, !noalias !70
  %_47.i263 = lshr i64 %326, 37
  %356 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 11
  %357 = trunc i64 %_47.i263 to i8
  store i8 %357, ptr %356, align 1, !alias.scope !64, !noalias !70
  %_50.i264 = lshr i64 %328, 45
  %_52.i265 = shl nuw nsw i64 %330, 6
  %_49.i266 = or disjoint i64 %_52.i265, %_50.i264
  %358 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 12
  %359 = trunc i64 %_49.i266 to i8
  store i8 %359, ptr %358, align 1, !alias.scope !64, !noalias !70
  %_54.i267 = lshr i64 %327, 2
  %360 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 13
  %361 = trunc i64 %_54.i267 to i8
  store i8 %361, ptr %360, align 1, !alias.scope !64, !noalias !70
  %_56.i268 = lshr i64 %327, 10
  %362 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 14
  %363 = trunc i64 %_56.i268 to i8
  store i8 %363, ptr %362, align 1, !alias.scope !64, !noalias !70
  %_58.i269 = lshr i64 %327, 18
  %364 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 15
  %365 = trunc i64 %_58.i269 to i8
  store i8 %365, ptr %364, align 1, !alias.scope !64, !noalias !70
  %_60.i270 = lshr i64 %327, 26
  %366 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 16
  %367 = trunc i64 %_60.i270 to i8
  store i8 %367, ptr %366, align 1, !alias.scope !64, !noalias !70
  %_62.i271 = lshr i64 %327, 34
  %368 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 17
  %369 = trunc i64 %_62.i271 to i8
  store i8 %369, ptr %368, align 1, !alias.scope !64, !noalias !70
  %_64.i272 = lshr i64 %327, 42
  %370 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 18
  %371 = trunc i64 %_64.i272 to i8
  store i8 %371, ptr %370, align 1, !alias.scope !64, !noalias !70
  %_67.i273 = lshr i64 %330, 50
  %_69.i274 = shl nuw nsw i64 %332, 1
  %_66.i275 = or disjoint i64 %_69.i274, %_67.i273
  %372 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 19
  %373 = trunc i64 %_66.i275 to i8
  store i8 %373, ptr %372, align 1, !alias.scope !64, !noalias !70
  %_71.i276 = lshr i64 %329, 7
  %374 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 20
  %375 = trunc i64 %_71.i276 to i8
  store i8 %375, ptr %374, align 1, !alias.scope !64, !noalias !70
  %_73.i277 = lshr i64 %329, 15
  %376 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 21
  %377 = trunc i64 %_73.i277 to i8
  store i8 %377, ptr %376, align 1, !alias.scope !64, !noalias !70
  %_75.i278 = lshr i64 %329, 23
  %378 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 22
  %379 = trunc i64 %_75.i278 to i8
  store i8 %379, ptr %378, align 1, !alias.scope !64, !noalias !70
  %_77.i279 = lshr i64 %329, 31
  %380 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 23
  %381 = trunc i64 %_77.i279 to i8
  store i8 %381, ptr %380, align 1, !alias.scope !64, !noalias !70
  %_79.i280 = lshr i64 %329, 39
  %382 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 24
  %383 = trunc i64 %_79.i280 to i8
  store i8 %383, ptr %382, align 1, !alias.scope !64, !noalias !70
  %_82.i281 = lshr i64 %332, 47
  %_84.i282 = shl nuw nsw i64 %333, 4
  %_81.i283 = or disjoint i64 %_84.i282, %_82.i281
  %384 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 25
  %385 = trunc i64 %_81.i283 to i8
  store i8 %385, ptr %384, align 1, !alias.scope !64, !noalias !70
  %_86.i284 = lshr i64 %331, 4
  %386 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 26
  %387 = trunc i64 %_86.i284 to i8
  store i8 %387, ptr %386, align 1, !alias.scope !64, !noalias !70
  %_88.i285 = lshr i64 %331, 12
  %388 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 27
  %389 = trunc i64 %_88.i285 to i8
  store i8 %389, ptr %388, align 1, !alias.scope !64, !noalias !70
  %_90.i286 = lshr i64 %331, 20
  %390 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 28
  %391 = trunc i64 %_90.i286 to i8
  store i8 %391, ptr %390, align 1, !alias.scope !64, !noalias !70
  %_92.i287 = lshr i64 %331, 28
  %392 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 29
  %393 = trunc i64 %_92.i287 to i8
  store i8 %393, ptr %392, align 1, !alias.scope !64, !noalias !70
  %_94.i288 = lshr i64 %331, 36
  %394 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 30
  %395 = trunc i64 %_94.i288 to i8
  store i8 %395, ptr %394, align 1, !alias.scope !64, !noalias !70
  %_96.i289 = lshr i64 %333, 44
  %396 = getelementptr inbounds nuw i8, ptr %_9.i28, i64 31
  %397 = trunc nuw nsw i64 %_96.i289 to i8
  store i8 %397, ptr %396, align 1, !alias.scope !64, !noalias !70
  %_0.i30 = call fastcc noundef i8 @_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519(ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) %_5.i29, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) %_9.i28) #9
  call void @llvm.lifetime.end.p0(ptr nonnull %_9.i28), !noalias !53
  call void @llvm.lifetime.end.p0(ptr nonnull %_5.i29), !noalias !53
  call void @llvm.lifetime.end.p0(ptr nonnull %_34)
  call void @llvm.lifetime.end.p0(ptr nonnull %_32)
  call void @llvm.lifetime.start.p0(ptr nonnull %r_prime)
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %r_prime, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(40) @alloc_4a840e2d409aa262ab906382f915ac1f, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %r) #8
  %_46 = or i8 %_0.i30, %_0.i3
  %_47 = tail call noundef i8 @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519(i8 noundef %_46) #10
  %_11.i = zext i8 %_47 to i64
  %_10.i = sub nsw i64 0, %_11.i
  %_5.i31 = getelementptr inbounds nuw i8, ptr %r, i64 8
  %398 = getelementptr inbounds nuw i8, ptr %r_prime, i64 8
  %_7.i = getelementptr inbounds nuw i8, ptr %r, i64 24
  %399 = getelementptr inbounds nuw i8, ptr %r_prime, i64 24
  %400 = load <2 x i64>, ptr %r, align 16
  %401 = load <2 x i64>, ptr %r_prime, align 16, !alias.scope !71, !noalias !74
  %402 = load <2 x i64>, ptr %_5.i31, align 8
  %403 = load <2 x i64>, ptr %398, align 8, !alias.scope !71, !noalias !74
  %404 = xor <2 x i64> %401, %400
  %405 = xor <2 x i64> %403, %402
  %406 = insertelement <2 x i64> poison, i64 %_10.i, i64 0
  %407 = shufflevector <2 x i64> %406, <2 x i64> poison, <2 x i32> zeroinitializer
  %408 = and <2 x i64> %404, %407
  %409 = and <2 x i64> %405, %407
  %410 = xor <2 x i64> %408, %400
  %411 = extractelement <2 x i64> %410, i64 0
  %412 = xor <2 x i64> %409, %402
  %413 = extractelement <2 x i64> %412, i64 1
  %_98.i363 = lshr i64 %411, 51
  %414 = extractelement <2 x i64> %412, i64 0
  %_100.i364 = lshr i64 %414, 51
  %_102.i365 = lshr i64 %413, 51
  %415 = and i64 %411, 2251799813685247
  %416 = and i64 %414, 2251799813685247
  %417 = and i64 %413, 2251799813685247
  %418 = add nuw nsw i64 %416, %_98.i363
  %419 = add nuw nsw i64 %417, %_100.i364
  %_3.i.i43 = sub i64 2251799813684944, %411
  %420 = sub <2 x i64> <i64 36028797018963664, i64 36028797018963952>, %410
  %421 = sub <2 x i64> splat (i64 2251799813685232), %412
  %422 = lshr <2 x i64> %420, splat (i64 51)
  %423 = and i64 %_3.i.i43, 2251799813685247
  %424 = and <2 x i64> %421, splat (i64 2251799813685247)
  %425 = add nuw nsw <2 x i64> %424, %422
  %426 = xor <2 x i64> %425, %412
  %427 = load <2 x i64>, ptr %_7.i, align 8
  %428 = load <2 x i64>, ptr %399, align 8, !alias.scope !71, !noalias !74
  %429 = xor <2 x i64> %428, %427
  %430 = and <2 x i64> %429, %407
  %431 = xor <2 x i64> %430, %427
  %432 = extractelement <2 x i64> %431, i64 1
  %433 = extractelement <2 x i64> %431, i64 0
  %_104.i366 = lshr i64 %433, 51
  %_106.i367 = lshr i64 %432, 51
  %434 = and i64 %433, 2251799813685247
  %435 = and i64 %432, 2251799813685247
  %_108.i368 = mul nuw nsw i64 %_106.i367, 19
  %436 = add nuw nsw i64 %435, %_104.i366
  %_11.i.i47 = sub i64 36028797018963952, %432
  %437 = sub <2 x i64> splat (i64 2251799813685232), %431
  %_21.i.i52 = lshr i64 %_11.i.i47, 51
  %438 = shufflevector <2 x i64> %412, <2 x i64> %431, <2 x i32> <i32 1, i32 2>
  %439 = sub <2 x i64> splat (i64 36028797018963952), %438
  %440 = and <2 x i64> %437, splat (i64 2251799813685247)
  %_23.i.i53 = mul nuw nsw i64 %_21.i.i52, 19
  %441 = add nuw nsw i64 %_108.i368, %415
  %442 = add nuw nsw i64 %434, %_102.i365
  %_4.i369 = add nuw nsw i64 %441, 19
  %443 = lshr i64 %_4.i369, 51
  %_6.i370 = add nuw nsw i64 %418, %443
  %444 = lshr i64 %_6.i370, 51
  %_8.i371 = add nuw nsw i64 %419, %444
  %445 = lshr i64 %_8.i371, 51
  %_10.i372 = add nuw nsw i64 %442, %445
  %446 = lshr i64 %_10.i372, 51
  %_12.i373 = add nuw nsw i64 %436, %446
  %447 = lshr i64 %_12.i373, 51
  %448 = add nuw nsw i64 %447, %441
  %449 = trunc i64 %448 to i8
  %_4.i = and i8 %449, 1
  %_6.i33 = tail call noundef i8 @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519(i8 noundef %_4.i) #10
  %450 = lshr <2 x i64> %439, splat (i64 51)
  %451 = add nuw nsw i64 %_23.i.i53, %423
  %452 = add nuw nsw <2 x i64> %440, %450
  %_11.i58 = zext i8 %_6.i33 to i64
  %_10.i59 = sub nsw i64 0, %_11.i58
  %_13.i62 = xor i64 %451, %411
  %_12.i63 = and i64 %_13.i62, %_10.i59
  %453 = xor i64 %_12.i63, %411
  store i64 %453, ptr %r, align 16
  %454 = insertelement <2 x i64> poison, i64 %_10.i59, i64 0
  %455 = shufflevector <2 x i64> %454, <2 x i64> poison, <2 x i32> zeroinitializer
  %456 = and <2 x i64> %426, %455
  %457 = xor <2 x i64> %456, %412
  store <2 x i64> %457, ptr %_5.i31, align 8
  %458 = xor <2 x i64> %452, %431
  %459 = and <2 x i64> %458, %455
  %460 = xor <2 x i64> %459, %431
  store <2 x i64> %460, ptr %_7.i, align 8
  %_52 = or i8 %_0.i3, %_0.i
  %_53 = tail call noundef i8 @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519(i8 noundef %_52) #10
  store i8 %_53, ptr %_0, align 8
  %461 = getelementptr inbounds nuw i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %461, ptr noundef nonnull align 16 dereferenceable(40) %r, i64 40, i1 false)
  call void @llvm.lifetime.end.p0(ptr nonnull %r_prime)
  call void @llvm.lifetime.end.p0(ptr nonnull %check)
  call void @llvm.lifetime.end.p0(ptr nonnull %v7)
  call void @llvm.lifetime.end.p0(ptr nonnull %v3)
  ret void
}

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable
declare hidden fastcc void @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement518pow22501(ptr dead_on_unwind noalias nofree noundef nonnull writable writeonly align 8 captures(none) dereferenceable(80) initializes((0, 80)), ptr noalias nofree noundef nonnull readonly align 8 captures(none) dereferenceable(40)) unnamed_addr #2

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable
declare void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([40 x i8]) align 8 captures(none) dereferenceable(40), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40), i32 noundef) unnamed_addr #2

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
declare void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([32 x i8]) align 1 captures(none) dereferenceable(32) initializes((0, 32)), ptr dead_on_return noalias nofree noundef readonly align 8 captures(none) dereferenceable(40)) unnamed_addr #3

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
declare void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([40 x i8]) align 8 captures(none) dereferenceable(40) initializes((0, 40)), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40)) unnamed_addr #3

; Function Attrs: inlinehint mustprogress nofree norecurse nounwind nonlazybind willreturn memory(argmem: read, inaccessiblemem: readwrite) uwtable
declare hidden fastcc noundef i8 @_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519(ptr noalias nofree noundef nonnull readonly captures(none), ptr noalias nofree noundef nonnull readonly captures(none)) unnamed_addr #4

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #5

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #6

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #5

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite)
declare void @llvm.experimental.noalias.scope.decl(metadata) #7

attributes #0 = { mustprogress nofree noinline norecurse nounwind nonlazybind willreturn memory(inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nofree norecurse nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #4 = { inlinehint mustprogress nofree norecurse nounwind nonlazybind willreturn memory(argmem: read, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #5 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #6 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #7 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite) }
attributes #8 = { nounwind }
attributes #9 = { inlinehint nounwind }
attributes #10 = { noinline nounwind }

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
!12 = !{!13, !15}
!13 = distinct !{!13, !14, !"_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement517pow_p58: %t21"}
!14 = distinct !{!14, !"_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement517pow_p58"}
!15 = distinct !{!15, !14, !"_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement517pow_p58: %self"}
!16 = !{!13}
!17 = !{!18, !20}
!18 = distinct !{!18, !19, !"_RNvXs0_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement51NtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq: %self"}
!19 = distinct !{!19, !"_RNvXs0_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement51NtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq"}
!20 = distinct !{!20, !19, !"_RNvXs0_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement51NtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq: %other"}
!21 = !{!22}
!22 = distinct !{!22, !23, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes: %s"}
!23 = distinct !{!23, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes"}
!24 = !{!25}
!25 = distinct !{!25, !23, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes: %self"}
!26 = !{!22, !20}
!27 = !{!25, !20}
!28 = !{!18}
!29 = !{!30, !32}
!30 = distinct !{!30, !31, !"_RNvXs0_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement51NtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq: %self"}
!31 = distinct !{!31, !"_RNvXs0_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement51NtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq"}
!32 = distinct !{!32, !31, !"_RNvXs0_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement51NtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq: %other"}
!33 = !{!34}
!34 = distinct !{!34, !35, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes: %s"}
!35 = distinct !{!35, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes"}
!36 = !{!37, !32}
!37 = distinct !{!37, !35, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes: %self"}
!38 = !{!39}
!39 = distinct !{!39, !40, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Neg3neg: %self"}
!40 = distinct !{!40, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Neg3neg"}
!41 = !{!42}
!42 = distinct !{!42, !40, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Neg3neg: %_0"}
!43 = !{!44}
!44 = distinct !{!44, !45, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes: %s"}
!45 = distinct !{!45, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes"}
!46 = !{!47, !30}
!47 = distinct !{!47, !45, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes: %self"}
!48 = !{!49}
!49 = distinct !{!49, !50, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Neg3neg: %_0"}
!50 = distinct !{!50, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Neg3neg"}
!51 = !{!52}
!52 = distinct !{!52, !50, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Neg3neg: %self"}
!53 = !{!54, !56}
!54 = distinct !{!54, !55, !"_RNvXs0_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement51NtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq: %self"}
!55 = distinct !{!55, !"_RNvXs0_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement51NtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq"}
!56 = distinct !{!56, !55, !"_RNvXs0_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement51NtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq: %other"}
!57 = !{!58}
!58 = distinct !{!58, !59, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes: %s"}
!59 = distinct !{!59, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes"}
!60 = !{!61}
!61 = distinct !{!61, !59, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes: %self"}
!62 = !{!58, !56}
!63 = !{!61, !56}
!64 = !{!65}
!65 = distinct !{!65, !66, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes: %s"}
!66 = distinct !{!66, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes"}
!67 = !{!68}
!68 = distinct !{!68, !66, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes: %self"}
!69 = !{!65, !54}
!70 = !{!68, !54}
!71 = !{!72}
!72 = distinct !{!72, !73, !"_RNvXs7_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51NtCsh8VEmffyqhs_6subtle23ConditionallySelectable18conditional_assign: %other"}
!73 = distinct !{!73, !"_RNvXs7_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51NtCsh8VEmffyqhs_6subtle23ConditionallySelectable18conditional_assign"}
!74 = !{!75}
!75 = distinct !{!75, !73, !"_RNvXs7_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement51NtCsh8VEmffyqhs_6subtle23ConditionallySelectable18conditional_assign: %self"}
