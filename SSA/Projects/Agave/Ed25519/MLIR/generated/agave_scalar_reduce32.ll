; ModuleID = '/home/nine/Documents/anza-code/.lmf-rir-ed25519/SSA/Projects/Agave/Ed25519/MLIR/generated/agave_scalar_reduce32.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree noinline norecurse nounwind nonlazybind willreturn memory(inaccessiblemem: readwrite) uwtable
declare noundef i8 @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519(i8 noundef) unnamed_addr #0

; Function Attrs: nofree norecurse nounwind nonlazybind uwtable
define hidden fastcc void @_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar6reduce(ptr dead_on_unwind noalias nofree noundef nonnull writable writeonly align 1 captures(none) dereferenceable(32) initializes((0, 32)) %scalar, ptr noalias nofree noundef nonnull readonly captures(none) dereferenceable(32) %self) unnamed_addr #1 personality ptr @rust_eh_personality {
start:
  %_2.i62.sroa.0 = alloca i64, align 8
  %_2.i62.sroa.4 = alloca i64, align 8
  %_2.i62.sroa.5 = alloca i64, align 8
  %_2.i62.sroa.6 = alloca i64, align 8
  %_2.i62.sroa.7 = alloca i64, align 8
  %_2.i54.sroa.0 = alloca i64, align 8
  %_2.i54.sroa.4 = alloca i64, align 8
  %_2.i54.sroa.5 = alloca i64, align 8
  %_2.i54.sroa.6 = alloca i64, align 8
  %_2.i54.sroa.7 = alloca i64, align 8
  %words.sroa.0.i.i = alloca i64, align 8
  %words.sroa.7.i.i = alloca i64, align 8
  %words.sroa.11.i.i = alloca i64, align 8
  %words.sroa.15.i.i = alloca i64, align 8
  %x_mod_l.sroa.0 = alloca i64, align 8
  %x_mod_l.sroa.5 = alloca i64, align 8
  %x_mod_l.sroa.7 = alloca i64, align 8
  %x_mod_l.sroa.9 = alloca i64, align 8
  %x_mod_l.sroa.11 = alloca i64, align 8
  %xR.sroa.0 = alloca i128, align 16
  %xR.sroa.5 = alloca i128, align 16
  %xR.sroa.7 = alloca i128, align 16
  %xR.sroa.9 = alloca i128, align 16
  %xR.sroa.11 = alloca i128, align 16
  %xR.sroa.13 = alloca i128, align 16
  %xR.sroa.15 = alloca i128, align 16
  %xR.sroa.17 = alloca i128, align 16
  %xR.sroa.19 = alloca i128, align 16
  %x.sroa.0 = alloca i64, align 8
  %x.sroa.5 = alloca i64, align 8
  %x.sroa.7 = alloca i64, align 8
  %x.sroa.9 = alloca i64, align 8
  %x.sroa.11 = alloca i64, align 8
  call void @llvm.lifetime.start.p0(ptr nonnull %x.sroa.0)
  call void @llvm.lifetime.start.p0(ptr nonnull %x.sroa.5)
  call void @llvm.lifetime.start.p0(ptr nonnull %x.sroa.7)
  call void @llvm.lifetime.start.p0(ptr nonnull %x.sroa.9)
  call void @llvm.lifetime.start.p0(ptr nonnull %x.sroa.11)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !4)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !7)
  call void @llvm.lifetime.start.p0(ptr nonnull %words.sroa.0.i.i)
  call void @llvm.lifetime.start.p0(ptr nonnull %words.sroa.7.i.i)
  call void @llvm.lifetime.start.p0(ptr nonnull %words.sroa.11.i.i)
  call void @llvm.lifetime.start.p0(ptr nonnull %words.sroa.15.i.i)
  %_9.i.i = load i32, ptr %self, align 1, !alias.scope !10, !noalias !11
  %0 = zext i32 %_9.i.i to i64
  %1 = getelementptr inbounds nuw i8, ptr %self, i64 4
  %_9.4.i.i = load i8, ptr %1, align 1, !alias.scope !10, !noalias !11, !noundef !14
  %_8.4.i.i = zext i8 %_9.4.i.i to i64
  %_7.4.i.i = shl nuw nsw i64 %_8.4.i.i, 32
  %2 = or disjoint i64 %_7.4.i.i, %0
  %3 = getelementptr inbounds nuw i8, ptr %self, i64 5
  %_9.5.i.i = load i8, ptr %3, align 1, !alias.scope !10, !noalias !11, !noundef !14
  %_8.5.i.i = zext i8 %_9.5.i.i to i64
  %_7.5.i.i = shl nuw nsw i64 %_8.5.i.i, 40
  %4 = or disjoint i64 %2, %_7.5.i.i
  %5 = getelementptr inbounds nuw i8, ptr %self, i64 6
  %_9.6.i.i = load i8, ptr %5, align 1, !alias.scope !10, !noalias !11, !noundef !14
  %_8.6.i.i = zext i8 %_9.6.i.i to i64
  %_7.6.i.i = shl nuw nsw i64 %_8.6.i.i, 48
  %6 = or disjoint i64 %4, %_7.6.i.i
  %7 = getelementptr inbounds nuw i8, ptr %self, i64 7
  %_9.7.i.i = load i8, ptr %7, align 1, !alias.scope !10, !noalias !11, !noundef !14
  %_8.7.i.i = zext i8 %_9.7.i.i to i64
  %_7.7.i.i = shl nuw i64 %_8.7.i.i, 56
  %8 = or disjoint i64 %_7.7.i.i, %6
  %9 = getelementptr inbounds nuw i8, ptr %self, i64 8
  %_9.112.i.i = load i32, ptr %9, align 1, !alias.scope !10, !noalias !11
  %10 = zext i32 %_9.112.i.i to i64
  %11 = getelementptr inbounds nuw i8, ptr %self, i64 12
  %_9.4.1.i.i = load i8, ptr %11, align 1, !alias.scope !10, !noalias !11, !noundef !14
  %_8.4.1.i.i = zext i8 %_9.4.1.i.i to i64
  %_7.4.1.i.i = shl nuw nsw i64 %_8.4.1.i.i, 32
  %12 = or disjoint i64 %_7.4.1.i.i, %10
  %13 = getelementptr inbounds nuw i8, ptr %self, i64 13
  %_9.5.1.i.i = load i8, ptr %13, align 1, !alias.scope !10, !noalias !11, !noundef !14
  %_8.5.1.i.i = zext i8 %_9.5.1.i.i to i64
  %_7.5.1.i.i = shl nuw nsw i64 %_8.5.1.i.i, 40
  %14 = getelementptr inbounds nuw i8, ptr %self, i64 14
  %_9.6.1.i.i = load i16, ptr %14, align 1, !alias.scope !10, !noalias !11
  %15 = zext i16 %_9.6.1.i.i to i64
  %16 = shl nuw i64 %15, 48
  %17 = or disjoint i64 %16, %_7.5.1.i.i
  %18 = or disjoint i64 %17, %12
  store i64 %18, ptr %words.sroa.7.i.i, align 8, !noalias !15
  %19 = getelementptr inbounds nuw i8, ptr %self, i64 16
  %_9.214.i.i = load i16, ptr %19, align 1, !alias.scope !10, !noalias !11
  %20 = zext i16 %_9.214.i.i to i64
  %21 = getelementptr inbounds nuw i8, ptr %self, i64 18
  %_9.2.2.i.i = load i8, ptr %21, align 1, !alias.scope !10, !noalias !11, !noundef !14
  %_8.2.2.i.i = zext i8 %_9.2.2.i.i to i64
  %_7.2.2.i.i = shl nuw nsw i64 %_8.2.2.i.i, 16
  %22 = or disjoint i64 %_7.2.2.i.i, %20
  %23 = getelementptr inbounds nuw i8, ptr %self, i64 19
  %_9.3.2.i.i = load i8, ptr %23, align 1, !alias.scope !10, !noalias !11, !noundef !14
  %_8.3.2.i.i = zext i8 %_9.3.2.i.i to i64
  %_7.3.2.i.i = shl nuw nsw i64 %_8.3.2.i.i, 24
  %24 = or disjoint i64 %22, %_7.3.2.i.i
  %25 = getelementptr inbounds nuw i8, ptr %self, i64 20
  %_9.4.2.i.i = load i32, ptr %25, align 1, !alias.scope !10, !noalias !11
  %26 = zext i32 %_9.4.2.i.i to i64
  %27 = shl nuw i64 %26, 32
  %28 = or disjoint i64 %27, %24
  store i64 %28, ptr %words.sroa.11.i.i, align 8, !noalias !15
  %29 = getelementptr inbounds nuw i8, ptr %self, i64 24
  %_9.316.i.i = load i8, ptr %29, align 1, !alias.scope !10, !noalias !11, !noundef !14
  %_8.317.i.i = zext i8 %_9.316.i.i to i64
  %30 = getelementptr inbounds nuw i8, ptr %self, i64 25
  %_9.1.3.i.i = load i8, ptr %30, align 1, !alias.scope !10, !noalias !11, !noundef !14
  %_8.1.3.i.i = zext i8 %_9.1.3.i.i to i64
  %_7.1.3.i.i = shl nuw nsw i64 %_8.1.3.i.i, 8
  %31 = or disjoint i64 %_7.1.3.i.i, %_8.317.i.i
  %32 = getelementptr inbounds nuw i8, ptr %self, i64 26
  %_9.2.3.i.i = load i32, ptr %32, align 1, !alias.scope !10, !noalias !11
  %33 = zext i32 %_9.2.3.i.i to i64
  %34 = shl nuw nsw i64 %33, 16
  %35 = getelementptr inbounds nuw i8, ptr %self, i64 30
  %_9.6.3.i.i = load i16, ptr %35, align 1, !alias.scope !10, !noalias !11
  %36 = zext i16 %_9.6.3.i.i to i64
  %37 = shl nuw i64 %36, 48
  %38 = or disjoint i64 %37, %34
  %39 = or disjoint i64 %38, %31
  store i64 %39, ptr %words.sroa.15.i.i, align 8, !noalias !15
  store volatile i64 0, ptr %words.sroa.0.i.i, align 8, !alias.scope !16, !noalias !19
  fence syncscope("singlethread") seq_cst
  store volatile i64 0, ptr %words.sroa.7.i.i, align 8, !alias.scope !16, !noalias !19
  fence syncscope("singlethread") seq_cst
  store volatile i64 0, ptr %words.sroa.11.i.i, align 8, !alias.scope !16, !noalias !19
  fence syncscope("singlethread") seq_cst
  store volatile i64 0, ptr %words.sroa.15.i.i, align 8, !alias.scope !16, !noalias !19
  fence syncscope("singlethread") seq_cst
  %_36.i.i = lshr exact i64 %38, 16
  %_30.i.i = tail call i64 @llvm.fshl.i64(i64 %31, i64 %28, i64 36)
  %_24.i.i = tail call i64 @llvm.fshl.i64(i64 %24, i64 %17, i64 24)
  %40 = and i64 %_24.i.i, 4503599627370495
  %_18.i.i = tail call i64 @llvm.fshl.i64(i64 %12, i64 %8, i64 12)
  %41 = and i64 %6, 4503599627370495
  call void @llvm.lifetime.end.p0(ptr nonnull %words.sroa.0.i.i)
  call void @llvm.lifetime.end.p0(ptr nonnull %words.sroa.7.i.i)
  call void @llvm.lifetime.end.p0(ptr nonnull %words.sroa.11.i.i)
  call void @llvm.lifetime.end.p0(ptr nonnull %words.sroa.15.i.i)
  call void @llvm.lifetime.start.p0(ptr nonnull %xR.sroa.0)
  call void @llvm.lifetime.start.p0(ptr nonnull %xR.sroa.5)
  call void @llvm.lifetime.start.p0(ptr nonnull %xR.sroa.7)
  call void @llvm.lifetime.start.p0(ptr nonnull %xR.sroa.9)
  call void @llvm.lifetime.start.p0(ptr nonnull %xR.sroa.11)
  call void @llvm.lifetime.start.p0(ptr nonnull %xR.sroa.13)
  call void @llvm.lifetime.start.p0(ptr nonnull %xR.sroa.15)
  call void @llvm.lifetime.start.p0(ptr nonnull %xR.sroa.17)
  call void @llvm.lifetime.start.p0(ptr nonnull %xR.sroa.19)
  %_47.i = zext nneg i64 %41 to i128
  %_3.i = mul nuw nsw i128 %_47.i, 4302102966953709
  store i128 %_3.i, ptr %xR.sroa.0, align 16, !alias.scope !22, !noalias !25
  %_6.i = mul nuw nsw i128 %_47.i, 1049714374468698
  %_50.i = zext nneg i64 %_18.i.i to i128
  %_8.i = mul nuw nsw i128 %_50.i, 4302102966953709
  %42 = add nuw nsw i128 %_8.i, %_6.i
  store i128 %42, ptr %xR.sroa.5, align 16, !alias.scope !22, !noalias !25
  %_11.i = mul nuw nsw i128 %_47.i, 4503599278581019
  %_13.i = mul nuw nsw i128 %_50.i, 1049714374468698
  %_10.i = add nuw nsw i128 %_13.i, %_11.i
  %_52.i = zext nneg i64 %40 to i128
  %_14.i = mul nuw nsw i128 %_52.i, 4302102966953709
  %43 = add nuw nsw i128 %_10.i, %_14.i
  store i128 %43, ptr %xR.sroa.7, align 16, !alias.scope !22, !noalias !25
  %_18.i = mul nuw nsw i128 %_47.i, 4503599627370495
  %_20.i = mul nuw nsw i128 %_50.i, 4503599278581019
  %_17.i = add nuw nsw i128 %_20.i, %_18.i
  %_21.i = mul nuw nsw i128 %_52.i, 1049714374468698
  %_16.i = add nuw nsw i128 %_17.i, %_21.i
  %_54.i = zext nneg i64 %_30.i.i to i128
  %_22.i = mul nuw nsw i128 %_54.i, 4302102966953709
  %44 = add nuw nsw i128 %_16.i, %_22.i
  store i128 %44, ptr %xR.sroa.9, align 16, !alias.scope !22, !noalias !25
  %_27.i = mul nuw nsw i128 %_47.i, 17592186044415
  %_29.i = mul nuw nsw i128 %_50.i, 4503599627370495
  %_26.i = add nuw nsw i128 %_29.i, %_27.i
  %_30.i = mul nuw nsw i128 %_52.i, 4503599278581019
  %_25.i = add nuw nsw i128 %_26.i, %_30.i
  %_31.i = mul nuw nsw i128 %_54.i, 1049714374468698
  %_24.i = add nuw nsw i128 %_25.i, %_31.i
  %_56.i = zext nneg i64 %_36.i.i to i128
  %_32.i = mul nuw nsw i128 %_56.i, 4302102966953709
  %45 = add nuw nsw i128 %_24.i, %_32.i
  store i128 %45, ptr %xR.sroa.11, align 16, !alias.scope !22, !noalias !25
  %_36.i = mul nuw nsw i128 %_50.i, 17592186044415
  %_37.i = mul nuw nsw i128 %_52.i, 4503599627370495
  %_35.i = add nuw nsw i128 %_37.i, %_36.i
  %_38.i = mul nuw nsw i128 %_54.i, 4503599278581019
  %_34.i = add nuw nsw i128 %_35.i, %_38.i
  %_39.i = mul nuw nsw i128 %_56.i, 1049714374468698
  %46 = add nuw nsw i128 %_34.i, %_39.i
  store i128 %46, ptr %xR.sroa.13, align 16, !alias.scope !22, !noalias !25
  %_41.i = mul nuw nsw i128 %_52.i, 17592186044415
  %_42.i = mul nuw nsw i128 %_54.i, 4503599627370495
  %_40.i = add nuw nsw i128 %_42.i, %_41.i
  %_43.i = mul nuw nsw i128 %_56.i, 4503599278581019
  %47 = add nuw nsw i128 %_40.i, %_43.i
  store i128 %47, ptr %xR.sroa.15, align 16, !alias.scope !22, !noalias !25
  %_44.i = mul nuw nsw i128 %_54.i, 17592186044415
  %_45.i = mul nuw nsw i128 %_56.i, 4503599627370495
  %48 = add nuw nsw i128 %_45.i, %_44.i
  store i128 %48, ptr %xR.sroa.17, align 16, !alias.scope !22, !noalias !25
  %_46.i = mul nuw nsw i128 %_56.i, 17592186044415
  store i128 %_46.i, ptr %xR.sroa.19, align 16, !alias.scope !22, !noalias !25
  call void @llvm.lifetime.start.p0(ptr nonnull %x_mod_l.sroa.0)
  call void @llvm.lifetime.start.p0(ptr nonnull %x_mod_l.sroa.5)
  call void @llvm.lifetime.start.p0(ptr nonnull %x_mod_l.sroa.7)
  call void @llvm.lifetime.start.p0(ptr nonnull %x_mod_l.sroa.9)
  call void @llvm.lifetime.start.p0(ptr nonnull %x_mod_l.sroa.11)
  %_55.i = trunc i128 %_3.i to i64
  %_54.i1 = mul i64 %_55.i, 1439961107955227
  %n0.i = and i64 %_54.i1, 4503599627370495
  %_59.i = zext nneg i64 %n0.i to i128
  %_58.i = mul nuw nsw i128 %_59.i, 671914833335277
  %_57.i = add nuw nsw i128 %_58.i, %_3.i
  %carry.i = lshr i128 %_57.i, 52
  %_6.i3 = mul nuw nsw i128 %_59.i, 3916664325105025
  %_4.i2 = add nuw nsw i128 %_6.i3, %42
  %_3.i4 = add nuw nsw i128 %_4.i2, %carry.i
  %_62.i = trunc i128 %_3.i4 to i64
  %_61.i = mul i64 %_62.i, 1439961107955227
  %n1.i = and i64 %_61.i, 4503599627370495
  %_66.i = zext nneg i64 %n1.i to i128
  %_65.i = mul nuw nsw i128 %_66.i, 671914833335277
  %_64.i = add nuw nsw i128 %_65.i, %_3.i4
  %carry1.i = lshr i128 %_64.i, 52
  %_11.i7 = mul nuw nsw i128 %_59.i, 1367801
  %_12.i = mul nuw nsw i128 %_66.i, 3916664325105025
  %_9.i6 = add nuw nsw i128 %43, %_11.i7
  %_8.i8 = add nuw nsw i128 %_9.i6, %_12.i
  %_7.i = add nuw nsw i128 %_8.i8, %carry1.i
  %_69.i = trunc i128 %_7.i to i64
  %_68.i = mul i64 %_69.i, 1439961107955227
  %n2.i = and i64 %_68.i, 4503599627370495
  %_73.i = zext nneg i64 %n2.i to i128
  %_72.i = mul nuw nsw i128 %_73.i, 671914833335277
  %_71.i = add nuw nsw i128 %_72.i, %_7.i
  %carry2.i = lshr i128 %_71.i, 52
  %_17.i11 = mul nuw nsw i128 %_66.i, 1367801
  %_18.i13 = mul nuw nsw i128 %_73.i, 3916664325105025
  %_15.i10 = add nuw nsw i128 %_17.i11, %44
  %_14.i12 = add nuw nsw i128 %_15.i10, %_18.i13
  %_13.i14 = add nuw nsw i128 %_14.i12, %carry2.i
  %_76.i = trunc i128 %_13.i14 to i64
  %_75.i = mul i64 %_76.i, 1439961107955227
  %n3.i = and i64 %_75.i, 4503599627370495
  %_80.i = zext nneg i64 %n3.i to i128
  %_79.i = mul nuw nsw i128 %_80.i, 671914833335277
  %_78.i = add nuw nsw i128 %_79.i, %_13.i14
  %carry3.i = lshr i128 %_78.i, 52
  %_24.i17 = shl nuw nsw i128 %_59.i, 44
  %_25.i19 = mul nuw nsw i128 %_73.i, 1367801
  %_26.i21 = mul nuw nsw i128 %_80.i, 3916664325105025
  %_22.i16 = add nuw nsw i128 %45, %_24.i17
  %_21.i18 = add nuw nsw i128 %_22.i16, %_25.i19
  %_20.i20 = add nuw nsw i128 %_21.i18, %_26.i21
  %_19.i = add nuw nsw i128 %_20.i20, %carry3.i
  %_83.i = trunc i128 %_19.i to i64
  %_82.i = mul i64 %_83.i, 1439961107955227
  %n4.i = and i64 %_82.i, 4503599627370495
  %_87.i = zext nneg i64 %n4.i to i128
  %_86.i = mul nuw nsw i128 %_87.i, 671914833335277
  %_85.i = add nuw nsw i128 %_86.i, %_19.i
  %carry4.i = lshr i128 %_85.i, 52
  %_32.i24 = shl nuw nsw i128 %_66.i, 44
  %_33.i26 = mul nuw nsw i128 %_80.i, 1367801
  %_34.i27 = mul nuw nsw i128 %_87.i, 3916664325105025
  %_30.i23 = add nuw nsw i128 %46, %_32.i24
  %_29.i25 = add nuw nsw i128 %_30.i23, %_33.i26
  %_28.i = add nuw nsw i128 %_29.i25, %_34.i27
  %_27.i28 = add nuw nsw i128 %_28.i, %carry4.i
  %_89.i = trunc i128 %_27.i28 to i64
  %r0.i = and i64 %_89.i, 4503599627370495
  %carry5.i = lshr i128 %_27.i28, 52
  %_39.i31 = shl nuw nsw i128 %_73.i, 44
  %_40.i33 = mul nuw nsw i128 %_87.i, 1367801
  %_37.i30 = add nuw nsw i128 %_39.i31, %47
  %_36.i32 = add nuw nsw i128 %_37.i30, %_40.i33
  %_35.i34 = add nuw nsw i128 %_36.i32, %carry5.i
  %_92.i = trunc i128 %_35.i34 to i64
  %r1.i = and i64 %_92.i, 4503599627370495
  %carry6.i = lshr i128 %_35.i34, 52
  %_44.i37 = shl nuw nsw i128 %_80.i, 44
  %_42.i36 = add nuw nsw i128 %_44.i37, %48
  %_41.i38 = add nuw nsw i128 %_42.i36, %carry6.i
  %_95.i = trunc i128 %_41.i38 to i64
  %r2.i = and i64 %_95.i, 4503599627370495
  %carry7.i = lshr i128 %_41.i38, 52
  %_48.i = shl nuw nsw i128 %_87.i, 44
  %_46.i40 = add nuw nsw i128 %_48.i, %_46.i
  %_45.i41 = add nuw nsw i128 %_46.i40, %carry7.i
  %_98.i = trunc i128 %_45.i41 to i64
  %r3.i = and i64 %_98.i, 4503599627370495
  %carry8.i = lshr i128 %_45.i41, 52
  %r4.i = trunc nuw nsw i128 %carry8.i to i64
  %49 = add nsw i64 %r0.i, -671914833335277
  %50 = and i64 %49, 4503599627370495
  %_10.neg8.1.i = ashr i64 %49, 63
  %_8.neg.1.i = add nsw i64 %_10.neg8.1.i, -3916664325105025
  %51 = add nsw i64 %_8.neg.1.i, %r1.i
  %52 = and i64 %51, 4503599627370495
  %_10.neg8.2.i = ashr i64 %51, 63
  %_8.neg.2.i = add nsw i64 %_10.neg8.2.i, -1367801
  %53 = add nsw i64 %_8.neg.2.i, %r2.i
  %54 = and i64 %53, 4503599627370495
  %_10.neg8.3.i = ashr i64 %53, 63
  %_8.neg.3.i = add nsw i64 %r3.i, %_10.neg8.3.i
  %55 = and i64 %_8.neg.3.i, 4503599627370495
  %_10.neg8.4.i = ashr i64 %_8.neg.3.i, 63
  %_8.neg.4.i = add nsw i64 %r4.i, -17592186044416
  %56 = add nsw i64 %_8.neg.4.i, %_10.neg8.4.i
  %_17.i43 = lshr i64 %56, 63
  %_16.i44 = trunc nuw nsw i64 %_17.i43 to i8
  %_23.i45 = tail call noundef i8 @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519(i8 noundef %_16.i44) #6, !noalias !28
  %_20.i.i = zext i8 %_23.i45 to i64
  %_19.i.i = sub nsw i64 0, %_20.i.i
  %addend.i.i = and i64 %_19.i.i, 671914833335277
  %57 = add nuw nsw i64 %50, %addend.i.i
  %58 = and i64 %57, 4503599627370495
  %addend.1.i.i = and i64 %_19.i.i, 3916664325105025
  %_7.1.i.i = lshr i64 %57, 52
  %_6.1.i.i = add nuw nsw i64 %_7.1.i.i, %addend.1.i.i
  %59 = add nuw nsw i64 %_6.1.i.i, %52
  %60 = and i64 %59, 4503599627370495
  %addend.2.i.i = and i64 %_19.i.i, 1367801
  %_7.2.i.i = lshr i64 %59, 52
  %_6.2.i.i = add nuw nsw i64 %54, %addend.2.i.i
  %61 = add nuw nsw i64 %_6.2.i.i, %_7.2.i.i
  %62 = and i64 %61, 4503599627370495
  %_7.3.i.i = lshr i64 %61, 52
  %_6.3.i.i = add nuw nsw i64 %_7.3.i.i, %55
  %63 = and i64 %_6.3.i.i, 4503599627370495
  %addend.4.i.i = and i64 %_19.i.i, 17592186044416
  %_7.4.i.i46 = lshr i64 %_6.3.i.i, 52
  %_6.4.i.i = add nsw i64 %56, %addend.4.i.i
  %64 = add nsw i64 %_6.4.i.i, %_7.4.i.i46
  %65 = and i64 %64, 4503599627370495
  store i64 %58, ptr %x_mod_l.sroa.0, align 8, !alias.scope !31, !noalias !34
  store i64 %60, ptr %x_mod_l.sroa.5, align 8, !alias.scope !31, !noalias !34
  store i64 %62, ptr %x_mod_l.sroa.7, align 8, !alias.scope !31, !noalias !34
  store i64 %63, ptr %x_mod_l.sroa.9, align 8, !alias.scope !31, !noalias !34
  store i64 %65, ptr %x_mod_l.sroa.11, align 8, !alias.scope !31, !noalias !34
  %66 = trunc i64 %57 to i8
  %_3.i.i = lshr i64 %57, 8
  %67 = trunc i64 %_3.i.i to i8
  %_4.i.i = lshr i64 %57, 16
  %68 = trunc i64 %_4.i.i to i8
  %_5.i.i = lshr i64 %57, 24
  %69 = trunc i64 %_5.i.i to i8
  %_6.i.i = lshr i64 %57, 32
  %70 = trunc i64 %_6.i.i to i8
  %_7.i.i = lshr i64 %57, 40
  %71 = trunc i64 %_7.i.i to i8
  %_9.i.i47 = lshr i64 %58, 48
  %_10.i.i = shl nuw nsw i64 %60, 4
  %_8.i.i = or disjoint i64 %_10.i.i, %_9.i.i47
  %72 = trunc i64 %_8.i.i to i8
  %_12.i.i = lshr i64 %59, 4
  %73 = trunc i64 %_12.i.i to i8
  %_13.i.i = lshr i64 %59, 12
  %74 = trunc i64 %_13.i.i to i8
  %_14.i.i = lshr i64 %59, 20
  %75 = trunc i64 %_14.i.i to i8
  %_15.i.i = lshr i64 %59, 28
  %76 = trunc i64 %_15.i.i to i8
  %_16.i.i = lshr i64 %59, 36
  %77 = trunc i64 %_16.i.i to i8
  %_17.i.i = lshr i64 %59, 44
  %78 = trunc i64 %_17.i.i to i8
  %79 = trunc i64 %61 to i8
  %_19.i.i49 = lshr i64 %61, 8
  %80 = trunc i64 %_19.i.i49 to i8
  %_20.i.i50 = lshr i64 %61, 16
  %81 = trunc i64 %_20.i.i50 to i8
  %_21.i.i = lshr i64 %61, 24
  %82 = trunc i64 %_21.i.i to i8
  %_22.i.i = lshr i64 %61, 32
  %83 = trunc i64 %_22.i.i to i8
  %_23.i.i = lshr i64 %61, 40
  %84 = trunc i64 %_23.i.i to i8
  %_25.i.i = lshr i64 %62, 48
  %_26.i.i = shl nuw nsw i64 %_6.3.i.i, 4
  %_24.i.i51 = or disjoint i64 %_26.i.i, %_25.i.i
  %85 = trunc i64 %_24.i.i51 to i8
  %_28.i.i = lshr i64 %_6.3.i.i, 4
  %86 = trunc i64 %_28.i.i to i8
  %_29.i.i = lshr i64 %_6.3.i.i, 12
  %87 = trunc i64 %_29.i.i to i8
  %_30.i.i52 = lshr i64 %_6.3.i.i, 20
  %88 = trunc i64 %_30.i.i52 to i8
  %_31.i.i = lshr i64 %_6.3.i.i, 28
  %89 = trunc i64 %_31.i.i to i8
  %_32.i.i = lshr i64 %_6.3.i.i, 36
  %90 = trunc i64 %_32.i.i to i8
  %_33.i.i = lshr i64 %_6.3.i.i, 44
  %91 = trunc i64 %_33.i.i to i8
  %92 = trunc i64 %64 to i8
  %_35.i.i = lshr i64 %64, 8
  %93 = trunc i64 %_35.i.i to i8
  %_36.i.i53 = lshr i64 %64, 16
  %94 = trunc i64 %_36.i.i53 to i8
  %_37.i.i = lshr i64 %64, 24
  %95 = trunc i64 %_37.i.i to i8
  %_38.i.i = lshr i64 %64, 32
  %96 = trunc i64 %_38.i.i to i8
  %_39.i.i = lshr i64 %64, 40
  %97 = trunc i64 %_39.i.i to i8
  store i8 %66, ptr %scalar, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.4.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 1
  store i8 %67, ptr %_2.sroa.4.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.5.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 2
  store i8 %68, ptr %_2.sroa.5.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.6.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 3
  store i8 %69, ptr %_2.sroa.6.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.7.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 4
  store i8 %70, ptr %_2.sroa.7.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.8.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 5
  store i8 %71, ptr %_2.sroa.8.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.9.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 6
  store i8 %72, ptr %_2.sroa.9.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.10.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 7
  store i8 %73, ptr %_2.sroa.10.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.11.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 8
  store i8 %74, ptr %_2.sroa.11.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.12.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 9
  store i8 %75, ptr %_2.sroa.12.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.13.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 10
  store i8 %76, ptr %_2.sroa.13.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.14.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 11
  store i8 %77, ptr %_2.sroa.14.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.15.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 12
  store i8 %78, ptr %_2.sroa.15.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.16.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 13
  store i8 %79, ptr %_2.sroa.16.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.17.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 14
  store i8 %80, ptr %_2.sroa.17.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.18.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 15
  store i8 %81, ptr %_2.sroa.18.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.19.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 16
  store i8 %82, ptr %_2.sroa.19.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.20.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 17
  store i8 %83, ptr %_2.sroa.20.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.21.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 18
  store i8 %84, ptr %_2.sroa.21.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.22.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 19
  store i8 %85, ptr %_2.sroa.22.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.23.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 20
  store i8 %86, ptr %_2.sroa.23.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.24.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 21
  store i8 %87, ptr %_2.sroa.24.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.25.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 22
  store i8 %88, ptr %_2.sroa.25.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.26.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 23
  store i8 %89, ptr %_2.sroa.26.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.27.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 24
  store i8 %90, ptr %_2.sroa.27.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.28.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 25
  store i8 %91, ptr %_2.sroa.28.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.29.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 26
  store i8 %92, ptr %_2.sroa.29.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.30.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 27
  store i8 %93, ptr %_2.sroa.30.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.31.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 28
  store i8 %94, ptr %_2.sroa.31.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.32.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 29
  store i8 %95, ptr %_2.sroa.32.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.33.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 30
  store i8 %96, ptr %_2.sroa.33.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  %_2.sroa.34.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 31
  store i8 %97, ptr %_2.sroa.34.0._0.sroa_idx.i, align 1, !alias.scope !37, !noalias !40
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i54.sroa.0)
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i54.sroa.4)
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i54.sroa.5)
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i54.sroa.6)
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i54.sroa.7)
  store i64 0, ptr %_2.i54.sroa.0, align 8, !alias.scope !42, !noalias !45
  store i64 0, ptr %_2.i54.sroa.4, align 8, !alias.scope !42, !noalias !45
  store i64 0, ptr %_2.i54.sroa.5, align 8, !alias.scope !42, !noalias !45
  store i64 0, ptr %_2.i54.sroa.6, align 8, !alias.scope !42, !noalias !45
  store i64 0, ptr %_2.i54.sroa.7, align 8, !alias.scope !42, !noalias !45
  %_2.i54.sroa.0.0._2.i54.sroa.0.0._2.i54.sroa.0.0._2.i54.sroa.0.0.x.sroa.0.0.copyload = load volatile i64, ptr %_2.i54.sroa.0, align 8
  store volatile i64 %_2.i54.sroa.0.0._2.i54.sroa.0.0._2.i54.sroa.0.0._2.i54.sroa.0.0.x.sroa.0.0.copyload, ptr %x.sroa.0, align 8
  %_2.i54.sroa.4.0._2.i54.sroa.4.0._2.i54.sroa.4.0._2.i54.sroa.4.8.x.sroa.5.0.copyload = load volatile i64, ptr %_2.i54.sroa.4, align 8
  store volatile i64 %_2.i54.sroa.4.0._2.i54.sroa.4.0._2.i54.sroa.4.0._2.i54.sroa.4.8.x.sroa.5.0.copyload, ptr %x.sroa.5, align 8
  %_2.i54.sroa.5.0._2.i54.sroa.5.0._2.i54.sroa.5.0._2.i54.sroa.5.16.x.sroa.7.0.copyload = load volatile i64, ptr %_2.i54.sroa.5, align 8
  store volatile i64 %_2.i54.sroa.5.0._2.i54.sroa.5.0._2.i54.sroa.5.0._2.i54.sroa.5.16.x.sroa.7.0.copyload, ptr %x.sroa.7, align 8
  %_2.i54.sroa.6.0._2.i54.sroa.6.0._2.i54.sroa.6.0._2.i54.sroa.6.24.x.sroa.9.0.copyload = load volatile i64, ptr %_2.i54.sroa.6, align 8
  store volatile i64 %_2.i54.sroa.6.0._2.i54.sroa.6.0._2.i54.sroa.6.0._2.i54.sroa.6.24.x.sroa.9.0.copyload, ptr %x.sroa.9, align 8
  %_2.i54.sroa.7.0._2.i54.sroa.7.0._2.i54.sroa.7.0._2.i54.sroa.7.32.x.sroa.11.0.copyload = load volatile i64, ptr %_2.i54.sroa.7, align 8
  store volatile i64 %_2.i54.sroa.7.0._2.i54.sroa.7.0._2.i54.sroa.7.0._2.i54.sroa.7.32.x.sroa.11.0.copyload, ptr %x.sroa.11, align 8
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i54.sroa.0)
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i54.sroa.4)
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i54.sroa.5)
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i54.sroa.6)
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i54.sroa.7)
  fence syncscope("singlethread") seq_cst
  store volatile i128 0, ptr %xR.sroa.0, align 16, !alias.scope !48, !noalias !51
  fence syncscope("singlethread") seq_cst
  store volatile i128 0, ptr %xR.sroa.5, align 16, !alias.scope !48, !noalias !51
  fence syncscope("singlethread") seq_cst
  store volatile i128 0, ptr %xR.sroa.7, align 16, !alias.scope !48, !noalias !51
  fence syncscope("singlethread") seq_cst
  store volatile i128 0, ptr %xR.sroa.9, align 16, !alias.scope !48, !noalias !51
  fence syncscope("singlethread") seq_cst
  store volatile i128 0, ptr %xR.sroa.11, align 16, !alias.scope !48, !noalias !51
  fence syncscope("singlethread") seq_cst
  store volatile i128 0, ptr %xR.sroa.13, align 16, !alias.scope !48, !noalias !51
  fence syncscope("singlethread") seq_cst
  store volatile i128 0, ptr %xR.sroa.15, align 16, !alias.scope !48, !noalias !51
  fence syncscope("singlethread") seq_cst
  store volatile i128 0, ptr %xR.sroa.17, align 16, !alias.scope !48, !noalias !51
  fence syncscope("singlethread") seq_cst
  store volatile i128 0, ptr %xR.sroa.19, align 16, !alias.scope !48, !noalias !51
  fence syncscope("singlethread") seq_cst
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i62.sroa.0)
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i62.sroa.4)
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i62.sroa.5)
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i62.sroa.6)
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i62.sroa.7)
  store i64 0, ptr %_2.i62.sroa.0, align 8, !alias.scope !54, !noalias !57
  store i64 0, ptr %_2.i62.sroa.4, align 8, !alias.scope !54, !noalias !57
  store i64 0, ptr %_2.i62.sroa.5, align 8, !alias.scope !54, !noalias !57
  store i64 0, ptr %_2.i62.sroa.6, align 8, !alias.scope !54, !noalias !57
  store i64 0, ptr %_2.i62.sroa.7, align 8, !alias.scope !54, !noalias !57
  %_2.i62.sroa.0.0._2.i62.sroa.0.0._2.i62.sroa.0.0._2.i62.sroa.0.0.x_mod_l.sroa.0.0.copyload = load volatile i64, ptr %_2.i62.sroa.0, align 8
  store volatile i64 %_2.i62.sroa.0.0._2.i62.sroa.0.0._2.i62.sroa.0.0._2.i62.sroa.0.0.x_mod_l.sroa.0.0.copyload, ptr %x_mod_l.sroa.0, align 8
  %_2.i62.sroa.4.0._2.i62.sroa.4.0._2.i62.sroa.4.0._2.i62.sroa.4.8.x_mod_l.sroa.5.0.copyload = load volatile i64, ptr %_2.i62.sroa.4, align 8
  store volatile i64 %_2.i62.sroa.4.0._2.i62.sroa.4.0._2.i62.sroa.4.0._2.i62.sroa.4.8.x_mod_l.sroa.5.0.copyload, ptr %x_mod_l.sroa.5, align 8
  %_2.i62.sroa.5.0._2.i62.sroa.5.0._2.i62.sroa.5.0._2.i62.sroa.5.16.x_mod_l.sroa.7.0.copyload = load volatile i64, ptr %_2.i62.sroa.5, align 8
  store volatile i64 %_2.i62.sroa.5.0._2.i62.sroa.5.0._2.i62.sroa.5.0._2.i62.sroa.5.16.x_mod_l.sroa.7.0.copyload, ptr %x_mod_l.sroa.7, align 8
  %_2.i62.sroa.6.0._2.i62.sroa.6.0._2.i62.sroa.6.0._2.i62.sroa.6.24.x_mod_l.sroa.9.0.copyload = load volatile i64, ptr %_2.i62.sroa.6, align 8
  store volatile i64 %_2.i62.sroa.6.0._2.i62.sroa.6.0._2.i62.sroa.6.0._2.i62.sroa.6.24.x_mod_l.sroa.9.0.copyload, ptr %x_mod_l.sroa.9, align 8
  %_2.i62.sroa.7.0._2.i62.sroa.7.0._2.i62.sroa.7.0._2.i62.sroa.7.32.x_mod_l.sroa.11.0.copyload = load volatile i64, ptr %_2.i62.sroa.7, align 8
  store volatile i64 %_2.i62.sroa.7.0._2.i62.sroa.7.0._2.i62.sroa.7.0._2.i62.sroa.7.32.x_mod_l.sroa.11.0.copyload, ptr %x_mod_l.sroa.11, align 8
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i62.sroa.0)
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i62.sroa.4)
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i62.sroa.5)
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i62.sroa.6)
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i62.sroa.7)
  fence syncscope("singlethread") seq_cst
  call void @llvm.lifetime.end.p0(ptr nonnull %x_mod_l.sroa.0)
  call void @llvm.lifetime.end.p0(ptr nonnull %x_mod_l.sroa.5)
  call void @llvm.lifetime.end.p0(ptr nonnull %x_mod_l.sroa.7)
  call void @llvm.lifetime.end.p0(ptr nonnull %x_mod_l.sroa.9)
  call void @llvm.lifetime.end.p0(ptr nonnull %x_mod_l.sroa.11)
  call void @llvm.lifetime.end.p0(ptr nonnull %xR.sroa.0)
  call void @llvm.lifetime.end.p0(ptr nonnull %xR.sroa.5)
  call void @llvm.lifetime.end.p0(ptr nonnull %xR.sroa.7)
  call void @llvm.lifetime.end.p0(ptr nonnull %xR.sroa.9)
  call void @llvm.lifetime.end.p0(ptr nonnull %xR.sroa.11)
  call void @llvm.lifetime.end.p0(ptr nonnull %xR.sroa.13)
  call void @llvm.lifetime.end.p0(ptr nonnull %xR.sroa.15)
  call void @llvm.lifetime.end.p0(ptr nonnull %xR.sroa.17)
  call void @llvm.lifetime.end.p0(ptr nonnull %xR.sroa.19)
  call void @llvm.lifetime.end.p0(ptr nonnull %x.sroa.0)
  call void @llvm.lifetime.end.p0(ptr nonnull %x.sroa.5)
  call void @llvm.lifetime.end.p0(ptr nonnull %x.sroa.7)
  call void @llvm.lifetime.end.p0(ptr nonnull %x.sroa.9)
  call void @llvm.lifetime.end.p0(ptr nonnull %x.sroa.11)
  ret void
}

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #2

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #2

; Function Attrs: nonlazybind
declare i32 @rust_eh_personality(...) unnamed_addr #3

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.fshl.i64(i64, i64, i64) #4

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite)
declare void @llvm.experimental.noalias.scope.decl(metadata) #5

attributes #0 = { mustprogress nofree noinline norecurse nounwind nonlazybind willreturn memory(inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nofree norecurse nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #3 = { nonlazybind "target-cpu"="x86-64" }
attributes #4 = { nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none) }
attributes #5 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite) }
attributes #6 = { noinline nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{!5}
!5 = distinct !{!5, !6, !"_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar6unpack: %self"}
!6 = distinct !{!6, !"_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar6unpack"}
!7 = !{!8}
!8 = distinct !{!8, !9, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5210from_bytes: %bytes"}
!9 = distinct !{!9, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5210from_bytes"}
!10 = !{!8, !5}
!11 = !{!12, !13}
!12 = distinct !{!12, !9, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5210from_bytes: %_0"}
!13 = distinct !{!13, !6, !"_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar6unpack: %_0"}
!14 = !{}
!15 = !{!12, !8, !13, !5}
!16 = !{!17}
!17 = distinct !{!17, !18, !"_RNvXCs2F8OvSoAkiP_7zeroizeyNtB2_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519: %self"}
!18 = distinct !{!18, !"_RNvXCs2F8OvSoAkiP_7zeroizeyNtB2_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519"}
!19 = !{!20, !12, !8, !13, !5}
!20 = distinct !{!20, !21, !"_RNvXs4_Cs2F8OvSoAkiP_7zeroizeINtNtNtCsgxBkk5gSRhY_4core5slice4iter7IterMutyENtB5_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519: %self"}
!21 = distinct !{!21, !"_RNvXs4_Cs2F8OvSoAkiP_7zeroizeINtNtNtCsgxBkk5gSRhY_4core5slice4iter7IterMutyENtB5_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519"}
!22 = !{!23}
!23 = distinct !{!23, !24, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5212mul_internal: %z"}
!24 = distinct !{!24, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5212mul_internal"}
!25 = !{!26, !27}
!26 = distinct !{!26, !24, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5212mul_internal: %a"}
!27 = distinct !{!27, !24, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5212mul_internal: %b"}
!28 = !{!29}
!29 = distinct !{!29, !30, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5217montgomery_reduce: %limbs"}
!30 = distinct !{!30, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5217montgomery_reduce"}
!31 = !{!32}
!32 = distinct !{!32, !33, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar523sub: %_0"}
!33 = distinct !{!33, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar523sub"}
!34 = !{!35, !36, !29}
!35 = distinct !{!35, !33, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar523sub: %a"}
!36 = distinct !{!36, !33, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar523sub: %b"}
!37 = !{!38}
!38 = distinct !{!38, !39, !"_RNvMsp_NtCsjK63O35OHGN_14solana_ed255196scalarNtNtNtNtNtB7_7backend6serial3u646scalar8Scalar524pack: %_0"}
!39 = distinct !{!39, !"_RNvMsp_NtCsjK63O35OHGN_14solana_ed255196scalarNtNtNtNtNtB7_7backend6serial3u646scalar8Scalar524pack"}
!40 = !{!41}
!41 = distinct !{!41, !39, !"_RNvMsp_NtCsjK63O35OHGN_14solana_ed255196scalarNtNtNtNtNtB7_7backend6serial3u646scalar8Scalar524pack: %self"}
!42 = !{!43}
!43 = distinct !{!43, !44, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar52NtNtCsgxBkk5gSRhY_4core7default7Default7default: %_0"}
!44 = distinct !{!44, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar52NtNtCsgxBkk5gSRhY_4core7default7Default7default"}
!45 = !{!46}
!46 = distinct !{!46, !47, !"_RNvXCs2F8OvSoAkiP_7zeroizeNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalar8Scalar52NtB2_7Zeroize7zeroizeBy_: %self"}
!47 = distinct !{!47, !"_RNvXCs2F8OvSoAkiP_7zeroizeNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalar8Scalar52NtB2_7Zeroize7zeroizeBy_"}
!48 = !{!49}
!49 = distinct !{!49, !50, !"_RNvXCs2F8OvSoAkiP_7zeroizeoNtB2_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519: %self"}
!50 = distinct !{!50, !"_RNvXCs2F8OvSoAkiP_7zeroizeoNtB2_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519"}
!51 = !{!52}
!52 = distinct !{!52, !53, !"_RNvXs4_Cs2F8OvSoAkiP_7zeroizeINtNtNtCsgxBkk5gSRhY_4core5slice4iter7IterMutoENtB5_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519: %self"}
!53 = distinct !{!53, !"_RNvXs4_Cs2F8OvSoAkiP_7zeroizeINtNtNtCsgxBkk5gSRhY_4core5slice4iter7IterMutoENtB5_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519"}
!54 = !{!55}
!55 = distinct !{!55, !56, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar52NtNtCsgxBkk5gSRhY_4core7default7Default7default: %_0"}
!56 = distinct !{!56, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar52NtNtCsgxBkk5gSRhY_4core7default7Default7default"}
!57 = !{!58}
!58 = distinct !{!58, !59, !"_RNvXCs2F8OvSoAkiP_7zeroizeNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalar8Scalar52NtB2_7Zeroize7zeroizeBy_: %self"}
!59 = distinct !{!59, !"_RNvXCs2F8OvSoAkiP_7zeroizeNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalar8Scalar52NtB2_7Zeroize7zeroizeBy_"}
