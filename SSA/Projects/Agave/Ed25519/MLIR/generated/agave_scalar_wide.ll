; ModuleID = '/home/nine/Documents/anza-code/.lmf-rir-ed25519/SSA/Projects/Agave/Ed25519/MLIR/generated/agave_scalar_wide.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_b0a0adc7a7ee3d20b0509962c17b23d6 = internal unnamed_addr constant [40 x i8] c";\D1R\E9e\D2\09\00\9F\A6\BE\15\C7c\0D\00\04vh\CBe\BE\05\00\7F!=\C7\EE\DC\03\00\9A0|\1BA\09\00\00", align 8
@alloc_595ed8f9b6c4f781a4a1d10db150f124 = internal unnamed_addr constant [40 x i8] c"\ED\E6!g\BDH\0F\00Z\E4g\AC\B5\BA\03\00\1B\E55\EB\FF\FF\0F\00\FF\FF\FF\FF\FF\FF\0F\00\FF\FF\FF\FF\FF\0F\00\00", align 8

; Function Attrs: mustprogress nofree noinline norecurse nounwind nonlazybind willreturn memory(inaccessiblemem: readwrite) uwtable
declare noundef i8 @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519(i8 noundef) unnamed_addr #0

; Function Attrs: nofree norecurse nounwind nonlazybind uwtable
define void @_RNvMNtCsjK63O35OHGN_14solana_ed255196scalarNtB2_6Scalar25from_bytes_mod_order_wide(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([32 x i8]) align 1 captures(none) dereferenceable(32) initializes((0, 32)) %scalar, ptr noalias nofree noundef readonly captures(none) dereferenceable(64) %input) unnamed_addr #1 personality ptr @rust_eh_personality {
start:
  %_2.i.sroa.0 = alloca i64, align 8
  %_2.i.sroa.4 = alloca i64, align 8
  %_2.i.sroa.5 = alloca i64, align 8
  %_2.i.sroa.6 = alloca i64, align 8
  %_2.i.sroa.7 = alloca i64, align 8
  %_2.i5.i = alloca [40 x i8], align 8
  %_2.i.i = alloca [40 x i8], align 8
  %_68.i = alloca [40 x i8], align 8
  %_66.i = alloca [40 x i8], align 8
  %hi.i = alloca [40 x i8], align 8
  %lo.i = alloca [40 x i8], align 8
  %words.sroa.0.i = alloca i64, align 8
  %words.sroa.7.i = alloca i64, align 8
  %words.sroa.11.i = alloca i64, align 8
  %words.sroa.15.i = alloca i64, align 8
  %words.sroa.19.i = alloca i64, align 8
  %words.sroa.23.i = alloca i64, align 8
  %words.sroa.27.i = alloca i64, align 8
  %words.sroa.31.i = alloca i64, align 8
  %unpacked.sroa.0 = alloca i64, align 8
  %unpacked.sroa.5 = alloca i64, align 8
  %unpacked.sroa.7 = alloca i64, align 8
  %unpacked.sroa.9 = alloca i64, align 8
  %unpacked.sroa.11 = alloca i64, align 8
  call void @llvm.lifetime.start.p0(ptr nonnull %unpacked.sroa.0)
  call void @llvm.lifetime.start.p0(ptr nonnull %unpacked.sroa.5)
  call void @llvm.lifetime.start.p0(ptr nonnull %unpacked.sroa.7)
  call void @llvm.lifetime.start.p0(ptr nonnull %unpacked.sroa.9)
  call void @llvm.lifetime.start.p0(ptr nonnull %unpacked.sroa.11)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !4)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !7)
  call void @llvm.lifetime.start.p0(ptr nonnull %words.sroa.0.i)
  call void @llvm.lifetime.start.p0(ptr nonnull %words.sroa.7.i)
  call void @llvm.lifetime.start.p0(ptr nonnull %words.sroa.11.i)
  call void @llvm.lifetime.start.p0(ptr nonnull %words.sroa.15.i)
  call void @llvm.lifetime.start.p0(ptr nonnull %words.sroa.19.i)
  call void @llvm.lifetime.start.p0(ptr nonnull %words.sroa.23.i)
  call void @llvm.lifetime.start.p0(ptr nonnull %words.sroa.27.i)
  call void @llvm.lifetime.start.p0(ptr nonnull %words.sroa.31.i)
  %_9.i = load i32, ptr %input, align 1, !alias.scope !7, !noalias !4
  %0 = zext i32 %_9.i to i64
  %1 = getelementptr inbounds nuw i8, ptr %input, i64 4
  %_9.4.i = load i8, ptr %1, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.4.i = zext i8 %_9.4.i to i64
  %_7.4.i = shl nuw nsw i64 %_8.4.i, 32
  %2 = or disjoint i64 %_7.4.i, %0
  %3 = getelementptr inbounds nuw i8, ptr %input, i64 5
  %_9.5.i = load i8, ptr %3, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.5.i = zext i8 %_9.5.i to i64
  %_7.5.i = shl nuw nsw i64 %_8.5.i, 40
  %4 = or disjoint i64 %2, %_7.5.i
  %5 = getelementptr inbounds nuw i8, ptr %input, i64 6
  %_9.6.i = load i8, ptr %5, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.6.i = zext i8 %_9.6.i to i64
  %_7.6.i = shl nuw nsw i64 %_8.6.i, 48
  %6 = or disjoint i64 %4, %_7.6.i
  %7 = getelementptr inbounds nuw i8, ptr %input, i64 7
  %_9.7.i = load i8, ptr %7, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.7.i = zext i8 %_9.7.i to i64
  %_7.7.i = shl nuw i64 %_8.7.i, 56
  %8 = or disjoint i64 %_7.7.i, %6
  %9 = getelementptr inbounds nuw i8, ptr %input, i64 8
  %_9.18.i = load i32, ptr %9, align 1, !alias.scope !7, !noalias !4
  %10 = zext i32 %_9.18.i to i64
  %11 = getelementptr inbounds nuw i8, ptr %input, i64 12
  %_9.4.1.i = load i8, ptr %11, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.4.1.i = zext i8 %_9.4.1.i to i64
  %_7.4.1.i = shl nuw nsw i64 %_8.4.1.i, 32
  %12 = or disjoint i64 %_7.4.1.i, %10
  %13 = getelementptr inbounds nuw i8, ptr %input, i64 13
  %_9.5.1.i = load i8, ptr %13, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.5.1.i = zext i8 %_9.5.1.i to i64
  %_7.5.1.i = shl nuw nsw i64 %_8.5.1.i, 40
  %14 = getelementptr inbounds nuw i8, ptr %input, i64 14
  %_9.6.1.i = load i16, ptr %14, align 1, !alias.scope !7, !noalias !4
  %15 = zext i16 %_9.6.1.i to i64
  %16 = shl nuw i64 %15, 48
  %17 = or disjoint i64 %_7.5.1.i, %16
  %18 = or disjoint i64 %17, %12
  store i64 %18, ptr %words.sroa.7.i, align 8, !noalias !10
  %19 = getelementptr inbounds nuw i8, ptr %input, i64 16
  %_9.210.i = load i16, ptr %19, align 1, !alias.scope !7, !noalias !4
  %20 = zext i16 %_9.210.i to i64
  %21 = getelementptr inbounds nuw i8, ptr %input, i64 18
  %_9.2.2.i = load i8, ptr %21, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.2.2.i = zext i8 %_9.2.2.i to i64
  %_7.2.2.i = shl nuw nsw i64 %_8.2.2.i, 16
  %22 = or disjoint i64 %_7.2.2.i, %20
  %23 = getelementptr inbounds nuw i8, ptr %input, i64 19
  %_9.3.2.i = load i8, ptr %23, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.3.2.i = zext i8 %_9.3.2.i to i64
  %_7.3.2.i = shl nuw nsw i64 %_8.3.2.i, 24
  %24 = or disjoint i64 %22, %_7.3.2.i
  %25 = getelementptr inbounds nuw i8, ptr %input, i64 20
  %_9.4.2.i = load i16, ptr %25, align 1, !alias.scope !7, !noalias !4
  %26 = zext i16 %_9.4.2.i to i64
  %27 = shl nuw nsw i64 %26, 32
  %28 = getelementptr inbounds nuw i8, ptr %input, i64 22
  %_9.6.2.i = load i16, ptr %28, align 1, !alias.scope !7, !noalias !4
  %29 = zext i16 %_9.6.2.i to i64
  %30 = shl nuw i64 %29, 48
  %31 = or disjoint i64 %27, %30
  %32 = or disjoint i64 %31, %24
  store i64 %32, ptr %words.sroa.11.i, align 8, !noalias !10
  %33 = getelementptr inbounds nuw i8, ptr %input, i64 24
  %_9.312.i = load i8, ptr %33, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.313.i = zext i8 %_9.312.i to i64
  %34 = getelementptr inbounds nuw i8, ptr %input, i64 25
  %_9.1.3.i = load i8, ptr %34, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.1.3.i = zext i8 %_9.1.3.i to i64
  %_7.1.3.i = shl nuw nsw i64 %_8.1.3.i, 8
  %35 = or disjoint i64 %_7.1.3.i, %_8.313.i
  %36 = getelementptr inbounds nuw i8, ptr %input, i64 26
  %_9.2.3.i = load i16, ptr %36, align 1, !alias.scope !7, !noalias !4
  %37 = zext i16 %_9.2.3.i to i64
  %38 = shl nuw nsw i64 %37, 16
  %39 = getelementptr inbounds nuw i8, ptr %input, i64 28
  %_9.4.3.i = load i16, ptr %39, align 1, !alias.scope !7, !noalias !4
  %40 = zext i16 %_9.4.3.i to i64
  %41 = shl nuw nsw i64 %40, 32
  %42 = or disjoint i64 %38, %41
  %43 = getelementptr inbounds nuw i8, ptr %input, i64 30
  %_9.6.3.i = load i16, ptr %43, align 1, !alias.scope !7, !noalias !4
  %44 = zext i16 %_9.6.3.i to i64
  %45 = shl nuw i64 %44, 48
  %46 = or disjoint i64 %42, %45
  %47 = or disjoint i64 %46, %35
  store i64 %47, ptr %words.sroa.15.i, align 8, !noalias !10
  %48 = getelementptr inbounds nuw i8, ptr %input, i64 32
  %_9.414.i = load i8, ptr %48, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.415.i = zext i8 %_9.414.i to i64
  %49 = getelementptr inbounds nuw i8, ptr %input, i64 33
  %_9.1.4.i = load i8, ptr %49, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.1.4.i = zext i8 %_9.1.4.i to i64
  %_7.1.4.i = shl nuw nsw i64 %_8.1.4.i, 8
  %50 = getelementptr inbounds nuw i8, ptr %input, i64 34
  %_9.2.4.i = load i16, ptr %50, align 1, !alias.scope !7, !noalias !4
  %51 = zext i16 %_9.2.4.i to i64
  %52 = shl nuw nsw i64 %51, 16
  %53 = or disjoint i64 %_7.1.4.i, %52
  %54 = getelementptr inbounds nuw i8, ptr %input, i64 36
  %_9.4.4.i = load i16, ptr %54, align 1, !alias.scope !7, !noalias !4
  %55 = zext i16 %_9.4.4.i to i64
  %56 = shl nuw nsw i64 %55, 32
  %57 = or disjoint i64 %53, %56
  %58 = getelementptr inbounds nuw i8, ptr %input, i64 38
  %_9.6.4.i = load i16, ptr %58, align 1, !alias.scope !7, !noalias !4
  %59 = zext i16 %_9.6.4.i to i64
  %60 = shl nuw i64 %59, 48
  %61 = or disjoint i64 %57, %60
  %62 = or disjoint i64 %61, %_8.415.i
  store i64 %62, ptr %words.sroa.19.i, align 8, !noalias !10
  %63 = getelementptr inbounds nuw i8, ptr %input, i64 40
  %_9.516.i = load i32, ptr %63, align 1, !alias.scope !7, !noalias !4
  %64 = zext i32 %_9.516.i to i64
  %65 = getelementptr inbounds nuw i8, ptr %input, i64 44
  %_9.4.5.i = load i8, ptr %65, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.4.5.i = zext i8 %_9.4.5.i to i64
  %_7.4.5.i = shl nuw nsw i64 %_8.4.5.i, 32
  %66 = or disjoint i64 %_7.4.5.i, %64
  %67 = getelementptr inbounds nuw i8, ptr %input, i64 45
  %_9.5.5.i = load i8, ptr %67, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.5.5.i = zext i8 %_9.5.5.i to i64
  %_7.5.5.i = shl nuw nsw i64 %_8.5.5.i, 40
  %68 = or disjoint i64 %66, %_7.5.5.i
  %69 = getelementptr inbounds nuw i8, ptr %input, i64 46
  %_9.6.5.i = load i16, ptr %69, align 1, !alias.scope !7, !noalias !4
  %70 = zext i16 %_9.6.5.i to i64
  %71 = shl nuw i64 %70, 48
  %72 = or disjoint i64 %71, %68
  store i64 %72, ptr %words.sroa.23.i, align 8, !noalias !10
  %73 = getelementptr inbounds nuw i8, ptr %input, i64 48
  %_9.618.i = load i16, ptr %73, align 1, !alias.scope !7, !noalias !4
  %74 = zext i16 %_9.618.i to i64
  %75 = getelementptr inbounds nuw i8, ptr %input, i64 50
  %_9.2.6.i = load i8, ptr %75, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.2.6.i = zext i8 %_9.2.6.i to i64
  %_7.2.6.i = shl nuw nsw i64 %_8.2.6.i, 16
  %76 = or disjoint i64 %_7.2.6.i, %74
  %77 = getelementptr inbounds nuw i8, ptr %input, i64 51
  %_9.3.6.i = load i8, ptr %77, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.3.6.i = zext i8 %_9.3.6.i to i64
  %_7.3.6.i = shl nuw nsw i64 %_8.3.6.i, 24
  %78 = or disjoint i64 %76, %_7.3.6.i
  %79 = getelementptr inbounds nuw i8, ptr %input, i64 52
  %_9.4.6.i = load i16, ptr %79, align 1, !alias.scope !7, !noalias !4
  %80 = zext i16 %_9.4.6.i to i64
  %81 = shl nuw nsw i64 %80, 32
  %82 = getelementptr inbounds nuw i8, ptr %input, i64 54
  %_9.6.6.i = load i16, ptr %82, align 1, !alias.scope !7, !noalias !4
  %83 = zext i16 %_9.6.6.i to i64
  %84 = shl nuw i64 %83, 48
  %85 = or disjoint i64 %81, %84
  %86 = or disjoint i64 %85, %78
  store i64 %86, ptr %words.sroa.27.i, align 8, !noalias !10
  %87 = getelementptr inbounds nuw i8, ptr %input, i64 56
  %_9.720.i = load i16, ptr %87, align 1, !alias.scope !7, !noalias !4
  %88 = zext i16 %_9.720.i to i64
  %89 = getelementptr inbounds nuw i8, ptr %input, i64 58
  %_9.2.7.i = load i8, ptr %89, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.2.7.i = zext i8 %_9.2.7.i to i64
  %_7.2.7.i = shl nuw nsw i64 %_8.2.7.i, 16
  %90 = or disjoint i64 %_7.2.7.i, %88
  %91 = getelementptr inbounds nuw i8, ptr %input, i64 59
  %_9.3.7.i = load i8, ptr %91, align 1, !alias.scope !7, !noalias !4, !noundef !9
  %_8.3.7.i = zext i8 %_9.3.7.i to i64
  %_7.3.7.i = shl nuw nsw i64 %_8.3.7.i, 24
  %92 = getelementptr inbounds nuw i8, ptr %input, i64 60
  %_9.4.7.i = load i16, ptr %92, align 1, !alias.scope !7, !noalias !4
  %93 = zext i16 %_9.4.7.i to i64
  %94 = shl nuw nsw i64 %93, 32
  %95 = or disjoint i64 %_7.3.7.i, %94
  %96 = getelementptr inbounds nuw i8, ptr %input, i64 62
  %_9.6.7.i = load i16, ptr %96, align 1, !alias.scope !7, !noalias !4
  %97 = zext i16 %_9.6.7.i to i64
  %98 = shl nuw i64 %97, 48
  %99 = or disjoint i64 %95, %98
  %100 = or disjoint i64 %99, %90
  store i64 %100, ptr %words.sroa.31.i, align 8, !noalias !10
  call void @llvm.lifetime.start.p0(ptr nonnull %lo.i), !noalias !10
  call void @llvm.lifetime.start.p0(ptr nonnull %hi.i), !noalias !10
  %101 = and i64 %6, 4503599627370495
  store i64 %101, ptr %lo.i, align 8, !noalias !10
  %_19.i = tail call i64 @llvm.fshl.i64(i64 %12, i64 %8, i64 12)
  %_24.i = getelementptr inbounds nuw i8, ptr %lo.i, i64 8
  store i64 %_19.i, ptr %_24.i, align 8, !noalias !10
  %_25.i = tail call i64 @llvm.fshl.i64(i64 %24, i64 %17, i64 24)
  %_30.i = getelementptr inbounds nuw i8, ptr %lo.i, i64 16
  %102 = and i64 %_25.i, 4503599627370495
  store i64 %102, ptr %_30.i, align 8, !noalias !10
  %_31.i = tail call i64 @llvm.fshl.i64(i64 %35, i64 %32, i64 36)
  %_36.i = getelementptr inbounds nuw i8, ptr %lo.i, i64 24
  store i64 %_31.i, ptr %_36.i, align 8, !noalias !10
  %_37.i = tail call i64 @llvm.fshl.i64(i64 %_8.415.i, i64 %46, i64 48)
  %_42.i = getelementptr inbounds nuw i8, ptr %lo.i, i64 32
  %103 = and i64 %_37.i, 4503599627370495
  store i64 %103, ptr %_42.i, align 8, !noalias !10
  %_43.i = lshr i64 %62, 4
  %104 = and i64 %_43.i, 4503599627370495
  store i64 %104, ptr %hi.i, align 8, !noalias !10
  %_46.i = tail call i64 @llvm.fshl.i64(i64 %68, i64 %60, i64 8)
  %_51.i = getelementptr inbounds nuw i8, ptr %hi.i, i64 8
  %105 = and i64 %_46.i, 4503599627370495
  store i64 %105, ptr %_51.i, align 8, !noalias !10
  %_52.i = tail call i64 @llvm.fshl.i64(i64 %78, i64 %72, i64 20)
  %_57.i = getelementptr inbounds nuw i8, ptr %hi.i, i64 16
  store i64 %_52.i, ptr %_57.i, align 8, !noalias !10
  %_58.i = tail call i64 @llvm.fshl.i64(i64 %90, i64 %85, i64 32)
  %_63.i = getelementptr inbounds nuw i8, ptr %hi.i, i64 24
  %106 = and i64 %_58.i, 4503599627370495
  store i64 %106, ptr %_63.i, align 8, !noalias !10
  %_65.i = getelementptr inbounds nuw i8, ptr %hi.i, i64 32
  %107 = lshr i64 %100, 20
  store i64 %107, ptr %_65.i, align 8, !noalias !10
  call void @llvm.lifetime.start.p0(ptr nonnull %_66.i), !noalias !10
  call fastcc void @_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5214montgomery_mul(ptr noalias nofree noundef align 8 captures(address) dereferenceable(40) %_66.i, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(40) %lo.i, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(40) @alloc_595ed8f9b6c4f781a4a1d10db150f124) #9, !noalias !4
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %lo.i, ptr noundef nonnull align 8 dereferenceable(40) %_66.i, i64 40, i1 false), !noalias !10
  call void @llvm.lifetime.end.p0(ptr nonnull %_66.i), !noalias !10
  call void @llvm.lifetime.start.p0(ptr nonnull %_68.i), !noalias !10
  call fastcc void @_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5214montgomery_mul(ptr noalias nofree noundef align 8 captures(address) dereferenceable(40) %_68.i, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(40) %hi.i, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(40) @alloc_b0a0adc7a7ee3d20b0509962c17b23d6) #9, !noalias !4
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %hi.i, ptr noundef nonnull align 8 dereferenceable(40) %_68.i, i64 40, i1 false), !noalias !10
  call void @llvm.lifetime.end.p0(ptr nonnull %_68.i), !noalias !10
  tail call void @llvm.experimental.noalias.scope.decl(metadata !11)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !14)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !16)
  %_8.i.i = load i64, ptr %hi.i, align 8, !alias.scope !14, !noalias !18, !noundef !9
  %_9.i.i = load i64, ptr %lo.i, align 8, !alias.scope !16, !noalias !19, !noundef !9
  %108 = add i64 %_9.i.i, %_8.i.i
  %109 = and i64 %108, 4503599627370495
  %_8.1.i.i = load i64, ptr %_51.i, align 8, !alias.scope !14, !noalias !18, !noundef !9
  %_9.1.i.i = load i64, ptr %_24.i, align 8, !alias.scope !16, !noalias !19, !noundef !9
  %_10.1.i.i = lshr i64 %108, 52
  %_7.1.i.i = add i64 %_10.1.i.i, %_8.1.i.i
  %110 = add i64 %_7.1.i.i, %_9.1.i.i
  %111 = and i64 %110, 4503599627370495
  %_8.2.i.i = load i64, ptr %_57.i, align 8, !alias.scope !14, !noalias !18, !noundef !9
  %_9.2.i.i = load i64, ptr %_30.i, align 8, !alias.scope !16, !noalias !19, !noundef !9
  %_10.2.i.i = lshr i64 %110, 52
  %_7.2.i.i = add i64 %_9.2.i.i, %_8.2.i.i
  %112 = add i64 %_7.2.i.i, %_10.2.i.i
  %113 = and i64 %112, 4503599627370495
  %_8.3.i.i = load i64, ptr %_63.i, align 8, !alias.scope !14, !noalias !18, !noundef !9
  %_9.3.i.i = load i64, ptr %_36.i, align 8, !alias.scope !16, !noalias !19, !noundef !9
  %_10.3.i.i = lshr i64 %112, 52
  %_7.3.i.i = add i64 %_9.3.i.i, %_8.3.i.i
  %114 = add i64 %_7.3.i.i, %_10.3.i.i
  %115 = and i64 %114, 4503599627370495
  %_8.4.i.i = load i64, ptr %_65.i, align 8, !alias.scope !14, !noalias !18, !noundef !9
  %_9.4.i.i = load i64, ptr %_42.i, align 8, !alias.scope !16, !noalias !19, !noundef !9
  %_10.4.i.i = lshr i64 %114, 52
  %_7.4.i.i = add i64 %_9.4.i.i, %_8.4.i.i
  %116 = add i64 %_7.4.i.i, %_10.4.i.i
  %117 = and i64 %116, 4503599627370495
  %118 = add nsw i64 %109, -671914833335277
  %119 = and i64 %118, 4503599627370495
  %_10.neg8.1.i.i.i = ashr i64 %118, 63
  %_8.neg.1.i.i.i = add nsw i64 %_10.neg8.1.i.i.i, -3916664325105025
  %120 = add nsw i64 %_8.neg.1.i.i.i, %111
  %121 = and i64 %120, 4503599627370495
  %_10.neg8.2.i.i.i = ashr i64 %120, 63
  %_8.neg.2.i.i.i = add nsw i64 %113, -1367801
  %122 = add nsw i64 %_8.neg.2.i.i.i, %_10.neg8.2.i.i.i
  %123 = and i64 %122, 4503599627370495
  %_10.neg8.3.i.i.i = ashr i64 %122, 63
  %_8.neg.3.i.i.i = add nsw i64 %_10.neg8.3.i.i.i, %115
  %124 = and i64 %_8.neg.3.i.i.i, 4503599627370495
  %_10.neg8.4.i.i.i = ashr i64 %_8.neg.3.i.i.i, 63
  %_8.neg.4.i.i.i = add nsw i64 %117, -17592186044416
  %125 = add nsw i64 %_8.neg.4.i.i.i, %_10.neg8.4.i.i.i
  %_17.i.i.i = lshr i64 %125, 63
  %_16.i.i.i = trunc nuw nsw i64 %_17.i.i.i to i8
  %_23.i.i.i = tail call noundef i8 @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519(i8 noundef %_16.i.i.i) #9
  %_20.i.i.i.i = zext i8 %_23.i.i.i to i64
  %_19.i.i.i.i = sub nsw i64 0, %_20.i.i.i.i
  %addend.i.i.i.i = and i64 %_19.i.i.i.i, 671914833335277
  %126 = add nuw nsw i64 %addend.i.i.i.i, %119
  %127 = and i64 %126, 4503599627370495
  %addend.1.i.i.i.i = and i64 %_19.i.i.i.i, 3916664325105025
  %_7.1.i.i.i.i = lshr i64 %126, 52
  %_6.1.i.i.i.i = add nuw nsw i64 %addend.1.i.i.i.i, %121
  %128 = add nuw nsw i64 %_6.1.i.i.i.i, %_7.1.i.i.i.i
  %129 = and i64 %128, 4503599627370495
  %addend.2.i.i.i.i = and i64 %_19.i.i.i.i, 1367801
  %_7.2.i.i.i.i = lshr i64 %128, 52
  %_6.2.i.i.i.i = add nuw nsw i64 %addend.2.i.i.i.i, %123
  %130 = add nuw nsw i64 %_6.2.i.i.i.i, %_7.2.i.i.i.i
  %131 = and i64 %130, 4503599627370495
  %_7.3.i.i.i.i = lshr i64 %130, 52
  %_6.3.i.i.i.i = add nuw nsw i64 %_7.3.i.i.i.i, %124
  %132 = and i64 %_6.3.i.i.i.i, 4503599627370495
  %addend.4.i.i.i.i = and i64 %_19.i.i.i.i, 17592186044416
  %_7.4.i.i.i.i = lshr i64 %_6.3.i.i.i.i, 52
  %_6.4.i.i.i.i = add nsw i64 %125, %addend.4.i.i.i.i
  %133 = add nsw i64 %_6.4.i.i.i.i, %_7.4.i.i.i.i
  %134 = and i64 %133, 4503599627370495
  store i64 %127, ptr %unpacked.sroa.0, align 8, !alias.scope !20, !noalias !23
  store i64 %129, ptr %unpacked.sroa.5, align 8, !alias.scope !20, !noalias !23
  store i64 %131, ptr %unpacked.sroa.7, align 8, !alias.scope !20, !noalias !23
  store i64 %132, ptr %unpacked.sroa.9, align 8, !alias.scope !20, !noalias !23
  store i64 %134, ptr %unpacked.sroa.11, align 8, !alias.scope !20, !noalias !23
  store volatile i64 0, ptr %words.sroa.0.i, align 8, !alias.scope !26, !noalias !29
  fence syncscope("singlethread") seq_cst
  store volatile i64 0, ptr %words.sroa.7.i, align 8, !alias.scope !26, !noalias !29
  fence syncscope("singlethread") seq_cst
  store volatile i64 0, ptr %words.sroa.11.i, align 8, !alias.scope !26, !noalias !29
  fence syncscope("singlethread") seq_cst
  store volatile i64 0, ptr %words.sroa.15.i, align 8, !alias.scope !26, !noalias !29
  fence syncscope("singlethread") seq_cst
  store volatile i64 0, ptr %words.sroa.19.i, align 8, !alias.scope !26, !noalias !29
  fence syncscope("singlethread") seq_cst
  store volatile i64 0, ptr %words.sroa.23.i, align 8, !alias.scope !26, !noalias !29
  fence syncscope("singlethread") seq_cst
  store volatile i64 0, ptr %words.sroa.27.i, align 8, !alias.scope !26, !noalias !29
  fence syncscope("singlethread") seq_cst
  store volatile i64 0, ptr %words.sroa.31.i, align 8, !alias.scope !26, !noalias !29
  fence syncscope("singlethread") seq_cst
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i.i)
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %_2.i.i, i8 0, i64 40, i1 false), !alias.scope !32, !noalias !35
  call void @llvm.memcpy.p0.p0.i64(ptr nonnull align 8 dereferenceable(40) %lo.i, ptr nonnull align 8 %_2.i.i, i64 40, i1 true), !noalias !4
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i.i)
  fence syncscope("singlethread") seq_cst
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i5.i)
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %_2.i5.i, i8 0, i64 40, i1 false), !alias.scope !38, !noalias !41
  call void @llvm.memcpy.p0.p0.i64(ptr nonnull align 8 dereferenceable(40) %hi.i, ptr nonnull align 8 %_2.i5.i, i64 40, i1 true), !noalias !4
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i5.i)
  fence syncscope("singlethread") seq_cst
  call void @llvm.lifetime.end.p0(ptr nonnull %hi.i), !noalias !10
  call void @llvm.lifetime.end.p0(ptr nonnull %lo.i), !noalias !10
  call void @llvm.lifetime.end.p0(ptr nonnull %words.sroa.0.i)
  call void @llvm.lifetime.end.p0(ptr nonnull %words.sroa.7.i)
  call void @llvm.lifetime.end.p0(ptr nonnull %words.sroa.11.i)
  call void @llvm.lifetime.end.p0(ptr nonnull %words.sroa.15.i)
  call void @llvm.lifetime.end.p0(ptr nonnull %words.sroa.19.i)
  call void @llvm.lifetime.end.p0(ptr nonnull %words.sroa.23.i)
  call void @llvm.lifetime.end.p0(ptr nonnull %words.sroa.27.i)
  call void @llvm.lifetime.end.p0(ptr nonnull %words.sroa.31.i)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !44)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !47)
  %unpacked.sroa.0.0.unpacked.sroa.0.0.unpacked.sroa.0.0.unpacked.sroa.0.0._2.i.i1 = load i64, ptr %unpacked.sroa.0, align 8, !alias.scope !49, !noalias !52, !noundef !9
  %135 = trunc i64 %unpacked.sroa.0.0.unpacked.sroa.0.0.unpacked.sroa.0.0.unpacked.sroa.0.0._2.i.i1 to i8
  %_3.i.i = lshr i64 %unpacked.sroa.0.0.unpacked.sroa.0.0.unpacked.sroa.0.0.unpacked.sroa.0.0._2.i.i1, 8
  %136 = trunc i64 %_3.i.i to i8
  %_4.i.i = lshr i64 %unpacked.sroa.0.0.unpacked.sroa.0.0.unpacked.sroa.0.0.unpacked.sroa.0.0._2.i.i1, 16
  %137 = trunc i64 %_4.i.i to i8
  %_5.i.i = lshr i64 %unpacked.sroa.0.0.unpacked.sroa.0.0.unpacked.sroa.0.0.unpacked.sroa.0.0._2.i.i1, 24
  %138 = trunc i64 %_5.i.i to i8
  %_6.i.i = lshr i64 %unpacked.sroa.0.0.unpacked.sroa.0.0.unpacked.sroa.0.0.unpacked.sroa.0.0._2.i.i1, 32
  %139 = trunc i64 %_6.i.i to i8
  %_7.i.i = lshr i64 %unpacked.sroa.0.0.unpacked.sroa.0.0.unpacked.sroa.0.0.unpacked.sroa.0.0._2.i.i1, 40
  %140 = trunc i64 %_7.i.i to i8
  %_9.i.i2 = lshr i64 %unpacked.sroa.0.0.unpacked.sroa.0.0.unpacked.sroa.0.0.unpacked.sroa.0.0._2.i.i1, 48
  %unpacked.sroa.5.0.unpacked.sroa.5.0.unpacked.sroa.5.0.unpacked.sroa.5.8._11.i.i = load i64, ptr %unpacked.sroa.5, align 8, !alias.scope !49, !noalias !52, !noundef !9
  %_10.i.i = shl i64 %unpacked.sroa.5.0.unpacked.sroa.5.0.unpacked.sroa.5.0.unpacked.sroa.5.8._11.i.i, 4
  %_8.i.i3 = or i64 %_10.i.i, %_9.i.i2
  %141 = trunc i64 %_8.i.i3 to i8
  %_12.i.i = lshr i64 %unpacked.sroa.5.0.unpacked.sroa.5.0.unpacked.sroa.5.0.unpacked.sroa.5.8._11.i.i, 4
  %142 = trunc i64 %_12.i.i to i8
  %_13.i.i = lshr i64 %unpacked.sroa.5.0.unpacked.sroa.5.0.unpacked.sroa.5.0.unpacked.sroa.5.8._11.i.i, 12
  %143 = trunc i64 %_13.i.i to i8
  %_14.i.i = lshr i64 %unpacked.sroa.5.0.unpacked.sroa.5.0.unpacked.sroa.5.0.unpacked.sroa.5.8._11.i.i, 20
  %144 = trunc i64 %_14.i.i to i8
  %_15.i.i = lshr i64 %unpacked.sroa.5.0.unpacked.sroa.5.0.unpacked.sroa.5.0.unpacked.sroa.5.8._11.i.i, 28
  %145 = trunc i64 %_15.i.i to i8
  %_16.i.i = lshr i64 %unpacked.sroa.5.0.unpacked.sroa.5.0.unpacked.sroa.5.0.unpacked.sroa.5.8._11.i.i, 36
  %146 = trunc i64 %_16.i.i to i8
  %_17.i.i = lshr i64 %unpacked.sroa.5.0.unpacked.sroa.5.0.unpacked.sroa.5.0.unpacked.sroa.5.8._11.i.i, 44
  %147 = trunc i64 %_17.i.i to i8
  %unpacked.sroa.7.0.unpacked.sroa.7.0.unpacked.sroa.7.0.unpacked.sroa.7.16._18.i.i = load i64, ptr %unpacked.sroa.7, align 8, !alias.scope !49, !noalias !52, !noundef !9
  %148 = trunc i64 %unpacked.sroa.7.0.unpacked.sroa.7.0.unpacked.sroa.7.0.unpacked.sroa.7.16._18.i.i to i8
  %_19.i.i = lshr i64 %unpacked.sroa.7.0.unpacked.sroa.7.0.unpacked.sroa.7.0.unpacked.sroa.7.16._18.i.i, 8
  %149 = trunc i64 %_19.i.i to i8
  %_20.i.i = lshr i64 %unpacked.sroa.7.0.unpacked.sroa.7.0.unpacked.sroa.7.0.unpacked.sroa.7.16._18.i.i, 16
  %150 = trunc i64 %_20.i.i to i8
  %_21.i.i = lshr i64 %unpacked.sroa.7.0.unpacked.sroa.7.0.unpacked.sroa.7.0.unpacked.sroa.7.16._18.i.i, 24
  %151 = trunc i64 %_21.i.i to i8
  %_22.i.i = lshr i64 %unpacked.sroa.7.0.unpacked.sroa.7.0.unpacked.sroa.7.0.unpacked.sroa.7.16._18.i.i, 32
  %152 = trunc i64 %_22.i.i to i8
  %_23.i.i = lshr i64 %unpacked.sroa.7.0.unpacked.sroa.7.0.unpacked.sroa.7.0.unpacked.sroa.7.16._18.i.i, 40
  %153 = trunc i64 %_23.i.i to i8
  %_25.i.i = lshr i64 %unpacked.sroa.7.0.unpacked.sroa.7.0.unpacked.sroa.7.0.unpacked.sroa.7.16._18.i.i, 48
  %unpacked.sroa.9.0.unpacked.sroa.9.0.unpacked.sroa.9.0.unpacked.sroa.9.24._27.i.i = load i64, ptr %unpacked.sroa.9, align 8, !alias.scope !49, !noalias !52, !noundef !9
  %_26.i.i = shl i64 %unpacked.sroa.9.0.unpacked.sroa.9.0.unpacked.sroa.9.0.unpacked.sroa.9.24._27.i.i, 4
  %_24.i.i = or i64 %_26.i.i, %_25.i.i
  %154 = trunc i64 %_24.i.i to i8
  %_28.i.i = lshr i64 %unpacked.sroa.9.0.unpacked.sroa.9.0.unpacked.sroa.9.0.unpacked.sroa.9.24._27.i.i, 4
  %155 = trunc i64 %_28.i.i to i8
  %_29.i.i = lshr i64 %unpacked.sroa.9.0.unpacked.sroa.9.0.unpacked.sroa.9.0.unpacked.sroa.9.24._27.i.i, 12
  %156 = trunc i64 %_29.i.i to i8
  %_30.i.i = lshr i64 %unpacked.sroa.9.0.unpacked.sroa.9.0.unpacked.sroa.9.0.unpacked.sroa.9.24._27.i.i, 20
  %157 = trunc i64 %_30.i.i to i8
  %_31.i.i = lshr i64 %unpacked.sroa.9.0.unpacked.sroa.9.0.unpacked.sroa.9.0.unpacked.sroa.9.24._27.i.i, 28
  %158 = trunc i64 %_31.i.i to i8
  %_32.i.i = lshr i64 %unpacked.sroa.9.0.unpacked.sroa.9.0.unpacked.sroa.9.0.unpacked.sroa.9.24._27.i.i, 36
  %159 = trunc i64 %_32.i.i to i8
  %_33.i.i = lshr i64 %unpacked.sroa.9.0.unpacked.sroa.9.0.unpacked.sroa.9.0.unpacked.sroa.9.24._27.i.i, 44
  %160 = trunc i64 %_33.i.i to i8
  %unpacked.sroa.11.0.unpacked.sroa.11.0.unpacked.sroa.11.0.unpacked.sroa.11.32._34.i.i = load i64, ptr %unpacked.sroa.11, align 8, !alias.scope !49, !noalias !52, !noundef !9
  %161 = trunc i64 %unpacked.sroa.11.0.unpacked.sroa.11.0.unpacked.sroa.11.0.unpacked.sroa.11.32._34.i.i to i8
  %_35.i.i = lshr i64 %unpacked.sroa.11.0.unpacked.sroa.11.0.unpacked.sroa.11.0.unpacked.sroa.11.32._34.i.i, 8
  %162 = trunc i64 %_35.i.i to i8
  %_36.i.i = lshr i64 %unpacked.sroa.11.0.unpacked.sroa.11.0.unpacked.sroa.11.0.unpacked.sroa.11.32._34.i.i, 16
  %163 = trunc i64 %_36.i.i to i8
  %_37.i.i = lshr i64 %unpacked.sroa.11.0.unpacked.sroa.11.0.unpacked.sroa.11.0.unpacked.sroa.11.32._34.i.i, 24
  %164 = trunc i64 %_37.i.i to i8
  %_38.i.i = lshr i64 %unpacked.sroa.11.0.unpacked.sroa.11.0.unpacked.sroa.11.0.unpacked.sroa.11.32._34.i.i, 32
  %165 = trunc i64 %_38.i.i to i8
  %_39.i.i = lshr i64 %unpacked.sroa.11.0.unpacked.sroa.11.0.unpacked.sroa.11.0.unpacked.sroa.11.32._34.i.i, 40
  %166 = trunc i64 %_39.i.i to i8
  store i8 %135, ptr %scalar, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.4.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 1
  store i8 %136, ptr %_2.sroa.4.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.5.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 2
  store i8 %137, ptr %_2.sroa.5.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.6.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 3
  store i8 %138, ptr %_2.sroa.6.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.7.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 4
  store i8 %139, ptr %_2.sroa.7.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.8.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 5
  store i8 %140, ptr %_2.sroa.8.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.9.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 6
  store i8 %141, ptr %_2.sroa.9.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.10.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 7
  store i8 %142, ptr %_2.sroa.10.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.11.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 8
  store i8 %143, ptr %_2.sroa.11.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.12.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 9
  store i8 %144, ptr %_2.sroa.12.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.13.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 10
  store i8 %145, ptr %_2.sroa.13.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.14.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 11
  store i8 %146, ptr %_2.sroa.14.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.15.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 12
  store i8 %147, ptr %_2.sroa.15.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.16.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 13
  store i8 %148, ptr %_2.sroa.16.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.17.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 14
  store i8 %149, ptr %_2.sroa.17.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.18.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 15
  store i8 %150, ptr %_2.sroa.18.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.19.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 16
  store i8 %151, ptr %_2.sroa.19.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.20.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 17
  store i8 %152, ptr %_2.sroa.20.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.21.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 18
  store i8 %153, ptr %_2.sroa.21.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.22.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 19
  store i8 %154, ptr %_2.sroa.22.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.23.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 20
  store i8 %155, ptr %_2.sroa.23.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.24.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 21
  store i8 %156, ptr %_2.sroa.24.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.25.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 22
  store i8 %157, ptr %_2.sroa.25.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.26.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 23
  store i8 %158, ptr %_2.sroa.26.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.27.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 24
  store i8 %159, ptr %_2.sroa.27.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.28.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 25
  store i8 %160, ptr %_2.sroa.28.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.29.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 26
  store i8 %161, ptr %_2.sroa.29.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.30.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 27
  store i8 %162, ptr %_2.sroa.30.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.31.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 28
  store i8 %163, ptr %_2.sroa.31.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.32.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 29
  store i8 %164, ptr %_2.sroa.32.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.33.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 30
  store i8 %165, ptr %_2.sroa.33.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  %_2.sroa.34.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %scalar, i64 31
  store i8 %166, ptr %_2.sroa.34.0._0.sroa_idx.i, align 1, !alias.scope !44, !noalias !47
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i.sroa.0)
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i.sroa.4)
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i.sroa.5)
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i.sroa.6)
  call void @llvm.lifetime.start.p0(ptr nonnull %_2.i.sroa.7)
  store i64 0, ptr %_2.i.sroa.0, align 8, !alias.scope !54, !noalias !57
  store i64 0, ptr %_2.i.sroa.4, align 8, !alias.scope !54, !noalias !57
  store i64 0, ptr %_2.i.sroa.5, align 8, !alias.scope !54, !noalias !57
  store i64 0, ptr %_2.i.sroa.6, align 8, !alias.scope !54, !noalias !57
  store i64 0, ptr %_2.i.sroa.7, align 8, !alias.scope !54, !noalias !57
  %_2.i.sroa.0.0._2.i.sroa.0.0._2.i.sroa.0.0._2.i.sroa.0.0.unpacked.sroa.0.0.copyload = load volatile i64, ptr %_2.i.sroa.0, align 8
  store volatile i64 %_2.i.sroa.0.0._2.i.sroa.0.0._2.i.sroa.0.0._2.i.sroa.0.0.unpacked.sroa.0.0.copyload, ptr %unpacked.sroa.0, align 8
  %_2.i.sroa.4.0._2.i.sroa.4.0._2.i.sroa.4.0._2.i.sroa.4.8.unpacked.sroa.5.0.copyload = load volatile i64, ptr %_2.i.sroa.4, align 8
  store volatile i64 %_2.i.sroa.4.0._2.i.sroa.4.0._2.i.sroa.4.0._2.i.sroa.4.8.unpacked.sroa.5.0.copyload, ptr %unpacked.sroa.5, align 8
  %_2.i.sroa.5.0._2.i.sroa.5.0._2.i.sroa.5.0._2.i.sroa.5.16.unpacked.sroa.7.0.copyload = load volatile i64, ptr %_2.i.sroa.5, align 8
  store volatile i64 %_2.i.sroa.5.0._2.i.sroa.5.0._2.i.sroa.5.0._2.i.sroa.5.16.unpacked.sroa.7.0.copyload, ptr %unpacked.sroa.7, align 8
  %_2.i.sroa.6.0._2.i.sroa.6.0._2.i.sroa.6.0._2.i.sroa.6.24.unpacked.sroa.9.0.copyload = load volatile i64, ptr %_2.i.sroa.6, align 8
  store volatile i64 %_2.i.sroa.6.0._2.i.sroa.6.0._2.i.sroa.6.0._2.i.sroa.6.24.unpacked.sroa.9.0.copyload, ptr %unpacked.sroa.9, align 8
  %_2.i.sroa.7.0._2.i.sroa.7.0._2.i.sroa.7.0._2.i.sroa.7.32.unpacked.sroa.11.0.copyload = load volatile i64, ptr %_2.i.sroa.7, align 8
  store volatile i64 %_2.i.sroa.7.0._2.i.sroa.7.0._2.i.sroa.7.0._2.i.sroa.7.32.unpacked.sroa.11.0.copyload, ptr %unpacked.sroa.11, align 8
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i.sroa.0)
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i.sroa.4)
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i.sroa.5)
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i.sroa.6)
  call void @llvm.lifetime.end.p0(ptr nonnull %_2.i.sroa.7)
  fence syncscope("singlethread") seq_cst
  call void @llvm.lifetime.end.p0(ptr nonnull %unpacked.sroa.0)
  call void @llvm.lifetime.end.p0(ptr nonnull %unpacked.sroa.5)
  call void @llvm.lifetime.end.p0(ptr nonnull %unpacked.sroa.7)
  call void @llvm.lifetime.end.p0(ptr nonnull %unpacked.sroa.9)
  call void @llvm.lifetime.end.p0(ptr nonnull %unpacked.sroa.11)
  ret void
}

; Function Attrs: nofree noinline norecurse nounwind nonlazybind uwtable
declare hidden fastcc void @_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5214montgomery_mul(ptr dead_on_unwind noalias nofree noundef nonnull writable writeonly align 8 captures(none) dereferenceable(40) initializes((0, 40)), ptr noalias nofree noundef nonnull readonly align 8 captures(none) dereferenceable(40), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40)) unnamed_addr #2

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #3

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #4

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #3

; Function Attrs: nonlazybind
declare i32 @rust_eh_personality(...) unnamed_addr #5

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr writeonly captures(none), i8, i64, i1 immarg) #6

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.fshl.i64(i64, i64, i64) #7

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite)
declare void @llvm.experimental.noalias.scope.decl(metadata) #8

attributes #0 = { mustprogress nofree noinline norecurse nounwind nonlazybind willreturn memory(inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nofree norecurse nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { nofree noinline norecurse nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #4 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #5 = { nonlazybind "target-cpu"="x86-64" }
attributes #6 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #7 = { nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none) }
attributes #8 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite) }
attributes #9 = { noinline nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{!5}
!5 = distinct !{!5, !6, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5215from_bytes_wide: %reduced"}
!6 = distinct !{!6, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5215from_bytes_wide"}
!7 = !{!8}
!8 = distinct !{!8, !6, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5215from_bytes_wide: %bytes"}
!9 = !{}
!10 = !{!5, !8}
!11 = !{!12}
!12 = distinct !{!12, !13, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar523add: %_0"}
!13 = distinct !{!13, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar523add"}
!14 = !{!15}
!15 = distinct !{!15, !13, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar523add: %a"}
!16 = !{!17}
!17 = distinct !{!17, !13, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar523add: %b"}
!18 = !{!12, !17, !5, !8}
!19 = !{!12, !15, !5, !8}
!20 = !{!21, !12, !5}
!21 = distinct !{!21, !22, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar523sub: %_0"}
!22 = distinct !{!22, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar523sub"}
!23 = !{!24, !25, !15, !17, !8}
!24 = distinct !{!24, !22, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar523sub: %a"}
!25 = distinct !{!25, !22, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar523sub: %b"}
!26 = !{!27}
!27 = distinct !{!27, !28, !"_RNvXCs2F8OvSoAkiP_7zeroizeyNtB2_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519: %self"}
!28 = distinct !{!28, !"_RNvXCs2F8OvSoAkiP_7zeroizeyNtB2_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519"}
!29 = !{!30, !5, !8}
!30 = distinct !{!30, !31, !"_RNvXs4_Cs2F8OvSoAkiP_7zeroizeINtNtNtCsgxBkk5gSRhY_4core5slice4iter7IterMutyENtB5_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519: %self"}
!31 = distinct !{!31, !"_RNvXs4_Cs2F8OvSoAkiP_7zeroizeINtNtNtCsgxBkk5gSRhY_4core5slice4iter7IterMutyENtB5_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519"}
!32 = !{!33}
!33 = distinct !{!33, !34, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar52NtNtCsgxBkk5gSRhY_4core7default7Default7default: %_0"}
!34 = distinct !{!34, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar52NtNtCsgxBkk5gSRhY_4core7default7Default7default"}
!35 = !{!36, !5, !8}
!36 = distinct !{!36, !37, !"_RNvXCs2F8OvSoAkiP_7zeroizeNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalar8Scalar52NtB2_7Zeroize7zeroizeBy_: %self"}
!37 = distinct !{!37, !"_RNvXCs2F8OvSoAkiP_7zeroizeNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalar8Scalar52NtB2_7Zeroize7zeroizeBy_"}
!38 = !{!39}
!39 = distinct !{!39, !40, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar52NtNtCsgxBkk5gSRhY_4core7default7Default7default: %_0"}
!40 = distinct !{!40, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar52NtNtCsgxBkk5gSRhY_4core7default7Default7default"}
!41 = !{!42, !5, !8}
!42 = distinct !{!42, !43, !"_RNvXCs2F8OvSoAkiP_7zeroizeNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalar8Scalar52NtB2_7Zeroize7zeroizeBy_: %self"}
!43 = distinct !{!43, !"_RNvXCs2F8OvSoAkiP_7zeroizeNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalar8Scalar52NtB2_7Zeroize7zeroizeBy_"}
!44 = !{!45}
!45 = distinct !{!45, !46, !"_RNvMsp_NtCsjK63O35OHGN_14solana_ed255196scalarNtNtNtNtNtB7_7backend6serial3u646scalar8Scalar524pack: %_0"}
!46 = distinct !{!46, !"_RNvMsp_NtCsjK63O35OHGN_14solana_ed255196scalarNtNtNtNtNtB7_7backend6serial3u646scalar8Scalar524pack"}
!47 = !{!48}
!48 = distinct !{!48, !46, !"_RNvMsp_NtCsjK63O35OHGN_14solana_ed255196scalarNtNtNtNtNtB7_7backend6serial3u646scalar8Scalar524pack: %self"}
!49 = !{!50, !48}
!50 = distinct !{!50, !51, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar528to_bytes: %self"}
!51 = distinct !{!51, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar528to_bytes"}
!52 = !{!53, !45}
!53 = distinct !{!53, !51, !"_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar528to_bytes: %s"}
!54 = !{!55}
!55 = distinct !{!55, !56, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar52NtNtCsgxBkk5gSRhY_4core7default7Default7default: %_0"}
!56 = distinct !{!56, !"_RNvXs6_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar52NtNtCsgxBkk5gSRhY_4core7default7Default7default"}
!57 = !{!58}
!58 = distinct !{!58, !59, !"_RNvXCs2F8OvSoAkiP_7zeroizeNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalar8Scalar52NtB2_7Zeroize7zeroizeBy_: %self"}
!59 = distinct !{!59, !"_RNvXCs2F8OvSoAkiP_7zeroizeNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalar8Scalar52NtB2_7Zeroize7zeroizeBy_"}
