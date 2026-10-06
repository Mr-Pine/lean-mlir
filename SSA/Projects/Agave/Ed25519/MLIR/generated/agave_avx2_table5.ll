; ModuleID = '/home/nine/Documents/anza-code/.lmf-rir-ed25519/SSA/Projects/Agave/Ed25519/MLIR/generated/agave_avx2_table5.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%"backend::vector::avx2::edwards::CachedPoint" = type { %"backend::vector::avx2::field::FieldElement2625x4" }
%"backend::vector::avx2::field::FieldElement2625x4" = type { [5 x <4 x i64>] }

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
declare void @_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x419square_and_negate_DB1a_NtB2_28___Impl_square_and_negate_D__25__impl_square_and_negate_D(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([160 x i8]) align 32 captures(none) dereferenceable(160) initializes((0, 160)), ptr noalias nofree noundef readonly align 32 captures(none) dereferenceable(160)) unnamed_addr #0

; Function Attrs: inlinehint mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
declare hidden fastcc void @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul(ptr dead_on_unwind noalias nofree noundef nonnull writable writeonly align 32 captures(none) dereferenceable(160) initializes((0, 160)), ptr noalias nofree noundef nonnull readonly align 32 captures(none) dereferenceable(160), ptr noalias nofree noundef nonnull readonly align 32 captures(none) dereferenceable(160)) unnamed_addr #1

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable
define void @_RNvXNvXsk_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsINtNtBg_6window15NafLookupTable5NtB8_11CachedPointEINtNtCsgxBkk5gSRhY_4core7convert4FromRNtNtBg_7edwards12EdwardsPointE4fromB1c_NtB2_13___Impl_from__10__impl_from(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([1280 x i8]) align 32 captures(none) dereferenceable(1280) %_0, ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160) %point) unnamed_addr #2 {
start:
  %t1.i = alloca [160 x i8], align 32
  %t0.i = alloca [160 x i8], align 32
  %_8.i = alloca [160 x i8], align 32
  %tmp.i = alloca [160 x i8], align 32
  %tmp1.i = alloca [160 x i8], align 32
  %tmp0.i = alloca [160 x i8], align 32
  %_15 = alloca [160 x i8], align 32
  %A2 = alloca [160 x i8], align 32
  %Ai = alloca [1280 x i8], align 32
  %_3.sroa.0.0.copyload = load i64, ptr %point, align 8
  %_3.sroa.4.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 8
  %_3.sroa.4.0.copyload = load i64, ptr %_3.sroa.4.0.point.sroa_idx, align 8
  %_3.sroa.5.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 16
  %_3.sroa.5.0.copyload = load i64, ptr %_3.sroa.5.0.point.sroa_idx, align 8
  %_3.sroa.6.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 24
  %_3.sroa.6.0.copyload = load i64, ptr %_3.sroa.6.0.point.sroa_idx, align 8
  %_3.sroa.7.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 32
  %_3.sroa.7.0.copyload = load i64, ptr %_3.sroa.7.0.point.sroa_idx, align 8
  %_3.sroa.8.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 40
  %_3.sroa.8.0.copyload = load i64, ptr %_3.sroa.8.0.point.sroa_idx, align 8
  %_3.sroa.9.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 48
  %_3.sroa.9.0.copyload = load i64, ptr %_3.sroa.9.0.point.sroa_idx, align 8
  %_3.sroa.10.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 56
  %_3.sroa.10.0.copyload = load i64, ptr %_3.sroa.10.0.point.sroa_idx, align 8
  %_3.sroa.11.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 64
  %_3.sroa.11.0.copyload = load i64, ptr %_3.sroa.11.0.point.sroa_idx, align 8
  %_3.sroa.12.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 72
  %_3.sroa.12.0.copyload = load i64, ptr %_3.sroa.12.0.point.sroa_idx, align 8
  %_3.sroa.13.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 80
  %_3.sroa.13.0.copyload = load i64, ptr %_3.sroa.13.0.point.sroa_idx, align 8
  %_3.sroa.14.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 88
  %_3.sroa.14.0.copyload = load i64, ptr %_3.sroa.14.0.point.sroa_idx, align 8
  %_3.sroa.15.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 96
  %_3.sroa.15.0.copyload = load i64, ptr %_3.sroa.15.0.point.sroa_idx, align 8
  %_3.sroa.16.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 104
  %_3.sroa.16.0.copyload = load i64, ptr %_3.sroa.16.0.point.sroa_idx, align 8
  %_3.sroa.17.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 112
  %_3.sroa.17.0.copyload = load i64, ptr %_3.sroa.17.0.point.sroa_idx, align 8
  %_3.sroa.18.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 120
  %_3.sroa.18.0.copyload = load i64, ptr %_3.sroa.18.0.point.sroa_idx, align 8
  %_3.sroa.19.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 128
  %_3.sroa.19.0.copyload = load i64, ptr %_3.sroa.19.0.point.sroa_idx, align 8
  %_3.sroa.20.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 136
  %_3.sroa.20.0.copyload = load i64, ptr %_3.sroa.20.0.point.sroa_idx, align 8
  %_3.sroa.21.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 144
  %_3.sroa.21.0.copyload = load i64, ptr %_3.sroa.21.0.point.sroa_idx, align 8
  %_3.sroa.22.0.point.sroa_idx = getelementptr inbounds nuw i8, ptr %point, i64 152
  %_3.sroa.22.0.copyload = load i64, ptr %_3.sroa.22.0.point.sroa_idx, align 8
  %0 = trunc i64 %_3.sroa.18.0.copyload to i32
  %1 = trunc i64 %_3.sroa.13.0.copyload to i32
  %2 = trunc i64 %_3.sroa.8.0.copyload to i32
  %3 = trunc i64 %_3.sroa.0.0.copyload to i32
  %4 = insertelement <4 x i32> poison, i32 %3, i64 0
  %5 = insertelement <4 x i32> %4, i32 %2, i64 1
  %6 = insertelement <4 x i32> %5, i32 %1, i64 2
  %7 = insertelement <4 x i32> %6, i32 %0, i64 3
  %8 = and <4 x i32> %7, splat (i32 67108863)
  %9 = insertelement <4 x i64> poison, i64 %_3.sroa.0.0.copyload, i64 0
  %10 = insertelement <4 x i64> %9, i64 %_3.sroa.8.0.copyload, i64 1
  %11 = insertelement <4 x i64> %10, i64 %_3.sroa.13.0.copyload, i64 2
  %12 = insertelement <4 x i64> %11, i64 %_3.sroa.18.0.copyload, i64 3
  %13 = lshr <4 x i64> %12, splat (i64 26)
  %14 = trunc <4 x i64> %13 to <4 x i32>
  %15 = shufflevector <4 x i32> %8, <4 x i32> %14, <8 x i32> <i32 0, i32 1, i32 4, i32 5, i32 2, i32 3, i32 6, i32 7>
  %16 = trunc i64 %_3.sroa.19.0.copyload to i32
  %17 = trunc i64 %_3.sroa.14.0.copyload to i32
  %18 = trunc i64 %_3.sroa.9.0.copyload to i32
  %19 = trunc i64 %_3.sroa.4.0.copyload to i32
  %20 = insertelement <4 x i32> poison, i32 %19, i64 0
  %21 = insertelement <4 x i32> %20, i32 %18, i64 1
  %22 = insertelement <4 x i32> %21, i32 %17, i64 2
  %23 = insertelement <4 x i32> %22, i32 %16, i64 3
  %24 = and <4 x i32> %23, splat (i32 67108863)
  %25 = insertelement <4 x i64> poison, i64 %_3.sroa.4.0.copyload, i64 0
  %26 = insertelement <4 x i64> %25, i64 %_3.sroa.9.0.copyload, i64 1
  %27 = insertelement <4 x i64> %26, i64 %_3.sroa.14.0.copyload, i64 2
  %28 = insertelement <4 x i64> %27, i64 %_3.sroa.19.0.copyload, i64 3
  %29 = lshr <4 x i64> %28, splat (i64 26)
  %30 = trunc <4 x i64> %29 to <4 x i32>
  %31 = shufflevector <4 x i32> %24, <4 x i32> %30, <8 x i32> <i32 0, i32 1, i32 4, i32 5, i32 2, i32 3, i32 6, i32 7>
  %32 = trunc i64 %_3.sroa.20.0.copyload to i32
  %33 = trunc i64 %_3.sroa.15.0.copyload to i32
  %34 = trunc i64 %_3.sroa.10.0.copyload to i32
  %35 = trunc i64 %_3.sroa.5.0.copyload to i32
  %36 = insertelement <4 x i32> poison, i32 %35, i64 0
  %37 = insertelement <4 x i32> %36, i32 %34, i64 1
  %38 = insertelement <4 x i32> %37, i32 %33, i64 2
  %39 = insertelement <4 x i32> %38, i32 %32, i64 3
  %40 = and <4 x i32> %39, splat (i32 67108863)
  %41 = insertelement <4 x i64> poison, i64 %_3.sroa.5.0.copyload, i64 0
  %42 = insertelement <4 x i64> %41, i64 %_3.sroa.10.0.copyload, i64 1
  %43 = insertelement <4 x i64> %42, i64 %_3.sroa.15.0.copyload, i64 2
  %44 = insertelement <4 x i64> %43, i64 %_3.sroa.20.0.copyload, i64 3
  %45 = lshr <4 x i64> %44, splat (i64 26)
  %46 = trunc <4 x i64> %45 to <4 x i32>
  %47 = shufflevector <4 x i32> %40, <4 x i32> %46, <8 x i32> <i32 0, i32 1, i32 4, i32 5, i32 2, i32 3, i32 6, i32 7>
  %48 = trunc i64 %_3.sroa.21.0.copyload to i32
  %49 = trunc i64 %_3.sroa.16.0.copyload to i32
  %50 = trunc i64 %_3.sroa.11.0.copyload to i32
  %51 = trunc i64 %_3.sroa.6.0.copyload to i32
  %52 = insertelement <4 x i32> poison, i32 %51, i64 0
  %53 = insertelement <4 x i32> %52, i32 %50, i64 1
  %54 = insertelement <4 x i32> %53, i32 %49, i64 2
  %55 = insertelement <4 x i32> %54, i32 %48, i64 3
  %56 = and <4 x i32> %55, splat (i32 67108863)
  %57 = insertelement <4 x i64> poison, i64 %_3.sroa.6.0.copyload, i64 0
  %58 = insertelement <4 x i64> %57, i64 %_3.sroa.11.0.copyload, i64 1
  %59 = insertelement <4 x i64> %58, i64 %_3.sroa.16.0.copyload, i64 2
  %60 = insertelement <4 x i64> %59, i64 %_3.sroa.21.0.copyload, i64 3
  %61 = lshr <4 x i64> %60, splat (i64 26)
  %62 = trunc <4 x i64> %61 to <4 x i32>
  %63 = shufflevector <4 x i32> %56, <4 x i32> %62, <8 x i32> <i32 0, i32 1, i32 4, i32 5, i32 2, i32 3, i32 6, i32 7>
  %64 = trunc i64 %_3.sroa.22.0.copyload to i32
  %65 = trunc i64 %_3.sroa.17.0.copyload to i32
  %66 = trunc i64 %_3.sroa.12.0.copyload to i32
  %67 = trunc i64 %_3.sroa.7.0.copyload to i32
  %68 = insertelement <4 x i32> poison, i32 %67, i64 0
  %69 = insertelement <4 x i32> %68, i32 %66, i64 1
  %70 = insertelement <4 x i32> %69, i32 %65, i64 2
  %71 = insertelement <4 x i32> %70, i32 %64, i64 3
  %72 = and <4 x i32> %71, splat (i32 67108863)
  %73 = insertelement <4 x i64> poison, i64 %_3.sroa.7.0.copyload, i64 0
  %74 = insertelement <4 x i64> %73, i64 %_3.sroa.12.0.copyload, i64 1
  %75 = insertelement <4 x i64> %74, i64 %_3.sroa.17.0.copyload, i64 2
  %76 = insertelement <4 x i64> %75, i64 %_3.sroa.22.0.copyload, i64 3
  %77 = lshr <4 x i64> %76, splat (i64 26)
  %78 = trunc <4 x i64> %77 to <4 x i32>
  %79 = shufflevector <4 x i32> %72, <4 x i32> %78, <8 x i32> <i32 0, i32 1, i32 4, i32 5, i32 2, i32 3, i32 6, i32 7>
  %_8.i.i.i.i46 = lshr <8 x i32> %15, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %80 = and <8 x i32> %15, <i32 67108863, i32 67108863, i32 33554431, i32 33554431, i32 67108863, i32 67108863, i32 33554431, i32 33554431>
  %_8.i.i43.i.i = lshr <8 x i32> %31, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i47.i.i = shufflevector <8 x i32> %_8.i.i.i.i46, <8 x i32> %_8.i.i43.i.i, <8 x i32> <i32 2, i32 3, i32 8, i32 9, i32 6, i32 7, i32 12, i32 13>
  %81 = and <8 x i32> %31, <i32 67108863, i32 67108863, i32 33554431, i32 33554431, i32 67108863, i32 67108863, i32 33554431, i32 33554431>
  %_6.i48.i.i = add nuw nsw <8 x i32> %_9.i47.i.i, %81
  %_8.i.i50.i.i = lshr <8 x i32> %47, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i54.i.i49 = shufflevector <8 x i32> %_8.i.i43.i.i, <8 x i32> %_8.i.i50.i.i, <8 x i32> <i32 2, i32 3, i32 8, i32 9, i32 6, i32 7, i32 12, i32 13>
  %82 = and <8 x i32> %47, <i32 67108863, i32 67108863, i32 33554431, i32 33554431, i32 67108863, i32 67108863, i32 33554431, i32 33554431>
  %_6.i55.i.i = add nuw nsw <8 x i32> %_9.i54.i.i49, %82
  %_8.i.i57.i.i = lshr <8 x i32> %63, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i61.i.i = shufflevector <8 x i32> %_8.i.i50.i.i, <8 x i32> %_8.i.i57.i.i, <8 x i32> <i32 2, i32 3, i32 8, i32 9, i32 6, i32 7, i32 12, i32 13>
  %83 = and <8 x i32> %63, <i32 67108863, i32 67108863, i32 33554431, i32 33554431, i32 67108863, i32 67108863, i32 33554431, i32 33554431>
  %_6.i62.i.i = add nuw nsw <8 x i32> %_9.i61.i.i, %83
  %_8.i.i64.i.i = lshr <8 x i32> %79, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i68.i.i = shufflevector <8 x i32> %_8.i.i57.i.i, <8 x i32> %_8.i.i64.i.i, <8 x i32> <i32 2, i32 3, i32 8, i32 9, i32 6, i32 7, i32 12, i32 13>
  %84 = and <8 x i32> %79, <i32 67108863, i32 67108863, i32 33554431, i32 33554431, i32 67108863, i32 67108863, i32 33554431, i32 33554431>
  %_6.i69.i.i = add nuw nsw <8 x i32> %_9.i68.i.i, %84
  %85 = and <8 x i32> %_8.i.i64.i.i, <i32 0, i32 0, i32 127, i32 127, i32 0, i32 0, i32 127, i32 127>
  %_76.i.i.inner = shufflevector <8 x i32> %85, <8 x i32> poison, <8 x i32> <i32 2, i32 0, i32 3, i32 1, i32 6, i32 4, i32 7, i32 5>
  %_76.i.i = bitcast <8 x i32> %_76.i.i.inner to <4 x i64>
  %_75.i.i = mul nuw nsw <4 x i64> %_76.i.i, splat (i64 19)
  %86 = bitcast <4 x i64> %_75.i.i to <8 x i32>
  %_78.i.i = shufflevector <8 x i32> %86, <8 x i32> poison, <8 x i32> <i32 0, i32 2, i32 1, i32 3, i32 4, i32 6, i32 5, i32 7>
  %_6.i.i.i.i50 = add nuw nsw <8 x i32> %80, %_78.i.i
  %_3.i219.i.i.i = shufflevector <8 x i32> %_6.i.i.i.i50, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i74272.i.i.i = shufflevector <8 x i32> %_6.i48.i.i, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i75326.i.i.i = shufflevector <8 x i32> %_6.i55.i.i, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i76380.i.i.i = shufflevector <8 x i32> %_6.i62.i.i, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i77.i.i.i = shufflevector <8 x i32> %_6.i69.i.i, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_6.i.i.i.i = sub nsw <8 x i32> <i32 134217690, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %_6.i.i.i.i50
  %_6.i10.i.i.i = sub nsw <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %_6.i48.i.i
  %_6.i11.i.i.i = sub nsw <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %_6.i55.i.i
  %_6.i12.i.i.i = sub nsw <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %_6.i62.i.i
  %_6.i13.i.i.i = sub nsw <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %_6.i69.i.i
  %r.i192.i.i.i = shufflevector <8 x i32> %_6.i.i.i.i, <8 x i32> %_6.i.i.i.i50, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i199.i.i.i = shufflevector <8 x i32> %_6.i10.i.i.i, <8 x i32> %_6.i48.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i206.i.i.i = shufflevector <8 x i32> %_6.i11.i.i.i, <8 x i32> %_6.i55.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i213.i.i.i = shufflevector <8 x i32> %_6.i12.i.i.i, <8 x i32> %_6.i62.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i220.i.i.i = shufflevector <8 x i32> %_6.i13.i.i.i, <8 x i32> %_6.i69.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %_6.i.i1.i.i = add <8 x i32> %r.i192.i.i.i, %_3.i219.i.i.i
  %_6.i10.i2.i.i = add <8 x i32> %r.i199.i.i.i, %_3.i74272.i.i.i
  %_6.i11.i3.i.i = add <8 x i32> %r.i206.i.i.i, %_3.i75326.i.i.i
  %_6.i12.i4.i.i = add <8 x i32> %r.i213.i.i.i, %_3.i76380.i.i.i
  %_6.i13.i5.i.i = add <8 x i32> %r.i220.i.i.i, %_3.i77.i.i.i
  %r.i191.i.i = shufflevector <8 x i32> %_6.i.i1.i.i, <8 x i32> %_6.i.i.i.i50, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i198.i.i = shufflevector <8 x i32> %_6.i10.i2.i.i, <8 x i32> %_6.i48.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i205.i.i = shufflevector <8 x i32> %_6.i11.i3.i.i, <8 x i32> %_6.i55.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i212.i.i = shufflevector <8 x i32> %_6.i12.i4.i.i, <8 x i32> %_6.i62.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i219.i.i = shufflevector <8 x i32> %_6.i13.i5.i.i, <8 x i32> %_6.i69.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %_11.i.i.i = shufflevector <8 x i32> %r.i191.i.i, <8 x i32> <i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison>, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %_14.i.i.i = shufflevector <8 x i32> %r.i191.i.i, <8 x i32> <i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0>, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %87 = bitcast <8 x i32> %_11.i.i.i to <4 x i64>
  %88 = bitcast <8 x i32> %_14.i.i.i to <4 x i64>
  %_11.i25.i.i = shufflevector <8 x i32> %r.i198.i.i, <8 x i32> <i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison>, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %_14.i26.i.i = shufflevector <8 x i32> %r.i198.i.i, <8 x i32> <i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0>, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %89 = bitcast <8 x i32> %_11.i25.i.i to <4 x i64>
  %90 = bitcast <8 x i32> %_14.i26.i.i to <4 x i64>
  %_11.i27.i.i = shufflevector <8 x i32> %r.i205.i.i, <8 x i32> <i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison>, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %_14.i28.i.i = shufflevector <8 x i32> %r.i205.i.i, <8 x i32> <i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0>, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %91 = bitcast <8 x i32> %_11.i27.i.i to <4 x i64>
  %92 = bitcast <8 x i32> %_14.i28.i.i to <4 x i64>
  %_11.i29.i.i = shufflevector <8 x i32> %r.i212.i.i, <8 x i32> <i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison>, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %_14.i30.i.i = shufflevector <8 x i32> %r.i212.i.i, <8 x i32> <i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0>, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %93 = bitcast <8 x i32> %_11.i29.i.i to <4 x i64>
  %94 = bitcast <8 x i32> %_14.i30.i.i to <4 x i64>
  %_11.i31.i.i = shufflevector <8 x i32> %r.i219.i.i, <8 x i32> <i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison>, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %_14.i32.i.i = shufflevector <8 x i32> %r.i219.i.i, <8 x i32> <i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0>, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %95 = bitcast <8 x i32> %_11.i31.i.i to <4 x i64>
  %96 = bitcast <8 x i32> %_14.i32.i.i to <4 x i64>
  %_9.i.i.i = mul nuw nsw <4 x i64> %87, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i36.i.i = mul nuw nsw <4 x i64> %88, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i39.i.i = mul nuw nsw <4 x i64> %89, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i42.i.i = mul nuw nsw <4 x i64> %90, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i45.i.i = mul nuw nsw <4 x i64> %91, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i48.i.i = mul nuw nsw <4 x i64> %92, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i51.i.i = mul nuw nsw <4 x i64> %93, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i54.i.i = mul nuw nsw <4 x i64> %94, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i57.i.i = mul nuw nsw <4 x i64> %95, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i60.i.i = mul nuw nsw <4 x i64> %96, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_5.i13.i.i.i.i = lshr <4 x i64> %_9.i.i.i, splat (i64 26)
  %_6.i.i15.i.i.i.i = add nuw nsw <4 x i64> %_5.i13.i.i.i.i, %_9.i36.i.i
  %_6.i.i17.i.i.i.i = and <4 x i64> %_9.i.i.i, splat (i64 67108862)
  %_5.i13.i45.i.i.i = lshr <4 x i64> %_9.i45.i.i, splat (i64 26)
  %_6.i.i15.i46.i.i.i = add nuw nsw <4 x i64> %_5.i13.i45.i.i.i, %_9.i48.i.i
  %_6.i.i17.i48.i.i.i = and <4 x i64> %_9.i45.i.i, splat (i64 67108862)
  %_5.i13.i52.i.i.i = lshr <4 x i64> %_6.i.i15.i.i.i.i, splat (i64 25)
  %_6.i.i15.i53.i.i.i = add nuw nsw <4 x i64> %_5.i13.i52.i.i.i, %_9.i39.i.i
  %_6.i.i17.i55.i.i.i = and <4 x i64> %_6.i.i15.i.i.i.i, splat (i64 33554431)
  %_5.i13.i59.i.i.i = lshr <4 x i64> %_6.i.i15.i46.i.i.i, splat (i64 25)
  %_6.i.i15.i60.i.i.i = add nuw nsw <4 x i64> %_5.i13.i59.i.i.i, %_9.i51.i.i
  %_6.i.i17.i62.i.i.i = and <4 x i64> %_6.i.i15.i46.i.i.i, splat (i64 33554431)
  %_5.i13.i66.i.i.i = lshr <4 x i64> %_6.i.i15.i53.i.i.i, splat (i64 26)
  %_6.i.i15.i67.i.i.i = add nuw nsw <4 x i64> %_5.i13.i66.i.i.i, %_9.i42.i.i
  %_5.i13.i73.i.i.i = lshr <4 x i64> %_6.i.i15.i60.i.i.i, splat (i64 26)
  %_6.i.i15.i74.i.i.i = add nuw nsw <4 x i64> %_5.i13.i73.i.i.i, %_9.i54.i.i
  %_5.i13.i80.i.i.i = lshr <4 x i64> %_6.i.i15.i67.i.i.i, splat (i64 25)
  %_6.i.i15.i81.i.i.i = add nuw nsw <4 x i64> %_5.i13.i80.i.i.i, %_6.i.i17.i48.i.i.i
  %_5.i13.i87.i.i.i = lshr <4 x i64> %_6.i.i15.i74.i.i.i, splat (i64 25)
  %_6.i.i15.i88.i.i.i = add nuw nsw <4 x i64> %_5.i13.i87.i.i.i, %_9.i57.i.i
  %_5.i13.i94.i.i.i = lshr <4 x i64> %_6.i.i15.i81.i.i.i, splat (i64 26)
  %_6.i.i15.i95.i.i.i = add nuw nsw <4 x i64> %_5.i13.i94.i.i.i, %_6.i.i17.i62.i.i.i
  %_5.i13.i101.i.i.i = lshr <4 x i64> %_6.i.i15.i88.i.i.i, splat (i64 26)
  %_6.i.i15.i102.i.i.i = add nuw nsw <4 x i64> %_5.i13.i101.i.i.i, %_9.i60.i.i
  %_5.i.i.i.i = lshr <4 x i64> %_6.i.i15.i102.i.i.i, splat (i64 25)
  %_9.i.i.i.i = mul nuw nsw <4 x i64> %_5.i.i.i.i, splat (i64 19)
  %_6.i.i115.i.i.i = add nuw nsw <4 x i64> %_9.i.i.i.i, %_6.i.i17.i.i.i.i
  %_5.i13.i121.i.i.i = lshr <4 x i64> %_6.i.i115.i.i.i, splat (i64 26)
  %_6.i.i15.i122.i.i.i = add nuw nsw <4 x i64> %_5.i13.i121.i.i.i, %_6.i.i17.i55.i.i.i
  %97 = bitcast <4 x i64> %_6.i.i115.i.i.i to <8 x i32>
  %98 = and <8 x i32> %97, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %99 = bitcast <4 x i64> %_6.i.i15.i122.i.i.i to <8 x i32>
  %_16.i.i.i.i = shufflevector <8 x i32> %98, <8 x i32> %99, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  %100 = bitcast <4 x i64> %_6.i.i15.i53.i.i.i to <8 x i32>
  %101 = and <8 x i32> %100, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %102 = bitcast <4 x i64> %_6.i.i15.i67.i.i.i to <8 x i32>
  %103 = and <8 x i32> %102, <i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison>
  %_16.i128.i.i.i = shufflevector <8 x i32> %101, <8 x i32> %103, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  %104 = bitcast <4 x i64> %_6.i.i15.i95.i.i.i to <8 x i32>
  %105 = bitcast <4 x i64> %_6.i.i15.i81.i.i.i to <8 x i32>
  %106 = and <8 x i32> %105, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %_16.i131.i.i.i = shufflevector <8 x i32> %106, <8 x i32> %104, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  %107 = bitcast <4 x i64> %_6.i.i15.i60.i.i.i to <8 x i32>
  %108 = and <8 x i32> %107, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %109 = bitcast <4 x i64> %_6.i.i15.i74.i.i.i to <8 x i32>
  %110 = and <8 x i32> %109, <i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison>
  %_16.i134.i.i.i = shufflevector <8 x i32> %108, <8 x i32> %110, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  %111 = bitcast <4 x i64> %_6.i.i15.i88.i.i.i to <8 x i32>
  %112 = and <8 x i32> %111, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %113 = bitcast <4 x i64> %_6.i.i15.i102.i.i.i to <8 x i32>
  %114 = and <8 x i32> %113, <i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison>
  %_16.i137.i.i.i = shufflevector <8 x i32> %112, <8 x i32> %114, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  %_6.i.i.i = sub <8 x i32> <i32 1073741520, i32 1073741520, i32 536870896, i32 536870896, i32 1073741520, i32 1073741520, i32 536870896, i32 536870896>, %_16.i.i.i.i
  %_6.i10.i.i = sub nuw nsw <8 x i32> <i32 1073741808, i32 1073741808, i32 536870896, i32 536870896, i32 1073741808, i32 1073741808, i32 536870896, i32 536870896>, %_16.i128.i.i.i
  %_6.i11.i.i = sub nuw nsw <8 x i32> <i32 1073741808, i32 1073741808, i32 536870896, i32 536870896, i32 1073741808, i32 1073741808, i32 536870896, i32 536870896>, %_16.i131.i.i.i
  %_6.i12.i.i = sub nuw nsw <8 x i32> <i32 1073741808, i32 1073741808, i32 536870896, i32 536870896, i32 1073741808, i32 1073741808, i32 536870896, i32 536870896>, %_16.i134.i.i.i
  %_6.i13.i.i = sub nuw nsw <8 x i32> <i32 1073741808, i32 1073741808, i32 536870896, i32 536870896, i32 1073741808, i32 1073741808, i32 536870896, i32 536870896>, %_16.i137.i.i.i
  %_8.i.i.i.i.i = lshr <8 x i32> %_6.i.i.i, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i.i.i1.i = shufflevector <8 x i32> %_8.i.i.i.i.i, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 5>
  %_9.i40.i.i56.i = insertelement <8 x i32> %_9.i.i.i1.i, i32 0, i64 5
  %115 = and <8 x i32> %_6.i.i.i, <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 67108863, i32 poison, i32 33554431>
  %_6.i41.i.i.i = add nuw nsw <8 x i32> %_9.i40.i.i56.i, %115
  %_8.i.i43.i.i.i = lshr <8 x i32> %_6.i10.i.i, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i47.i.i.i = shufflevector <8 x i32> %_8.i.i.i.i.i, <8 x i32> %_8.i.i43.i.i.i, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 7, i32 poison, i32 13>
  %116 = and <8 x i32> %_6.i10.i.i, <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 67108863, i32 poison, i32 33554431>
  %_6.i48.i.i.i = add nuw nsw <8 x i32> %_9.i47.i.i.i, %116
  %_8.i.i50.i.i.i = lshr <8 x i32> %_6.i11.i.i, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i54.i.i.i = shufflevector <8 x i32> %_8.i.i43.i.i.i, <8 x i32> %_8.i.i50.i.i.i, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 7, i32 poison, i32 13>
  %117 = and <8 x i32> %_6.i11.i.i, <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 67108863, i32 poison, i32 33554431>
  %_6.i55.i.i.i = add nuw nsw <8 x i32> %_9.i54.i.i.i, %117
  %_8.i.i57.i.i.i = lshr <8 x i32> %_6.i12.i.i, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i61.i.i.i = shufflevector <8 x i32> %_8.i.i50.i.i.i, <8 x i32> %_8.i.i57.i.i.i, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 7, i32 poison, i32 13>
  %118 = and <8 x i32> %_6.i12.i.i, <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 67108863, i32 poison, i32 33554431>
  %_6.i62.i.i.i = add nuw nsw <8 x i32> %_9.i61.i.i.i, %118
  %_8.i.i64.i.i.i = lshr <8 x i32> %_6.i13.i.i, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i68.i.i.i = shufflevector <8 x i32> %_8.i.i57.i.i.i, <8 x i32> %_8.i.i64.i.i.i, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 7, i32 poison, i32 13>
  %119 = and <8 x i32> %_6.i13.i.i, <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 67108863, i32 poison, i32 33554431>
  %_6.i69.i.i.i = add nuw nsw <8 x i32> %_9.i68.i.i.i, %119
  %120 = and <8 x i32> %_8.i.i64.i.i.i, <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 0, i32 poison, i32 15>
  %_76.i.i.i.inner = shufflevector <8 x i32> %120, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 7, i32 5>
  %_76.i.i.i = bitcast <8 x i32> %_76.i.i.i.inner to <4 x i64>
  %_75.i.i.i = mul nuw nsw <4 x i64> %_76.i.i.i, <i64 poison, i64 poison, i64 poison, i64 19>
  %121 = bitcast <4 x i64> %_75.i.i.i to <8 x i32>
  %_78.i.i.i = shufflevector <8 x i32> %121, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 6, i32 poison, i32 7>
  %_6.i.i.i.i.i = add nuw nsw <8 x i32> %_6.i41.i.i.i, %_78.i.i.i
  %r.i190.i.i = shufflevector <8 x i32> %_16.i.i.i.i, <8 x i32> %_6.i.i.i.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i197.i.i = shufflevector <8 x i32> %_16.i128.i.i.i, <8 x i32> %_6.i48.i.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i204.i.i = shufflevector <8 x i32> %_16.i131.i.i.i, <8 x i32> %_6.i55.i.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i211.i.i = shufflevector <8 x i32> %_16.i134.i.i.i, <8 x i32> %_6.i62.i.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i218.i.i = shufflevector <8 x i32> %_16.i137.i.i.i, <8 x i32> %_6.i69.i.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  store <8 x i32> %r.i190.i.i, ptr %Ai, align 32
  %_5.sroa.4.0..sroa_idx = getelementptr inbounds nuw i8, ptr %Ai, i64 32
  store <8 x i32> %r.i197.i.i, ptr %_5.sroa.4.0..sroa_idx, align 32
  %_5.sroa.5.0..sroa_idx = getelementptr inbounds nuw i8, ptr %Ai, i64 64
  store <8 x i32> %r.i204.i.i, ptr %_5.sroa.5.0..sroa_idx, align 32
  %_5.sroa.6.0..sroa_idx = getelementptr inbounds nuw i8, ptr %Ai, i64 96
  store <8 x i32> %r.i211.i.i, ptr %_5.sroa.6.0..sroa_idx, align 32
  %_5.sroa.7.0..sroa_idx = getelementptr inbounds nuw i8, ptr %Ai, i64 128
  store <8 x i32> %r.i218.i.i, ptr %_5.sroa.7.0..sroa_idx, align 32
  %122 = getelementptr inbounds nuw i8, ptr %Ai, i64 160
  store <8 x i32> %r.i190.i.i, ptr %122, align 32
  %_5.sroa.4.0..sroa_idx.1 = getelementptr inbounds nuw i8, ptr %Ai, i64 192
  store <8 x i32> %r.i197.i.i, ptr %_5.sroa.4.0..sroa_idx.1, align 32
  %_5.sroa.5.0..sroa_idx.1 = getelementptr inbounds nuw i8, ptr %Ai, i64 224
  store <8 x i32> %r.i204.i.i, ptr %_5.sroa.5.0..sroa_idx.1, align 32
  %_5.sroa.6.0..sroa_idx.1 = getelementptr inbounds nuw i8, ptr %Ai, i64 256
  store <8 x i32> %r.i211.i.i, ptr %_5.sroa.6.0..sroa_idx.1, align 32
  %_5.sroa.7.0..sroa_idx.1 = getelementptr inbounds nuw i8, ptr %Ai, i64 288
  store <8 x i32> %r.i218.i.i, ptr %_5.sroa.7.0..sroa_idx.1, align 32
  %123 = getelementptr inbounds nuw i8, ptr %Ai, i64 320
  store <8 x i32> %r.i190.i.i, ptr %123, align 32
  %_5.sroa.4.0..sroa_idx.2 = getelementptr inbounds nuw i8, ptr %Ai, i64 352
  store <8 x i32> %r.i197.i.i, ptr %_5.sroa.4.0..sroa_idx.2, align 32
  %_5.sroa.5.0..sroa_idx.2 = getelementptr inbounds nuw i8, ptr %Ai, i64 384
  store <8 x i32> %r.i204.i.i, ptr %_5.sroa.5.0..sroa_idx.2, align 32
  %_5.sroa.6.0..sroa_idx.2 = getelementptr inbounds nuw i8, ptr %Ai, i64 416
  store <8 x i32> %r.i211.i.i, ptr %_5.sroa.6.0..sroa_idx.2, align 32
  %_5.sroa.7.0..sroa_idx.2 = getelementptr inbounds nuw i8, ptr %Ai, i64 448
  store <8 x i32> %r.i218.i.i, ptr %_5.sroa.7.0..sroa_idx.2, align 32
  %124 = getelementptr inbounds nuw i8, ptr %Ai, i64 480
  store <8 x i32> %r.i190.i.i, ptr %124, align 32
  %_5.sroa.4.0..sroa_idx.3 = getelementptr inbounds nuw i8, ptr %Ai, i64 512
  store <8 x i32> %r.i197.i.i, ptr %_5.sroa.4.0..sroa_idx.3, align 32
  %_5.sroa.5.0..sroa_idx.3 = getelementptr inbounds nuw i8, ptr %Ai, i64 544
  store <8 x i32> %r.i204.i.i, ptr %_5.sroa.5.0..sroa_idx.3, align 32
  %_5.sroa.6.0..sroa_idx.3 = getelementptr inbounds nuw i8, ptr %Ai, i64 576
  store <8 x i32> %r.i211.i.i, ptr %_5.sroa.6.0..sroa_idx.3, align 32
  %_5.sroa.7.0..sroa_idx.3 = getelementptr inbounds nuw i8, ptr %Ai, i64 608
  store <8 x i32> %r.i218.i.i, ptr %_5.sroa.7.0..sroa_idx.3, align 32
  %125 = getelementptr inbounds nuw i8, ptr %Ai, i64 640
  store <8 x i32> %r.i190.i.i, ptr %125, align 32
  %_5.sroa.4.0..sroa_idx.4 = getelementptr inbounds nuw i8, ptr %Ai, i64 672
  store <8 x i32> %r.i197.i.i, ptr %_5.sroa.4.0..sroa_idx.4, align 32
  %_5.sroa.5.0..sroa_idx.4 = getelementptr inbounds nuw i8, ptr %Ai, i64 704
  store <8 x i32> %r.i204.i.i, ptr %_5.sroa.5.0..sroa_idx.4, align 32
  %_5.sroa.6.0..sroa_idx.4 = getelementptr inbounds nuw i8, ptr %Ai, i64 736
  store <8 x i32> %r.i211.i.i, ptr %_5.sroa.6.0..sroa_idx.4, align 32
  %_5.sroa.7.0..sroa_idx.4 = getelementptr inbounds nuw i8, ptr %Ai, i64 768
  store <8 x i32> %r.i218.i.i, ptr %_5.sroa.7.0..sroa_idx.4, align 32
  %126 = getelementptr inbounds nuw i8, ptr %Ai, i64 800
  store <8 x i32> %r.i190.i.i, ptr %126, align 32
  %_5.sroa.4.0..sroa_idx.5 = getelementptr inbounds nuw i8, ptr %Ai, i64 832
  store <8 x i32> %r.i197.i.i, ptr %_5.sroa.4.0..sroa_idx.5, align 32
  %_5.sroa.5.0..sroa_idx.5 = getelementptr inbounds nuw i8, ptr %Ai, i64 864
  store <8 x i32> %r.i204.i.i, ptr %_5.sroa.5.0..sroa_idx.5, align 32
  %_5.sroa.6.0..sroa_idx.5 = getelementptr inbounds nuw i8, ptr %Ai, i64 896
  store <8 x i32> %r.i211.i.i, ptr %_5.sroa.6.0..sroa_idx.5, align 32
  %_5.sroa.7.0..sroa_idx.5 = getelementptr inbounds nuw i8, ptr %Ai, i64 928
  store <8 x i32> %r.i218.i.i, ptr %_5.sroa.7.0..sroa_idx.5, align 32
  %127 = getelementptr inbounds nuw i8, ptr %Ai, i64 960
  store <8 x i32> %r.i190.i.i, ptr %127, align 32
  %_5.sroa.4.0..sroa_idx.6 = getelementptr inbounds nuw i8, ptr %Ai, i64 992
  store <8 x i32> %r.i197.i.i, ptr %_5.sroa.4.0..sroa_idx.6, align 32
  %_5.sroa.5.0..sroa_idx.6 = getelementptr inbounds nuw i8, ptr %Ai, i64 1024
  store <8 x i32> %r.i204.i.i, ptr %_5.sroa.5.0..sroa_idx.6, align 32
  %_5.sroa.6.0..sroa_idx.6 = getelementptr inbounds nuw i8, ptr %Ai, i64 1056
  store <8 x i32> %r.i211.i.i, ptr %_5.sroa.6.0..sroa_idx.6, align 32
  %_5.sroa.7.0..sroa_idx.6 = getelementptr inbounds nuw i8, ptr %Ai, i64 1088
  store <8 x i32> %r.i218.i.i, ptr %_5.sroa.7.0..sroa_idx.6, align 32
  %128 = getelementptr inbounds nuw i8, ptr %Ai, i64 1120
  store <8 x i32> %r.i190.i.i, ptr %128, align 32
  %_5.sroa.4.0..sroa_idx.7 = getelementptr inbounds nuw i8, ptr %Ai, i64 1152
  store <8 x i32> %r.i197.i.i, ptr %_5.sroa.4.0..sroa_idx.7, align 32
  %_5.sroa.5.0..sroa_idx.7 = getelementptr inbounds nuw i8, ptr %Ai, i64 1184
  store <8 x i32> %r.i204.i.i, ptr %_5.sroa.5.0..sroa_idx.7, align 32
  %_5.sroa.6.0..sroa_idx.7 = getelementptr inbounds nuw i8, ptr %Ai, i64 1216
  store <8 x i32> %r.i211.i.i, ptr %_5.sroa.6.0..sroa_idx.7, align 32
  %_5.sroa.7.0..sroa_idx.7 = getelementptr inbounds nuw i8, ptr %Ai, i64 1248
  store <8 x i32> %r.i218.i.i, ptr %_5.sroa.7.0..sroa_idx.7, align 32
  call void @llvm.lifetime.start.p0(ptr nonnull %A2)
  call void @llvm.lifetime.start.p0(ptr nonnull %tmp0.i), !noalias !4
  %_3.i214.i.i = shufflevector <8 x i32> %_6.i.i.i.i50, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 1, i32 poison, i32 3>
  %_3.i74266.i.i = shufflevector <8 x i32> %_6.i48.i.i, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 1, i32 poison, i32 3>
  %_3.i75320.i.i = shufflevector <8 x i32> %_6.i55.i.i, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 1, i32 poison, i32 3>
  %_3.i76374.i.i = shufflevector <8 x i32> %_6.i62.i.i, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 1, i32 poison, i32 3>
  %_3.i77.i.i = shufflevector <8 x i32> %_6.i69.i.i, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 1, i32 poison, i32 3>
  %_3.sroa.4.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %tmp0.i, i64 32
  %_3.sroa.5.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %tmp0.i, i64 64
  %_3.sroa.6.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %tmp0.i, i64 96
  %_3.sroa.7.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %tmp0.i, i64 128
  call void @llvm.lifetime.start.p0(ptr nonnull %tmp1.i), !noalias !4
  %_3.i219.i.i = shufflevector <8 x i32> %_6.i.i.i.i50, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 0, i32 poison, i32 2>
  %_3.i74272.i.i = shufflevector <8 x i32> %_6.i48.i.i, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 0, i32 poison, i32 2>
  %_3.i75326.i.i = shufflevector <8 x i32> %_6.i55.i.i, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 0, i32 poison, i32 2>
  %_3.i76380.i.i = shufflevector <8 x i32> %_6.i62.i.i, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 0, i32 poison, i32 2>
  %_3.i77.i7.i = shufflevector <8 x i32> %_6.i69.i.i, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 0, i32 poison, i32 2>
  %_3.sroa.4.0._0.sroa_idx.i8.i = getelementptr inbounds nuw i8, ptr %tmp1.i, i64 32
  %_3.sroa.5.0._0.sroa_idx.i9.i = getelementptr inbounds nuw i8, ptr %tmp1.i, i64 64
  %_3.sroa.6.0._0.sroa_idx.i10.i = getelementptr inbounds nuw i8, ptr %tmp1.i, i64 96
  %_3.sroa.7.0._0.sroa_idx.i11.i = getelementptr inbounds nuw i8, ptr %tmp1.i, i64 128
  %_6.i.i.i4 = add <8 x i32> %_3.i219.i.i, %_3.i214.i.i
  %_6.i10.i.i5 = add <8 x i32> %_3.i74272.i.i, %_3.i74266.i.i
  %_6.i11.i.i6 = add <8 x i32> %_3.i75326.i.i, %_3.i75320.i.i
  %_6.i12.i.i7 = add <8 x i32> %_3.i76380.i.i, %_3.i76374.i.i
  %_6.i13.i.i8 = add <8 x i32> %_3.i77.i7.i, %_3.i77.i.i
  %r.i190.i.i9 = shufflevector <8 x i32> %_6.i.i.i.i50, <8 x i32> %_6.i.i.i4, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i197.i.i10 = shufflevector <8 x i32> %_6.i48.i.i, <8 x i32> %_6.i10.i.i5, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i204.i.i11 = shufflevector <8 x i32> %_6.i55.i.i, <8 x i32> %_6.i11.i.i6, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i211.i.i12 = shufflevector <8 x i32> %_6.i62.i.i, <8 x i32> %_6.i12.i.i7, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i218.i.i13 = shufflevector <8 x i32> %_6.i69.i.i, <8 x i32> %_6.i13.i.i8, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  store <8 x i32> %r.i190.i.i9, ptr %tmp0.i, align 32, !noalias !4
  store <8 x i32> %r.i197.i.i10, ptr %_3.sroa.4.0._0.sroa_idx.i.i, align 32, !noalias !4
  store <8 x i32> %r.i204.i.i11, ptr %_3.sroa.5.0._0.sroa_idx.i.i, align 32, !noalias !4
  store <8 x i32> %r.i211.i.i12, ptr %_3.sroa.6.0._0.sroa_idx.i.i, align 32, !noalias !4
  store <8 x i32> %r.i218.i.i13, ptr %_3.sroa.7.0._0.sroa_idx.i.i, align 32, !noalias !4
  call void @_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x419square_and_negate_DB1a_NtB2_28___Impl_square_and_negate_D__25__impl_square_and_negate_D(ptr noalias nofree noundef nonnull sret([160 x i8]) align 32 captures(address) dereferenceable(160) %tmp1.i, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %tmp0.i) #5, !noalias !4
  %_5423.i16.i = load <8 x i32>, ptr %tmp1.i, align 32, !alias.scope !8, !noalias !11
  %_7184416.i17.i = load <8 x i32>, ptr %_3.sroa.4.0._0.sroa_idx.i8.i, align 32, !alias.scope !8, !noalias !11
  %_9230417.i18.i = load <8 x i32>, ptr %_3.sroa.5.0._0.sroa_idx.i9.i, align 32, !alias.scope !8, !noalias !11
  %_11284418.i19.i = load <8 x i32>, ptr %_3.sroa.6.0._0.sroa_idx.i10.i, align 32, !alias.scope !8, !noalias !11
  %_3.i183.i.i = shufflevector <8 x i32> %_5423.i16.i, <8 x i32> poison, <8 x i32> <i32 0, i32 0, i32 2, i32 2, i32 0, i32 0, i32 2, i32 2>
  %_3.i74229.i.i = shufflevector <8 x i32> %_7184416.i17.i, <8 x i32> poison, <8 x i32> <i32 0, i32 0, i32 2, i32 2, i32 0, i32 0, i32 2, i32 2>
  %_3.i75283.i.i = shufflevector <8 x i32> %_9230417.i18.i, <8 x i32> poison, <8 x i32> <i32 0, i32 0, i32 2, i32 2, i32 0, i32 0, i32 2, i32 2>
  %_3.i76337.i.i = shufflevector <8 x i32> %_11284418.i19.i, <8 x i32> poison, <8 x i32> <i32 0, i32 0, i32 2, i32 2, i32 0, i32 0, i32 2, i32 2>
  %_13339419.i21.i = load <8 x i32>, ptr %_3.sroa.7.0._0.sroa_idx.i11.i, align 32, !alias.scope !8, !noalias !11
  %_3.i77.i22.i = shufflevector <8 x i32> %_13339419.i21.i, <8 x i32> poison, <8 x i32> <i32 0, i32 0, i32 2, i32 2, i32 0, i32 0, i32 2, i32 2>
  %_3.i189.i.i = shufflevector <8 x i32> %_5423.i16.i, <8 x i32> poison, <8 x i32> <i32 1, i32 1, i32 3, i32 3, i32 1, i32 1, i32 3, i32 3>
  %_3.i74236.i.i = shufflevector <8 x i32> %_7184416.i17.i, <8 x i32> poison, <8 x i32> <i32 1, i32 1, i32 3, i32 3, i32 1, i32 1, i32 3, i32 3>
  %_3.i75290.i.i = shufflevector <8 x i32> %_9230417.i18.i, <8 x i32> poison, <8 x i32> <i32 1, i32 1, i32 3, i32 3, i32 1, i32 1, i32 3, i32 3>
  %_3.i76344.i.i = shufflevector <8 x i32> %_11284418.i19.i, <8 x i32> poison, <8 x i32> <i32 1, i32 1, i32 3, i32 3, i32 1, i32 1, i32 3, i32 3>
  %_3.i77.i33.i = shufflevector <8 x i32> %_13339419.i21.i, <8 x i32> poison, <8 x i32> <i32 1, i32 1, i32 3, i32 3, i32 1, i32 1, i32 3, i32 3>
  %_6.i.i40.i = shl <8 x i32> %_5423.i16.i, splat (i32 1)
  %_6.i10.i43.i = shl <8 x i32> %_7184416.i17.i, splat (i32 1)
  %_6.i11.i46.i = shl <8 x i32> %_9230417.i18.i, splat (i32 1)
  %_6.i12.i49.i = shl <8 x i32> %_11284418.i19.i, splat (i32 1)
  %_6.i13.i52.i = shl <8 x i32> %_13339419.i21.i, splat (i32 1)
  %r.i.i.i = shufflevector <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 poison, i32 poison, i32 poison, i32 poison>, <8 x i32> %_6.i.i40.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 poison, i32 14, i32 poison>
  %r.i196.i.i = shufflevector <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 poison, i32 poison, i32 poison, i32 poison>, <8 x i32> %_6.i10.i43.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 poison, i32 14, i32 poison>
  %r.i203.i.i = shufflevector <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 poison, i32 poison, i32 poison, i32 poison>, <8 x i32> %_6.i11.i46.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 poison, i32 14, i32 poison>
  %r.i210.i.i = shufflevector <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 poison, i32 poison, i32 poison, i32 poison>, <8 x i32> %_6.i12.i49.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 poison, i32 14, i32 poison>
  %r.i217.i.i = shufflevector <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 poison, i32 poison, i32 poison, i32 poison>, <8 x i32> %_6.i13.i52.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 poison, i32 14, i32 poison>
  %r.i190.i81.i = shufflevector <8 x i32> %r.i.i.i, <8 x i32> %_5423.i16.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i197.i82.i = shufflevector <8 x i32> %r.i196.i.i, <8 x i32> %_7184416.i17.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i204.i83.i = shufflevector <8 x i32> %r.i203.i.i, <8 x i32> %_9230417.i18.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i211.i84.i = shufflevector <8 x i32> %r.i210.i.i, <8 x i32> %_11284418.i19.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i218.i85.i = shufflevector <8 x i32> %r.i217.i.i, <8 x i32> %_13339419.i21.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i194.i.i = shufflevector <8 x i32> %_3.i189.i.i, <8 x i32> <i32 poison, i32 0, i32 poison, i32 0, i32 0, i32 poison, i32 0, i32 poison>, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %r.i201.i.i = shufflevector <8 x i32> %_3.i74236.i.i, <8 x i32> <i32 poison, i32 0, i32 poison, i32 0, i32 0, i32 poison, i32 0, i32 poison>, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %r.i208.i.i = shufflevector <8 x i32> %_3.i75290.i.i, <8 x i32> <i32 poison, i32 0, i32 poison, i32 0, i32 0, i32 poison, i32 0, i32 poison>, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %r.i215.i.i = shufflevector <8 x i32> %_3.i76344.i.i, <8 x i32> <i32 poison, i32 0, i32 poison, i32 0, i32 0, i32 poison, i32 0, i32 poison>, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %r.i222.i.i = shufflevector <8 x i32> %_3.i77.i33.i, <8 x i32> <i32 poison, i32 0, i32 poison, i32 0, i32 0, i32 poison, i32 0, i32 poison>, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %_6.i.i142.i = sub <8 x i32> <i32 poison, i32 134217690, i32 poison, i32 67108862, i32 134217690, i32 poison, i32 67108862, i32 poison>, %_3.i189.i.i
  %_6.i10.i143.i = sub <8 x i32> <i32 poison, i32 134217726, i32 poison, i32 67108862, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i74236.i.i
  %_6.i11.i144.i = sub <8 x i32> <i32 poison, i32 134217726, i32 poison, i32 67108862, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i75290.i.i
  %_6.i12.i145.i = sub <8 x i32> <i32 poison, i32 134217726, i32 poison, i32 67108862, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i76344.i.i
  %_6.i13.i146.i = sub <8 x i32> <i32 poison, i32 134217726, i32 poison, i32 67108862, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i77.i33.i
  %r.i195.i.i = shufflevector <8 x i32> <i32 0, i32 poison, i32 0, i32 poison, i32 poison, i32 0, i32 poison, i32 0>, <8 x i32> %_6.i.i142.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %r.i202.i.i = shufflevector <8 x i32> <i32 0, i32 poison, i32 0, i32 poison, i32 poison, i32 0, i32 poison, i32 0>, <8 x i32> %_6.i10.i143.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %r.i209.i.i = shufflevector <8 x i32> <i32 0, i32 poison, i32 0, i32 poison, i32 poison, i32 0, i32 poison, i32 0>, <8 x i32> %_6.i11.i144.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %r.i216.i.i = shufflevector <8 x i32> <i32 0, i32 poison, i32 0, i32 poison, i32 poison, i32 0, i32 poison, i32 0>, <8 x i32> %_6.i12.i145.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %r.i223.i.i = shufflevector <8 x i32> <i32 0, i32 poison, i32 0, i32 poison, i32 poison, i32 0, i32 poison, i32 0>, <8 x i32> %_6.i13.i146.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %_6.i.i92.i = add <8 x i32> %r.i194.i.i, %_3.i183.i.i
  %_6.i.i125.i = add <8 x i32> %_6.i.i92.i, %r.i190.i81.i
  %_6.i.i163.i = add <8 x i32> %_6.i.i125.i, %r.i195.i.i
  %_6.i10.i95.i = add <8 x i32> %r.i201.i.i, %_3.i74229.i.i
  %_6.i10.i128.i = add <8 x i32> %_6.i10.i95.i, %r.i197.i82.i
  %_6.i10.i166.i = add <8 x i32> %_6.i10.i128.i, %r.i202.i.i
  %_6.i11.i98.i = add <8 x i32> %r.i208.i.i, %_3.i75283.i.i
  %_6.i11.i131.i = add <8 x i32> %_6.i11.i98.i, %r.i204.i83.i
  %_6.i11.i169.i = add <8 x i32> %_6.i11.i131.i, %r.i209.i.i
  %_6.i12.i101.i = add <8 x i32> %r.i215.i.i, %_3.i76337.i.i
  %_6.i12.i134.i = add <8 x i32> %_6.i12.i101.i, %r.i211.i84.i
  %_6.i12.i172.i = add <8 x i32> %_6.i12.i134.i, %r.i216.i.i
  %_6.i13.i104.i = add <8 x i32> %r.i222.i.i, %_3.i77.i22.i
  %_6.i13.i137.i = add <8 x i32> %_6.i13.i104.i, %r.i218.i85.i
  %_6.i13.i175.i = add <8 x i32> %_6.i13.i137.i, %r.i223.i.i
  %_3.i199.i.i = shufflevector <8 x i32> %_6.i.i163.i, <8 x i32> poison, <8 x i32> <i32 5, i32 1, i32 7, i32 3, i32 1, i32 5, i32 3, i32 7>
  %_3.i74248.i.i = shufflevector <8 x i32> %_6.i10.i166.i, <8 x i32> poison, <8 x i32> <i32 5, i32 1, i32 7, i32 3, i32 1, i32 5, i32 3, i32 7>
  %_3.i75302.i.i = shufflevector <8 x i32> %_6.i11.i169.i, <8 x i32> poison, <8 x i32> <i32 5, i32 1, i32 7, i32 3, i32 1, i32 5, i32 3, i32 7>
  %_3.i76356.i.i = shufflevector <8 x i32> %_6.i12.i172.i, <8 x i32> poison, <8 x i32> <i32 5, i32 1, i32 7, i32 3, i32 1, i32 5, i32 3, i32 7>
  %_3.i77.i186.i = shufflevector <8 x i32> %_6.i13.i175.i, <8 x i32> poison, <8 x i32> <i32 5, i32 1, i32 7, i32 3, i32 1, i32 5, i32 3, i32 7>
  store <8 x i32> %_3.i199.i.i, ptr %tmp1.i, align 32, !noalias !4
  store <8 x i32> %_3.i74248.i.i, ptr %_3.sroa.4.0._0.sroa_idx.i8.i, align 32, !noalias !4
  store <8 x i32> %_3.i75302.i.i, ptr %_3.sroa.5.0._0.sroa_idx.i9.i, align 32, !noalias !4
  store <8 x i32> %_3.i76356.i.i, ptr %_3.sroa.6.0._0.sroa_idx.i10.i, align 32, !noalias !4
  store <8 x i32> %_3.i77.i186.i, ptr %_3.sroa.7.0._0.sroa_idx.i11.i, align 32, !noalias !4
  %_3.i194.i.i = shufflevector <8 x i32> %_6.i.i163.i, <8 x i32> poison, <8 x i32> <i32 4, i32 0, i32 6, i32 2, i32 4, i32 0, i32 6, i32 2>
  %_3.i74242.i.i = shufflevector <8 x i32> %_6.i10.i166.i, <8 x i32> poison, <8 x i32> <i32 4, i32 0, i32 6, i32 2, i32 4, i32 0, i32 6, i32 2>
  %_3.i75296.i.i = shufflevector <8 x i32> %_6.i11.i169.i, <8 x i32> poison, <8 x i32> <i32 4, i32 0, i32 6, i32 2, i32 4, i32 0, i32 6, i32 2>
  %_3.i76350.i.i = shufflevector <8 x i32> %_6.i12.i172.i, <8 x i32> poison, <8 x i32> <i32 4, i32 0, i32 6, i32 2, i32 4, i32 0, i32 6, i32 2>
  %_3.i77.i197.i = shufflevector <8 x i32> %_6.i13.i175.i, <8 x i32> poison, <8 x i32> <i32 4, i32 0, i32 6, i32 2, i32 4, i32 0, i32 6, i32 2>
  store <8 x i32> %_3.i194.i.i, ptr %tmp0.i, align 32, !noalias !4
  store <8 x i32> %_3.i74242.i.i, ptr %_3.sroa.4.0._0.sroa_idx.i.i, align 32, !noalias !4
  store <8 x i32> %_3.i75296.i.i, ptr %_3.sroa.5.0._0.sroa_idx.i.i, align 32, !noalias !4
  store <8 x i32> %_3.i76350.i.i, ptr %_3.sroa.6.0._0.sroa_idx.i.i, align 32, !noalias !4
  store <8 x i32> %_3.i77.i197.i, ptr %_3.sroa.7.0._0.sroa_idx.i.i, align 32, !noalias !4
  call fastcc void @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul(ptr noalias nofree noundef nonnull align 32 captures(address) dereferenceable(160) %A2, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %tmp0.i, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %tmp1.i) #6, !noalias !13
  call void @llvm.lifetime.end.p0(ptr nonnull %tmp1.i), !noalias !4
  call void @llvm.lifetime.end.p0(ptr nonnull %tmp0.i), !noalias !4
  %129 = getelementptr inbounds nuw i8, ptr %tmp.i, i64 32
  %130 = getelementptr inbounds nuw i8, ptr %tmp.i, i64 64
  %131 = getelementptr inbounds nuw i8, ptr %tmp.i, i64 96
  %_13339.in.i.i.i = getelementptr inbounds nuw i8, ptr %tmp.i, i64 128
  %_3.sroa.4.0._0.sroa_idx.i38.i = getelementptr inbounds nuw i8, ptr %t0.i, i64 32
  %_3.sroa.5.0._0.sroa_idx.i39.i = getelementptr inbounds nuw i8, ptr %t0.i, i64 64
  %_3.sroa.6.0._0.sroa_idx.i40.i = getelementptr inbounds nuw i8, ptr %t0.i, i64 96
  %_3.sroa.7.0._0.sroa_idx.i41.i = getelementptr inbounds nuw i8, ptr %t0.i, i64 128
  %_3.sroa.4.0._0.sroa_idx.i49.i = getelementptr inbounds nuw i8, ptr %t1.i, i64 32
  %_3.sroa.5.0._0.sroa_idx.i50.i = getelementptr inbounds nuw i8, ptr %t1.i, i64 64
  %_3.sroa.6.0._0.sroa_idx.i51.i = getelementptr inbounds nuw i8, ptr %t1.i, i64 96
  %_3.sroa.7.0._0.sroa_idx.i52.i = getelementptr inbounds nuw i8, ptr %t1.i, i64 128
  %x.sroa.12.0.P.sroa_idx.i52 = getelementptr inbounds nuw i8, ptr %_15, i64 32
  %x.sroa.15.0.P.sroa_idx.i54 = getelementptr inbounds nuw i8, ptr %_15, i64 64
  %x.sroa.18.0.P.sroa_idx.i56 = getelementptr inbounds nuw i8, ptr %_15, i64 96
  %x.sroa.21.0.P.sroa_idx.i58 = getelementptr inbounds nuw i8, ptr %_15, i64 128
  br label %bb13

bb9:                                              ; preds = %bb13
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 32 dereferenceable(1280) %_0, ptr noundef nonnull align 32 dereferenceable(1280) %Ai, i64 1280, i1 false)
  call void @llvm.lifetime.end.p0(ptr nonnull %A2)
  ret void

bb13:                                             ; preds = %bb13, %start
  %iter.sroa.0.0191 = phi i64 [ 0, %start ], [ %_0.i1.i.i, %bb13 ]
  %_0.i1.i.i = add nuw nsw i64 %iter.sroa.0.0191, 1
  call void @llvm.lifetime.start.p0(ptr nonnull %_15)
  %_17 = getelementptr inbounds nuw %"backend::vector::avx2::edwards::CachedPoint", ptr %Ai, i64 %iter.sroa.0.0191
  call void @llvm.lifetime.start.p0(ptr nonnull %tmp.i), !noalias !14
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 32 dereferenceable(160) %tmp.i, ptr noundef nonnull readonly align 32 dereferenceable(160) %A2, i64 160, i1 false), !noalias !19
  %_5423.i.i.i = load <8 x i32>, ptr %tmp.i, align 32, !alias.scope !20, !noalias !25
  %_7184416.i.i.i = load <8 x i32>, ptr %129, align 32, !alias.scope !20, !noalias !25
  %_9230417.i.i.i = load <8 x i32>, ptr %130, align 32, !alias.scope !20, !noalias !25
  %_11284418.i.i.i = load <8 x i32>, ptr %131, align 32, !alias.scope !20, !noalias !25
  %_3.i219.i.i.i14 = shufflevector <8 x i32> %_5423.i.i.i, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i74272.i.i.i15 = shufflevector <8 x i32> %_7184416.i.i.i, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i75326.i.i.i16 = shufflevector <8 x i32> %_9230417.i.i.i, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i76380.i.i.i17 = shufflevector <8 x i32> %_11284418.i.i.i, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_13339419.i.i.i = load <8 x i32>, ptr %_13339.in.i.i.i, align 32, !alias.scope !20, !noalias !25
  %_3.i77.i.i.i18 = shufflevector <8 x i32> %_13339419.i.i.i, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_6.i.i.i.i19 = sub <8 x i32> <i32 134217690, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %_5423.i.i.i
  %_6.i10.i.i.i20 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %_7184416.i.i.i
  %_6.i11.i.i.i21 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %_9230417.i.i.i
  %_6.i12.i.i.i22 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %_11284418.i.i.i
  %_6.i13.i.i.i23 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %_13339419.i.i.i
  %r.i192.i.i.i24 = shufflevector <8 x i32> %_6.i.i.i.i19, <8 x i32> %_5423.i.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i199.i.i.i25 = shufflevector <8 x i32> %_6.i10.i.i.i20, <8 x i32> %_7184416.i.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i206.i.i.i26 = shufflevector <8 x i32> %_6.i11.i.i.i21, <8 x i32> %_9230417.i.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i213.i.i.i27 = shufflevector <8 x i32> %_6.i12.i.i.i22, <8 x i32> %_11284418.i.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i220.i.i.i28 = shufflevector <8 x i32> %_6.i13.i.i.i23, <8 x i32> %_13339419.i.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %_6.i.i1.i.i29 = add <8 x i32> %r.i192.i.i.i24, %_3.i219.i.i.i14
  %_6.i10.i2.i.i30 = add <8 x i32> %r.i199.i.i.i25, %_3.i74272.i.i.i15
  %_6.i11.i3.i.i31 = add <8 x i32> %r.i206.i.i.i26, %_3.i75326.i.i.i16
  %_6.i12.i4.i.i32 = add <8 x i32> %r.i213.i.i.i27, %_3.i76380.i.i.i17
  %_6.i13.i5.i.i33 = add <8 x i32> %r.i220.i.i.i28, %_3.i77.i.i.i18
  %r.i191.i.i34 = shufflevector <8 x i32> %_6.i.i1.i.i29, <8 x i32> %_5423.i.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i198.i.i35 = shufflevector <8 x i32> %_6.i10.i2.i.i30, <8 x i32> %_7184416.i.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i205.i.i36 = shufflevector <8 x i32> %_6.i11.i3.i.i31, <8 x i32> %_9230417.i.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i212.i.i37 = shufflevector <8 x i32> %_6.i12.i4.i.i32, <8 x i32> %_11284418.i.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i219.i.i38 = shufflevector <8 x i32> %_6.i13.i5.i.i33, <8 x i32> %_13339419.i.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  store <8 x i32> %r.i191.i.i34, ptr %tmp.i, align 32, !noalias !14
  store <8 x i32> %r.i198.i.i35, ptr %129, align 32, !noalias !14
  store <8 x i32> %r.i205.i.i36, ptr %130, align 32, !noalias !14
  store <8 x i32> %r.i212.i.i37, ptr %131, align 32, !noalias !14
  store <8 x i32> %r.i219.i.i38, ptr %_13339.in.i.i.i, align 32, !noalias !14
  call void @llvm.lifetime.start.p0(ptr nonnull %_8.i), !noalias !14
  call fastcc void @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul(ptr noalias nofree noundef nonnull align 32 captures(address) dereferenceable(160) %_8.i, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %tmp.i, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %_17) #6
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 32 dereferenceable(160) %tmp.i, ptr noundef nonnull align 32 dereferenceable(160) %_8.i, i64 160, i1 false), !noalias !14
  call void @llvm.lifetime.end.p0(ptr nonnull %_8.i), !noalias !14
  %_5423.i.i39 = load <8 x i32>, ptr %tmp.i, align 32, !alias.scope !28, !noalias !31
  %_7184416.i.i40 = load <8 x i32>, ptr %129, align 32, !alias.scope !28, !noalias !31
  %_9230417.i.i41 = load <8 x i32>, ptr %130, align 32, !alias.scope !28, !noalias !31
  %_11284418.i.i42 = load <8 x i32>, ptr %131, align 32, !alias.scope !28, !noalias !31
  %_3.i.i.i43 = shufflevector <8 x i32> %_5423.i.i39, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i74.i.i = shufflevector <8 x i32> %_7184416.i.i40, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i75.i.i = shufflevector <8 x i32> %_9230417.i.i41, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i76.i.i = shufflevector <8 x i32> %_11284418.i.i42, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_13339419.i.i44 = load <8 x i32>, ptr %_13339.in.i.i.i, align 32, !alias.scope !28, !noalias !31
  %_3.i77.i.i45 = shufflevector <8 x i32> %_13339419.i.i44, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i219.i.i5.i = shufflevector <8 x i32> %_5423.i.i39, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i74272.i.i6.i = shufflevector <8 x i32> %_7184416.i.i40, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i75326.i.i7.i = shufflevector <8 x i32> %_9230417.i.i41, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i76380.i.i8.i = shufflevector <8 x i32> %_11284418.i.i42, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i77.i.i11.i = shufflevector <8 x i32> %_13339419.i.i44, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_6.i.i.i12.i = sub <8 x i32> <i32 134217690, i32 poison, i32 67108862, i32 poison, i32 134217690, i32 poison, i32 67108862, i32 poison>, %_3.i.i.i43
  %_6.i10.i.i13.i = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i74.i.i
  %_6.i11.i.i14.i = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i75.i.i
  %_6.i12.i.i15.i = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i76.i.i
  %_6.i13.i.i16.i = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i77.i.i45
  %r.i192.i.i17.i = shufflevector <8 x i32> %_6.i.i.i12.i, <8 x i32> %_3.i.i.i43, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i199.i.i18.i = shufflevector <8 x i32> %_6.i10.i.i13.i, <8 x i32> %_3.i74.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i206.i.i19.i = shufflevector <8 x i32> %_6.i11.i.i14.i, <8 x i32> %_3.i75.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i213.i.i20.i = shufflevector <8 x i32> %_6.i12.i.i15.i, <8 x i32> %_3.i76.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i220.i.i21.i = shufflevector <8 x i32> %_6.i13.i.i16.i, <8 x i32> %_3.i77.i.i45, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %_6.i.i1.i22.i = add <8 x i32> %r.i192.i.i17.i, %_3.i219.i.i5.i
  %_6.i10.i2.i23.i = add <8 x i32> %r.i199.i.i18.i, %_3.i74272.i.i6.i
  %_6.i11.i3.i24.i = add <8 x i32> %r.i206.i.i19.i, %_3.i75326.i.i7.i
  %_6.i12.i4.i25.i = add <8 x i32> %r.i213.i.i20.i, %_3.i76380.i.i8.i
  %_6.i13.i5.i26.i = add <8 x i32> %r.i220.i.i21.i, %_3.i77.i.i11.i
  call void @llvm.lifetime.start.p0(ptr nonnull %t0.i), !noalias !14
  %_3.i204.i.i = shufflevector <8 x i32> %_6.i.i1.i22.i, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i74254.i.i = shufflevector <8 x i32> %_6.i10.i2.i23.i, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i75308.i.i = shufflevector <8 x i32> %_6.i11.i3.i24.i, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i76362.i.i = shufflevector <8 x i32> %_6.i12.i4.i25.i, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i77.i37.i = shufflevector <8 x i32> %_6.i13.i5.i26.i, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  store <8 x i32> %_3.i204.i.i, ptr %t0.i, align 32, !alias.scope !33, !noalias !36
  store <8 x i32> %_3.i74254.i.i, ptr %_3.sroa.4.0._0.sroa_idx.i38.i, align 32, !alias.scope !33, !noalias !36
  store <8 x i32> %_3.i75308.i.i, ptr %_3.sroa.5.0._0.sroa_idx.i39.i, align 32, !alias.scope !33, !noalias !36
  store <8 x i32> %_3.i76362.i.i, ptr %_3.sroa.6.0._0.sroa_idx.i40.i, align 32, !alias.scope !33, !noalias !36
  store <8 x i32> %_3.i77.i37.i, ptr %_3.sroa.7.0._0.sroa_idx.i41.i, align 32, !alias.scope !33, !noalias !36
  call void @llvm.lifetime.start.p0(ptr nonnull %t1.i), !noalias !14
  %_3.i209.i.i = shufflevector <8 x i32> %_6.i.i1.i22.i, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i74260.i.i = shufflevector <8 x i32> %_6.i10.i2.i23.i, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i75314.i.i = shufflevector <8 x i32> %_6.i11.i3.i24.i, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i76368.i.i = shufflevector <8 x i32> %_6.i12.i4.i25.i, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i77.i48.i = shufflevector <8 x i32> %_6.i13.i5.i26.i, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  store <8 x i32> %_3.i209.i.i, ptr %t1.i, align 32, !alias.scope !38, !noalias !41
  store <8 x i32> %_3.i74260.i.i, ptr %_3.sroa.4.0._0.sroa_idx.i49.i, align 32, !alias.scope !38, !noalias !41
  store <8 x i32> %_3.i75314.i.i, ptr %_3.sroa.5.0._0.sroa_idx.i50.i, align 32, !alias.scope !38, !noalias !41
  store <8 x i32> %_3.i76368.i.i, ptr %_3.sroa.6.0._0.sroa_idx.i51.i, align 32, !alias.scope !38, !noalias !41
  store <8 x i32> %_3.i77.i48.i, ptr %_3.sroa.7.0._0.sroa_idx.i52.i, align 32, !alias.scope !38, !noalias !41
  call fastcc void @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul(ptr noalias nofree noundef nonnull align 32 captures(address) dereferenceable(160) %_15, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %t0.i, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %t1.i) #6, !noalias !43
  call void @llvm.lifetime.end.p0(ptr nonnull %t1.i), !noalias !14
  call void @llvm.lifetime.end.p0(ptr nonnull %t0.i), !noalias !14
  call void @llvm.lifetime.end.p0(ptr nonnull %tmp.i), !noalias !14
  %x.sroa.0.0.copyload.i51 = load <8 x i32>, ptr %_15, align 32, !alias.scope !44, !noalias !50
  %x.sroa.12.0.copyload.i53 = load <8 x i32>, ptr %x.sroa.12.0.P.sroa_idx.i52, align 32, !alias.scope !44, !noalias !50
  %x.sroa.15.0.copyload.i55 = load <8 x i32>, ptr %x.sroa.15.0.P.sroa_idx.i54, align 32, !alias.scope !44, !noalias !50
  %x.sroa.18.0.copyload.i57 = load <8 x i32>, ptr %x.sroa.18.0.P.sroa_idx.i56, align 32, !alias.scope !44, !noalias !50
  %x.sroa.21.0.copyload.i59 = load <8 x i32>, ptr %x.sroa.21.0.P.sroa_idx.i58, align 32, !alias.scope !44, !noalias !50
  %_3.i219.i.i.i60 = shufflevector <8 x i32> %x.sroa.0.0.copyload.i51, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i74272.i.i.i61 = shufflevector <8 x i32> %x.sroa.12.0.copyload.i53, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i75326.i.i.i62 = shufflevector <8 x i32> %x.sroa.15.0.copyload.i55, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i76380.i.i.i63 = shufflevector <8 x i32> %x.sroa.18.0.copyload.i57, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i77.i.i.i64 = shufflevector <8 x i32> %x.sroa.21.0.copyload.i59, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_6.i.i.i.i65 = sub <8 x i32> <i32 134217690, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %x.sroa.0.0.copyload.i51
  %_6.i10.i.i.i66 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %x.sroa.12.0.copyload.i53
  %_6.i11.i.i.i67 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %x.sroa.15.0.copyload.i55
  %_6.i12.i.i.i68 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %x.sroa.18.0.copyload.i57
  %_6.i13.i.i.i69 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %x.sroa.21.0.copyload.i59
  %r.i192.i.i.i70 = shufflevector <8 x i32> %_6.i.i.i.i65, <8 x i32> %x.sroa.0.0.copyload.i51, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i199.i.i.i71 = shufflevector <8 x i32> %_6.i10.i.i.i66, <8 x i32> %x.sroa.12.0.copyload.i53, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i206.i.i.i72 = shufflevector <8 x i32> %_6.i11.i.i.i67, <8 x i32> %x.sroa.15.0.copyload.i55, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i213.i.i.i73 = shufflevector <8 x i32> %_6.i12.i.i.i68, <8 x i32> %x.sroa.18.0.copyload.i57, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i220.i.i.i74 = shufflevector <8 x i32> %_6.i13.i.i.i69, <8 x i32> %x.sroa.21.0.copyload.i59, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %_6.i.i1.i.i75 = add <8 x i32> %r.i192.i.i.i70, %_3.i219.i.i.i60
  %_6.i10.i2.i.i76 = add <8 x i32> %r.i199.i.i.i71, %_3.i74272.i.i.i61
  %_6.i11.i3.i.i77 = add <8 x i32> %r.i206.i.i.i72, %_3.i75326.i.i.i62
  %_6.i12.i4.i.i78 = add <8 x i32> %r.i213.i.i.i73, %_3.i76380.i.i.i63
  %_6.i13.i5.i.i79 = add <8 x i32> %r.i220.i.i.i74, %_3.i77.i.i.i64
  %r.i191.i.i80 = shufflevector <8 x i32> %_6.i.i1.i.i75, <8 x i32> %x.sroa.0.0.copyload.i51, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i198.i.i81 = shufflevector <8 x i32> %_6.i10.i2.i.i76, <8 x i32> %x.sroa.12.0.copyload.i53, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i205.i.i82 = shufflevector <8 x i32> %_6.i11.i3.i.i77, <8 x i32> %x.sroa.15.0.copyload.i55, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i212.i.i83 = shufflevector <8 x i32> %_6.i12.i4.i.i78, <8 x i32> %x.sroa.18.0.copyload.i57, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i219.i.i84 = shufflevector <8 x i32> %_6.i13.i5.i.i79, <8 x i32> %x.sroa.21.0.copyload.i59, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %_11.i.i.i85 = shufflevector <8 x i32> %r.i191.i.i80, <8 x i32> <i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison>, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %_14.i.i.i86 = shufflevector <8 x i32> %r.i191.i.i80, <8 x i32> <i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0>, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %132 = bitcast <8 x i32> %_11.i.i.i85 to <4 x i64>
  %133 = bitcast <8 x i32> %_14.i.i.i86 to <4 x i64>
  %_11.i25.i.i87 = shufflevector <8 x i32> %r.i198.i.i81, <8 x i32> <i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison>, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %_14.i26.i.i88 = shufflevector <8 x i32> %r.i198.i.i81, <8 x i32> <i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0>, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %134 = bitcast <8 x i32> %_11.i25.i.i87 to <4 x i64>
  %135 = bitcast <8 x i32> %_14.i26.i.i88 to <4 x i64>
  %_11.i27.i.i89 = shufflevector <8 x i32> %r.i205.i.i82, <8 x i32> <i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison>, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %_14.i28.i.i90 = shufflevector <8 x i32> %r.i205.i.i82, <8 x i32> <i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0>, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %136 = bitcast <8 x i32> %_11.i27.i.i89 to <4 x i64>
  %137 = bitcast <8 x i32> %_14.i28.i.i90 to <4 x i64>
  %_11.i29.i.i91 = shufflevector <8 x i32> %r.i212.i.i83, <8 x i32> <i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison>, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %_14.i30.i.i92 = shufflevector <8 x i32> %r.i212.i.i83, <8 x i32> <i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0>, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %138 = bitcast <8 x i32> %_11.i29.i.i91 to <4 x i64>
  %139 = bitcast <8 x i32> %_14.i30.i.i92 to <4 x i64>
  %_11.i31.i.i93 = shufflevector <8 x i32> %r.i219.i.i84, <8 x i32> <i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison>, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %_14.i32.i.i94 = shufflevector <8 x i32> %r.i219.i.i84, <8 x i32> <i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0>, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %140 = bitcast <8 x i32> %_11.i31.i.i93 to <4 x i64>
  %141 = bitcast <8 x i32> %_14.i32.i.i94 to <4 x i64>
  %_9.i.i.i95 = mul nuw nsw <4 x i64> %132, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i36.i.i96 = mul nuw nsw <4 x i64> %133, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i39.i.i97 = mul nuw nsw <4 x i64> %134, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i42.i.i98 = mul nuw nsw <4 x i64> %135, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i45.i.i99 = mul nuw nsw <4 x i64> %136, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i48.i.i100 = mul nuw nsw <4 x i64> %137, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i51.i.i101 = mul nuw nsw <4 x i64> %138, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i54.i.i102 = mul nuw nsw <4 x i64> %139, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i57.i.i103 = mul nuw nsw <4 x i64> %140, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_9.i60.i.i104 = mul nuw nsw <4 x i64> %141, <i64 121666, i64 121666, i64 243332, i64 243330>
  %_5.i13.i.i.i.i105 = lshr <4 x i64> %_9.i.i.i95, splat (i64 26)
  %_6.i.i15.i.i.i.i106 = add nuw nsw <4 x i64> %_5.i13.i.i.i.i105, %_9.i36.i.i96
  %_6.i.i17.i.i.i.i107 = and <4 x i64> %_9.i.i.i95, splat (i64 67108862)
  %_5.i13.i45.i.i.i108 = lshr <4 x i64> %_9.i45.i.i99, splat (i64 26)
  %_6.i.i15.i46.i.i.i109 = add nuw nsw <4 x i64> %_5.i13.i45.i.i.i108, %_9.i48.i.i100
  %_6.i.i17.i48.i.i.i110 = and <4 x i64> %_9.i45.i.i99, splat (i64 67108862)
  %_5.i13.i52.i.i.i111 = lshr <4 x i64> %_6.i.i15.i.i.i.i106, splat (i64 25)
  %_6.i.i15.i53.i.i.i112 = add nuw nsw <4 x i64> %_5.i13.i52.i.i.i111, %_9.i39.i.i97
  %_6.i.i17.i55.i.i.i113 = and <4 x i64> %_6.i.i15.i.i.i.i106, splat (i64 33554431)
  %_5.i13.i59.i.i.i114 = lshr <4 x i64> %_6.i.i15.i46.i.i.i109, splat (i64 25)
  %_6.i.i15.i60.i.i.i115 = add nuw nsw <4 x i64> %_5.i13.i59.i.i.i114, %_9.i51.i.i101
  %_6.i.i17.i62.i.i.i116 = and <4 x i64> %_6.i.i15.i46.i.i.i109, splat (i64 33554431)
  %_5.i13.i66.i.i.i117 = lshr <4 x i64> %_6.i.i15.i53.i.i.i112, splat (i64 26)
  %_6.i.i15.i67.i.i.i118 = add nuw nsw <4 x i64> %_5.i13.i66.i.i.i117, %_9.i42.i.i98
  %_5.i13.i73.i.i.i119 = lshr <4 x i64> %_6.i.i15.i60.i.i.i115, splat (i64 26)
  %_6.i.i15.i74.i.i.i120 = add nuw nsw <4 x i64> %_5.i13.i73.i.i.i119, %_9.i54.i.i102
  %_5.i13.i80.i.i.i121 = lshr <4 x i64> %_6.i.i15.i67.i.i.i118, splat (i64 25)
  %_6.i.i15.i81.i.i.i122 = add nuw nsw <4 x i64> %_5.i13.i80.i.i.i121, %_6.i.i17.i48.i.i.i110
  %_5.i13.i87.i.i.i123 = lshr <4 x i64> %_6.i.i15.i74.i.i.i120, splat (i64 25)
  %_6.i.i15.i88.i.i.i124 = add nuw nsw <4 x i64> %_5.i13.i87.i.i.i123, %_9.i57.i.i103
  %_5.i13.i94.i.i.i125 = lshr <4 x i64> %_6.i.i15.i81.i.i.i122, splat (i64 26)
  %_6.i.i15.i95.i.i.i126 = add nuw nsw <4 x i64> %_5.i13.i94.i.i.i125, %_6.i.i17.i62.i.i.i116
  %_5.i13.i101.i.i.i127 = lshr <4 x i64> %_6.i.i15.i88.i.i.i124, splat (i64 26)
  %_6.i.i15.i102.i.i.i128 = add nuw nsw <4 x i64> %_5.i13.i101.i.i.i127, %_9.i60.i.i104
  %_5.i.i.i.i129 = lshr <4 x i64> %_6.i.i15.i102.i.i.i128, splat (i64 25)
  %_9.i.i.i.i130 = mul nuw nsw <4 x i64> %_5.i.i.i.i129, splat (i64 19)
  %_6.i.i115.i.i.i131 = add nuw nsw <4 x i64> %_9.i.i.i.i130, %_6.i.i17.i.i.i.i107
  %_5.i13.i121.i.i.i132 = lshr <4 x i64> %_6.i.i115.i.i.i131, splat (i64 26)
  %_6.i.i15.i122.i.i.i133 = add nuw nsw <4 x i64> %_5.i13.i121.i.i.i132, %_6.i.i17.i55.i.i.i113
  %142 = bitcast <4 x i64> %_6.i.i115.i.i.i131 to <8 x i32>
  %143 = and <8 x i32> %142, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %144 = bitcast <4 x i64> %_6.i.i15.i122.i.i.i133 to <8 x i32>
  %_16.i.i.i.i136 = shufflevector <8 x i32> %143, <8 x i32> %144, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  %145 = bitcast <4 x i64> %_6.i.i15.i53.i.i.i112 to <8 x i32>
  %146 = and <8 x i32> %145, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %147 = bitcast <4 x i64> %_6.i.i15.i67.i.i.i118 to <8 x i32>
  %148 = and <8 x i32> %147, <i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison>
  %_16.i128.i.i.i139 = shufflevector <8 x i32> %146, <8 x i32> %148, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  %149 = bitcast <4 x i64> %_6.i.i15.i95.i.i.i126 to <8 x i32>
  %150 = bitcast <4 x i64> %_6.i.i15.i81.i.i.i122 to <8 x i32>
  %151 = and <8 x i32> %150, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %_16.i131.i.i.i142 = shufflevector <8 x i32> %151, <8 x i32> %149, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  %152 = bitcast <4 x i64> %_6.i.i15.i60.i.i.i115 to <8 x i32>
  %153 = and <8 x i32> %152, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %154 = bitcast <4 x i64> %_6.i.i15.i74.i.i.i120 to <8 x i32>
  %155 = and <8 x i32> %154, <i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison>
  %_16.i134.i.i.i145 = shufflevector <8 x i32> %153, <8 x i32> %155, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  %156 = bitcast <4 x i64> %_6.i.i15.i88.i.i.i124 to <8 x i32>
  %157 = and <8 x i32> %156, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %158 = bitcast <4 x i64> %_6.i.i15.i102.i.i.i128 to <8 x i32>
  %159 = and <8 x i32> %158, <i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison>
  %_16.i137.i.i.i148 = shufflevector <8 x i32> %157, <8 x i32> %159, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  %_6.i.i.i149 = sub <8 x i32> <i32 1073741520, i32 1073741520, i32 536870896, i32 536870896, i32 1073741520, i32 1073741520, i32 536870896, i32 536870896>, %_16.i.i.i.i136
  %_6.i10.i.i150 = sub nuw nsw <8 x i32> <i32 1073741808, i32 1073741808, i32 536870896, i32 536870896, i32 1073741808, i32 1073741808, i32 536870896, i32 536870896>, %_16.i128.i.i.i139
  %_6.i11.i.i151 = sub nuw nsw <8 x i32> <i32 1073741808, i32 1073741808, i32 536870896, i32 536870896, i32 1073741808, i32 1073741808, i32 536870896, i32 536870896>, %_16.i131.i.i.i142
  %_6.i12.i.i152 = sub nuw nsw <8 x i32> <i32 1073741808, i32 1073741808, i32 536870896, i32 536870896, i32 1073741808, i32 1073741808, i32 536870896, i32 536870896>, %_16.i134.i.i.i145
  %_6.i13.i.i153 = sub nuw nsw <8 x i32> <i32 1073741808, i32 1073741808, i32 536870896, i32 536870896, i32 1073741808, i32 1073741808, i32 536870896, i32 536870896>, %_16.i137.i.i.i148
  %_8.i.i.i.i.i154 = lshr <8 x i32> %_6.i.i.i149, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i.i.i1.i155 = shufflevector <8 x i32> %_8.i.i.i.i.i154, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 5>
  %_9.i40.i.i56.i156 = insertelement <8 x i32> %_9.i.i.i1.i155, i32 0, i64 5
  %160 = and <8 x i32> %_6.i.i.i149, <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 67108863, i32 poison, i32 33554431>
  %_6.i41.i.i.i157 = add nuw nsw <8 x i32> %_9.i40.i.i56.i156, %160
  %_8.i.i43.i.i.i158 = lshr <8 x i32> %_6.i10.i.i150, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i47.i.i.i160 = shufflevector <8 x i32> %_8.i.i.i.i.i154, <8 x i32> %_8.i.i43.i.i.i158, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 7, i32 poison, i32 13>
  %161 = and <8 x i32> %_6.i10.i.i150, <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 67108863, i32 poison, i32 33554431>
  %_6.i48.i.i.i161 = add nuw nsw <8 x i32> %_9.i47.i.i.i160, %161
  %_8.i.i50.i.i.i162 = lshr <8 x i32> %_6.i11.i.i151, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i54.i.i.i164 = shufflevector <8 x i32> %_8.i.i43.i.i.i158, <8 x i32> %_8.i.i50.i.i.i162, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 7, i32 poison, i32 13>
  %162 = and <8 x i32> %_6.i11.i.i151, <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 67108863, i32 poison, i32 33554431>
  %_6.i55.i.i.i165 = add nuw nsw <8 x i32> %_9.i54.i.i.i164, %162
  %_8.i.i57.i.i.i166 = lshr <8 x i32> %_6.i12.i.i152, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i61.i.i.i168 = shufflevector <8 x i32> %_8.i.i50.i.i.i162, <8 x i32> %_8.i.i57.i.i.i166, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 7, i32 poison, i32 13>
  %163 = and <8 x i32> %_6.i12.i.i152, <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 67108863, i32 poison, i32 33554431>
  %_6.i62.i.i.i169 = add nuw nsw <8 x i32> %_9.i61.i.i.i168, %163
  %_8.i.i64.i.i.i170 = lshr <8 x i32> %_6.i13.i.i153, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i68.i.i.i172 = shufflevector <8 x i32> %_8.i.i57.i.i.i166, <8 x i32> %_8.i.i64.i.i.i170, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 7, i32 poison, i32 13>
  %164 = and <8 x i32> %_6.i13.i.i153, <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 67108863, i32 poison, i32 33554431>
  %_6.i69.i.i.i173 = add nuw nsw <8 x i32> %_9.i68.i.i.i172, %164
  %165 = and <8 x i32> %_8.i.i64.i.i.i170, <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 0, i32 poison, i32 15>
  %_76.i.i.i175.inner = shufflevector <8 x i32> %165, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 7, i32 5>
  %_76.i.i.i175 = bitcast <8 x i32> %_76.i.i.i175.inner to <4 x i64>
  %_75.i.i.i176 = mul nuw nsw <4 x i64> %_76.i.i.i175, <i64 poison, i64 poison, i64 poison, i64 19>
  %166 = bitcast <4 x i64> %_75.i.i.i176 to <8 x i32>
  %_78.i.i.i177 = shufflevector <8 x i32> %166, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 6, i32 poison, i32 7>
  %_6.i.i.i.i.i178 = add nuw nsw <8 x i32> %_6.i41.i.i.i157, %_78.i.i.i177
  %r.i190.i.i179 = shufflevector <8 x i32> %_16.i.i.i.i136, <8 x i32> %_6.i.i.i.i.i178, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i197.i.i180 = shufflevector <8 x i32> %_16.i128.i.i.i139, <8 x i32> %_6.i48.i.i.i161, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i204.i.i181 = shufflevector <8 x i32> %_16.i131.i.i.i142, <8 x i32> %_6.i55.i.i.i165, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i211.i.i182 = shufflevector <8 x i32> %_16.i134.i.i.i145, <8 x i32> %_6.i62.i.i.i169, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i218.i.i183 = shufflevector <8 x i32> %_16.i137.i.i.i148, <8 x i32> %_6.i69.i.i.i173, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  call void @llvm.lifetime.end.p0(ptr nonnull %_15)
  %167 = getelementptr inbounds nuw i8, ptr %_17, i64 160
  store <8 x i32> %r.i190.i.i179, ptr %167, align 32
  %_14.sroa.4.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_17, i64 192
  store <8 x i32> %r.i197.i.i180, ptr %_14.sroa.4.0..sroa_idx, align 32
  %_14.sroa.5.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_17, i64 224
  store <8 x i32> %r.i204.i.i181, ptr %_14.sroa.5.0..sroa_idx, align 32
  %_14.sroa.6.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_17, i64 256
  store <8 x i32> %r.i211.i.i182, ptr %_14.sroa.6.0..sroa_idx, align 32
  %_14.sroa.7.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_17, i64 288
  store <8 x i32> %r.i218.i.i183, ptr %_14.sroa.7.0..sroa_idx, align 32
  %exitcond.not = icmp eq i64 %_0.i1.i.i, 7
  br i1 %exitcond.not, label %bb9, label %bb13
}

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #3

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #4

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #3

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }
attributes #1 = { inlinehint mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }
attributes #2 = { nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }
attributes #3 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #4 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #5 = { nounwind }
attributes #6 = { inlinehint nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{!5, !7}
!5 = distinct !{!5, !6, !"_RNvXNvMs7_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsNtB8_13ExtendedPoint6doubleB1c_NtB2_15___Impl_double__12__impl_double: %_0"}
!6 = distinct !{!6, !"_RNvXNvMs7_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsNtB8_13ExtendedPoint6doubleB1c_NtB2_15___Impl_double__12__impl_double"}
!7 = distinct !{!7, !6, !"_RNvXNvMs7_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsNtB8_13ExtendedPoint6doubleB1c_NtB2_15___Impl_double__12__impl_double: %self"}
!8 = !{!9}
!9 = distinct !{!9, !10, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!10 = distinct !{!10, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!11 = !{!12, !5, !7}
!12 = distinct !{!12, !10, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!13 = !{!7}
!14 = !{!15, !17, !18}
!15 = distinct !{!15, !16, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add: %_0"}
!16 = distinct !{!16, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add"}
!17 = distinct !{!17, !16, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add: %self"}
!18 = distinct !{!18, !16, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add: %other"}
!19 = !{!15, !18}
!20 = !{!21, !23}
!21 = distinct !{!21, !22, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!22 = distinct !{!22, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!23 = distinct !{!23, !24, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x48diff_sumB1a_NtB2_17___Impl_diff_sum__14__impl_diff_sum: %self"}
!24 = distinct !{!24, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x48diff_sumB1a_NtB2_17___Impl_diff_sum__14__impl_diff_sum"}
!25 = !{!26, !27, !15, !17, !18}
!26 = distinct !{!26, !22, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!27 = distinct !{!27, !24, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x48diff_sumB1a_NtB2_17___Impl_diff_sum__14__impl_diff_sum: %_0"}
!28 = !{!29}
!29 = distinct !{!29, !30, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!30 = distinct !{!30, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!31 = !{!32, !15, !17, !18}
!32 = distinct !{!32, !30, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!33 = !{!34}
!34 = distinct !{!34, !35, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!35 = distinct !{!35, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!36 = !{!37, !15, !17, !18}
!37 = distinct !{!37, !35, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!38 = !{!39}
!39 = distinct !{!39, !40, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!40 = distinct !{!40, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!41 = !{!42, !15, !17, !18}
!42 = distinct !{!42, !40, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!43 = !{!17, !18}
!44 = !{!45, !47, !49}
!45 = distinct !{!45, !46, !"_RNvXNvXsc_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsNtB8_11CachedPointINtNtCsgxBkk5gSRhY_4core7convert4FromNtB8_13ExtendedPointE4fromB1c_NtB2_13___Impl_from__10__impl_from: %P"}
!46 = distinct !{!46, !"_RNvXNvXsc_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsNtB8_11CachedPointINtNtCsgxBkk5gSRhY_4core7convert4FromNtB8_13ExtendedPointE4fromB1c_NtB2_13___Impl_from__10__impl_from"}
!47 = distinct !{!47, !48, !"_RNvXs1_NtCsgxBkk5gSRhY_4core7convertNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwards13ExtendedPointINtB5_4IntoNtBA_11CachedPointE4intoBI_: %_0"}
!48 = distinct !{!48, !"_RNvXs1_NtCsgxBkk5gSRhY_4core7convertNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwards13ExtendedPointINtB5_4IntoNtBA_11CachedPointE4intoBI_"}
!49 = distinct !{!49, !48, !"_RNvXs1_NtCsgxBkk5gSRhY_4core7convertNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwards13ExtendedPointINtB5_4IntoNtBA_11CachedPointE4intoBI_: %self"}
!50 = !{!51}
!51 = distinct !{!51, !46, !"_RNvXNvXsc_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsNtB8_11CachedPointINtNtCsgxBkk5gSRhY_4core7convert4FromNtB8_13ExtendedPointE4fromB1c_NtB2_13___Impl_from__10__impl_from: %_0"}
