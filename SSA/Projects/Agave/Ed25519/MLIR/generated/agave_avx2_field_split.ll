; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_avx2_field_split.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
define void @_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x45splitB1a_NtB2_14___Impl_split__11__impl_split(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([160 x i8]) align 8 captures(none) dereferenceable(160) initializes((0, 160)) %out, ptr noalias nofree noundef readonly align 32 captures(none) dereferenceable(160) %self) unnamed_addr #0 {
start:
  %_1046 = load <8 x i32>, ptr %self, align 32
  %0 = getelementptr inbounds nuw i8, ptr %self, i64 32
  %.sroa.0.0.vec.extract.i.1 = load i32, ptr %0, align 32
  %1 = getelementptr inbounds nuw i8, ptr %self, i64 36
  %.sroa.0.4.vec.extract.i.1 = load i32, ptr %1, align 4
  %b_2i.1 = zext i32 %.sroa.0.4.vec.extract.i.1 to i64
  %2 = getelementptr inbounds nuw i8, ptr %self, i64 40
  %.sroa.0.8.vec.extract.i.1 = load i32, ptr %2, align 8
  %3 = getelementptr inbounds nuw i8, ptr %self, i64 44
  %.sroa.0.12.vec.extract.i.1 = load i32, ptr %3, align 4
  %b_2i_1.1 = zext i32 %.sroa.0.12.vec.extract.i.1 to i64
  %4 = getelementptr inbounds nuw i8, ptr %self, i64 48
  %.sroa.0.16.vec.extract.i.1 = load i32, ptr %4, align 16
  %5 = getelementptr inbounds nuw i8, ptr %self, i64 52
  %.sroa.0.20.vec.extract.i.1 = load i32, ptr %5, align 4
  %d_2i.1 = zext i32 %.sroa.0.20.vec.extract.i.1 to i64
  %6 = getelementptr inbounds nuw i8, ptr %self, i64 56
  %.sroa.0.24.vec.extract.i.1 = load i32, ptr %6, align 8
  %7 = getelementptr inbounds nuw i8, ptr %self, i64 60
  %.sroa.0.28.vec.extract.i.1 = load i32, ptr %7, align 4
  %d_2i_1.1 = zext i32 %.sroa.0.28.vec.extract.i.1 to i64
  %8 = shufflevector <8 x i32> %_1046, <8 x i32> poison, <2 x i32> <i32 0, i32 1>
  %9 = insertelement <2 x i32> %8, i32 %.sroa.0.0.vec.extract.i.1, i64 1
  %10 = zext <2 x i32> %9 to <2 x i64>
  %11 = shufflevector <8 x i32> %_1046, <8 x i32> poison, <2 x i32> <i32 2, i32 3>
  %12 = insertelement <2 x i32> %11, i32 %.sroa.0.8.vec.extract.i.1, i64 1
  %13 = zext <2 x i32> %12 to <2 x i64>
  %14 = shl nuw nsw <2 x i64> %13, splat (i64 26)
  %15 = add nuw nsw <2 x i64> %14, %10
  store <2 x i64> %15, ptr %out, align 8
  %_27.1 = shl nuw nsw i64 %b_2i_1.1, 26
  %16 = getelementptr inbounds nuw i8, ptr %out, i64 48
  %17 = add nuw nsw i64 %_27.1, %b_2i.1
  store i64 %17, ptr %16, align 8
  %_29.1 = shl nuw nsw i64 %d_2i_1.1, 26
  %18 = getelementptr inbounds nuw i8, ptr %out, i64 128
  %19 = add nuw nsw i64 %_29.1, %d_2i.1
  store i64 %19, ptr %18, align 8
  %20 = getelementptr inbounds nuw i8, ptr %self, i64 64
  %.sroa.0.0.vec.extract.i.2 = load i32, ptr %20, align 32
  %a_2i.2 = zext i32 %.sroa.0.0.vec.extract.i.2 to i64
  %21 = getelementptr inbounds nuw i8, ptr %self, i64 68
  %.sroa.0.4.vec.extract.i.2 = load i32, ptr %21, align 4
  %b_2i.2 = zext i32 %.sroa.0.4.vec.extract.i.2 to i64
  %22 = getelementptr inbounds nuw i8, ptr %self, i64 72
  %.sroa.0.8.vec.extract.i.2 = load i32, ptr %22, align 8
  %a_2i_1.2 = zext i32 %.sroa.0.8.vec.extract.i.2 to i64
  %23 = getelementptr inbounds nuw i8, ptr %self, i64 76
  %.sroa.0.12.vec.extract.i.2 = load i32, ptr %23, align 4
  %b_2i_1.2 = zext i32 %.sroa.0.12.vec.extract.i.2 to i64
  %24 = getelementptr inbounds nuw i8, ptr %self, i64 80
  %.sroa.0.16.vec.extract.i.2 = load i32, ptr %24, align 16
  %25 = getelementptr inbounds nuw i8, ptr %self, i64 84
  %.sroa.0.20.vec.extract.i.2 = load i32, ptr %25, align 4
  %d_2i.2 = zext i32 %.sroa.0.20.vec.extract.i.2 to i64
  %26 = getelementptr inbounds nuw i8, ptr %self, i64 88
  %.sroa.0.24.vec.extract.i.2 = load i32, ptr %26, align 8
  %27 = getelementptr inbounds nuw i8, ptr %self, i64 92
  %.sroa.0.28.vec.extract.i.2 = load i32, ptr %27, align 4
  %d_2i_1.2 = zext i32 %.sroa.0.28.vec.extract.i.2 to i64
  %_26.2 = shl nuw nsw i64 %a_2i_1.2, 26
  %28 = getelementptr inbounds nuw i8, ptr %out, i64 16
  %29 = add nuw nsw i64 %_26.2, %a_2i.2
  store i64 %29, ptr %28, align 8
  %_27.2 = shl nuw nsw i64 %b_2i_1.2, 26
  %30 = getelementptr inbounds nuw i8, ptr %out, i64 56
  %31 = add nuw nsw i64 %_27.2, %b_2i.2
  store i64 %31, ptr %30, align 8
  %32 = getelementptr inbounds nuw i8, ptr %out, i64 96
  %_29.2 = shl nuw nsw i64 %d_2i_1.2, 26
  %33 = getelementptr inbounds nuw i8, ptr %out, i64 136
  %34 = add nuw nsw i64 %_29.2, %d_2i.2
  store i64 %34, ptr %33, align 8
  %35 = getelementptr inbounds nuw i8, ptr %self, i64 96
  %.sroa.0.0.vec.extract.i.3 = load i32, ptr %35, align 32
  %a_2i.3 = zext i32 %.sroa.0.0.vec.extract.i.3 to i64
  %36 = getelementptr inbounds nuw i8, ptr %self, i64 100
  %.sroa.0.4.vec.extract.i.3 = load i32, ptr %36, align 4
  %37 = getelementptr inbounds nuw i8, ptr %self, i64 104
  %.sroa.0.8.vec.extract.i.3 = load i32, ptr %37, align 8
  %a_2i_1.3 = zext i32 %.sroa.0.8.vec.extract.i.3 to i64
  %38 = getelementptr inbounds nuw i8, ptr %self, i64 108
  %.sroa.0.12.vec.extract.i.3 = load i32, ptr %38, align 4
  %39 = getelementptr inbounds nuw i8, ptr %self, i64 112
  %.sroa.0.16.vec.extract.i.3 = load i32, ptr %39, align 16
  %40 = getelementptr inbounds nuw i8, ptr %self, i64 116
  %.sroa.0.20.vec.extract.i.3 = load i32, ptr %40, align 4
  %d_2i.3 = zext i32 %.sroa.0.20.vec.extract.i.3 to i64
  %41 = getelementptr inbounds nuw i8, ptr %self, i64 120
  %.sroa.0.24.vec.extract.i.3 = load i32, ptr %41, align 8
  %42 = getelementptr inbounds nuw i8, ptr %self, i64 124
  %.sroa.0.28.vec.extract.i.3 = load i32, ptr %42, align 4
  %d_2i_1.3 = zext i32 %.sroa.0.28.vec.extract.i.3 to i64
  %_26.3 = shl nuw nsw i64 %a_2i_1.3, 26
  %43 = getelementptr inbounds nuw i8, ptr %out, i64 24
  %44 = add nuw nsw i64 %_26.3, %a_2i.3
  store i64 %44, ptr %43, align 8
  %45 = getelementptr inbounds nuw i8, ptr %out, i64 64
  %_29.3 = shl nuw nsw i64 %d_2i_1.3, 26
  %46 = getelementptr inbounds nuw i8, ptr %out, i64 144
  %47 = add nuw nsw i64 %_29.3, %d_2i.3
  store i64 %47, ptr %46, align 8
  %48 = getelementptr inbounds nuw i8, ptr %self, i64 128
  %.sroa.0.0.vec.extract.i.4 = load i32, ptr %48, align 32
  %49 = getelementptr inbounds nuw i8, ptr %self, i64 132
  %.sroa.0.4.vec.extract.i.4 = load i32, ptr %49, align 4
  %50 = getelementptr inbounds nuw i8, ptr %self, i64 136
  %.sroa.0.8.vec.extract.i.4 = load i32, ptr %50, align 8
  %51 = getelementptr inbounds nuw i8, ptr %self, i64 140
  %.sroa.0.12.vec.extract.i.4 = load i32, ptr %51, align 4
  %52 = getelementptr inbounds nuw i8, ptr %self, i64 144
  %.sroa.0.16.vec.extract.i.4 = load i32, ptr %52, align 16
  %53 = getelementptr inbounds nuw i8, ptr %self, i64 148
  %.sroa.0.20.vec.extract.i.4 = load i32, ptr %53, align 4
  %d_2i.4 = zext i32 %.sroa.0.20.vec.extract.i.4 to i64
  %54 = getelementptr inbounds nuw i8, ptr %self, i64 152
  %.sroa.0.24.vec.extract.i.4 = load i32, ptr %54, align 8
  %55 = getelementptr inbounds nuw i8, ptr %self, i64 156
  %.sroa.0.28.vec.extract.i.4 = load i32, ptr %55, align 4
  %d_2i_1.4 = zext i32 %.sroa.0.28.vec.extract.i.4 to i64
  %56 = getelementptr inbounds nuw i8, ptr %out, i64 32
  %57 = insertelement <2 x i32> %8, i32 %.sroa.0.0.vec.extract.i.4, i64 0
  %58 = zext <2 x i32> %57 to <2 x i64>
  %59 = insertelement <2 x i32> %11, i32 %.sroa.0.8.vec.extract.i.4, i64 0
  %60 = zext <2 x i32> %59 to <2 x i64>
  %61 = shl nuw nsw <2 x i64> %60, splat (i64 26)
  %62 = add nuw nsw <2 x i64> %61, %58
  store <2 x i64> %62, ptr %56, align 8
  %63 = shufflevector <8 x i32> %_1046, <8 x i32> poison, <4 x i32> <i32 poison, i32 poison, i32 4, i32 5>
  %64 = insertelement <4 x i32> %63, i32 %.sroa.0.4.vec.extract.i.3, i64 0
  %65 = insertelement <4 x i32> %64, i32 %.sroa.0.4.vec.extract.i.4, i64 1
  %66 = insertelement <4 x i32> %65, i32 %.sroa.0.16.vec.extract.i.1, i64 3
  %67 = zext <4 x i32> %66 to <4 x i64>
  %68 = shufflevector <8 x i32> %_1046, <8 x i32> poison, <4 x i32> <i32 poison, i32 poison, i32 6, i32 7>
  %69 = insertelement <4 x i32> %68, i32 %.sroa.0.12.vec.extract.i.3, i64 0
  %70 = insertelement <4 x i32> %69, i32 %.sroa.0.12.vec.extract.i.4, i64 1
  %71 = insertelement <4 x i32> %70, i32 %.sroa.0.24.vec.extract.i.1, i64 3
  %72 = zext <4 x i32> %71 to <4 x i64>
  %73 = shl nuw nsw <4 x i64> %72, splat (i64 26)
  %74 = add nuw nsw <4 x i64> %73, %67
  store <4 x i64> %74, ptr %45, align 8
  %75 = insertelement <4 x i32> %63, i32 %.sroa.0.16.vec.extract.i.2, i64 0
  %76 = insertelement <4 x i32> %75, i32 %.sroa.0.16.vec.extract.i.3, i64 1
  %77 = insertelement <4 x i32> %76, i32 %.sroa.0.16.vec.extract.i.4, i64 2
  %78 = zext <4 x i32> %77 to <4 x i64>
  %79 = insertelement <4 x i32> %68, i32 %.sroa.0.24.vec.extract.i.2, i64 0
  %80 = insertelement <4 x i32> %79, i32 %.sroa.0.24.vec.extract.i.3, i64 1
  %81 = insertelement <4 x i32> %80, i32 %.sroa.0.24.vec.extract.i.4, i64 2
  %82 = zext <4 x i32> %81 to <4 x i64>
  %83 = shl nuw nsw <4 x i64> %82, splat (i64 26)
  %84 = add nuw nsw <4 x i64> %83, %78
  store <4 x i64> %84, ptr %32, align 8
  %_29.4 = shl nuw nsw i64 %d_2i_1.4, 26
  %85 = getelementptr inbounds nuw i8, ptr %out, i64 152
  %86 = add nuw nsw i64 %_29.4, %d_2i.4
  store i64 %86, ptr %85, align 8
  ret void
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
