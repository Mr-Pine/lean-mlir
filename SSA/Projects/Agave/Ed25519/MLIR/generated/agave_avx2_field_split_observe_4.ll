; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_avx2_field_split_observe_4.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable
define noundef range(i64 0, 288230380379570176) i64 @agave_avx2_field_split_observe_4(<4 x i64> %v0, <4 x i64> %v1, <4 x i64> %v2, <4 x i64> %v3, <4 x i64> %v4) unnamed_addr #0 {
start:
  %0 = bitcast <4 x i64> %v4 to <8 x i32>
  %_8.sroa.31.128.vec.extract = extractelement <8 x i32> %0, i64 0
  %a_2i.4.i = zext i32 %_8.sroa.31.128.vec.extract to i64
  %_8.sroa.31.136.vec.extract = extractelement <8 x i32> %0, i64 2
  %a_2i_1.4.i = zext i32 %_8.sroa.31.136.vec.extract to i64
  %_26.4.i = shl nuw nsw i64 %a_2i_1.4.i, 26
  %1 = add nuw nsw i64 %_26.4.i, %a_2i.4.i
  ret i64 %1
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
