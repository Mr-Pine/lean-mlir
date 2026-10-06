; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_avx2_field_reduce.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
define void @agave_avx2_field_reduce(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([160 x i8]) align 32 captures(none) dereferenceable(160) initializes((0, 160)) %_0, ptr noalias nofree noundef readonly align 32 captures(none) dereferenceable(160) %a) unnamed_addr #0 {
start:
  tail call void @llvm.experimental.noalias.scope.decl(metadata !4)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !7)
  %v.sroa.0.0.copyload206.i = load <8 x i32>, ptr %a, align 32, !alias.scope !7, !noalias !4
  %v.sroa.9.0.self.sroa_idx.i = getelementptr inbounds nuw i8, ptr %a, i64 32
  %v.sroa.9.0.copyload207.i = load <8 x i32>, ptr %v.sroa.9.0.self.sroa_idx.i, align 32, !alias.scope !7, !noalias !4
  %v.sroa.12.0.self.sroa_idx.i = getelementptr inbounds nuw i8, ptr %a, i64 64
  %v.sroa.12.0.copyload208.i = load <8 x i32>, ptr %v.sroa.12.0.self.sroa_idx.i, align 32, !alias.scope !7, !noalias !4
  %v.sroa.15.0.self.sroa_idx.i = getelementptr inbounds nuw i8, ptr %a, i64 96
  %v.sroa.15.0.copyload209.i = load <8 x i32>, ptr %v.sroa.15.0.self.sroa_idx.i, align 32, !alias.scope !7, !noalias !4
  %v.sroa.18.0.self.sroa_idx.i = getelementptr inbounds nuw i8, ptr %a, i64 128
  %v.sroa.18.0.copyload210.i = load <8 x i32>, ptr %v.sroa.18.0.self.sroa_idx.i, align 32, !alias.scope !7, !noalias !4
  %_8.i.i.i = lshr <8 x i32> %v.sroa.0.0.copyload206.i, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i40.i = shufflevector <8 x i32> <i32 0, i32 0, i32 poison, i32 poison, i32 0, i32 0, i32 poison, i32 poison>, <8 x i32> %_8.i.i.i, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %0 = and <8 x i32> %v.sroa.0.0.copyload206.i, <i32 67108863, i32 67108863, i32 33554431, i32 33554431, i32 67108863, i32 67108863, i32 33554431, i32 33554431>
  %_6.i41.i = add nuw nsw <8 x i32> %_9.i40.i, %0
  %_8.i.i43.i = lshr <8 x i32> %v.sroa.9.0.copyload207.i, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i47.i = shufflevector <8 x i32> %_8.i.i.i, <8 x i32> %_8.i.i43.i, <8 x i32> <i32 2, i32 3, i32 8, i32 9, i32 6, i32 7, i32 12, i32 13>
  %1 = and <8 x i32> %v.sroa.9.0.copyload207.i, <i32 67108863, i32 67108863, i32 33554431, i32 33554431, i32 67108863, i32 67108863, i32 33554431, i32 33554431>
  %_6.i48.i = add nuw nsw <8 x i32> %_9.i47.i, %1
  %_8.i.i50.i = lshr <8 x i32> %v.sroa.12.0.copyload208.i, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i54.i = shufflevector <8 x i32> %_8.i.i43.i, <8 x i32> %_8.i.i50.i, <8 x i32> <i32 2, i32 3, i32 8, i32 9, i32 6, i32 7, i32 12, i32 13>
  %2 = and <8 x i32> %v.sroa.12.0.copyload208.i, <i32 67108863, i32 67108863, i32 33554431, i32 33554431, i32 67108863, i32 67108863, i32 33554431, i32 33554431>
  %_6.i55.i = add nuw nsw <8 x i32> %_9.i54.i, %2
  %_8.i.i57.i = lshr <8 x i32> %v.sroa.15.0.copyload209.i, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i61.i = shufflevector <8 x i32> %_8.i.i50.i, <8 x i32> %_8.i.i57.i, <8 x i32> <i32 2, i32 3, i32 8, i32 9, i32 6, i32 7, i32 12, i32 13>
  %3 = and <8 x i32> %v.sroa.15.0.copyload209.i, <i32 67108863, i32 67108863, i32 33554431, i32 33554431, i32 67108863, i32 67108863, i32 33554431, i32 33554431>
  %_6.i62.i = add nuw nsw <8 x i32> %_9.i61.i, %3
  %_8.i.i64.i = lshr <8 x i32> %v.sroa.18.0.copyload210.i, <i32 26, i32 26, i32 25, i32 25, i32 26, i32 26, i32 25, i32 25>
  %_9.i68.i = shufflevector <8 x i32> %_8.i.i57.i, <8 x i32> %_8.i.i64.i, <8 x i32> <i32 2, i32 3, i32 8, i32 9, i32 6, i32 7, i32 12, i32 13>
  %4 = and <8 x i32> %v.sroa.18.0.copyload210.i, <i32 67108863, i32 67108863, i32 33554431, i32 33554431, i32 67108863, i32 67108863, i32 33554431, i32 33554431>
  %_6.i69.i = add nuw nsw <8 x i32> %_9.i68.i, %4
  %5 = and <8 x i32> %_8.i.i64.i, <i32 0, i32 0, i32 127, i32 127, i32 0, i32 0, i32 127, i32 127>
  %_76.i.inner = shufflevector <8 x i32> %5, <8 x i32> poison, <8 x i32> <i32 2, i32 0, i32 3, i32 1, i32 6, i32 4, i32 7, i32 5>
  %_76.i = bitcast <8 x i32> %_76.i.inner to <4 x i64>
  %_75.i = mul nuw nsw <4 x i64> %_76.i, splat (i64 19)
  %6 = bitcast <4 x i64> %_75.i to <8 x i32>
  %_78.i = shufflevector <8 x i32> %6, <8 x i32> poison, <8 x i32> <i32 0, i32 2, i32 1, i32 3, i32 4, i32 6, i32 5, i32 7>
  %_6.i.i.i = add nuw nsw <8 x i32> %_6.i41.i, %_78.i
  store <8 x i32> %_6.i.i.i, ptr %_0, align 32, !alias.scope !4, !noalias !7
  %_68.sroa.4.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %_0, i64 32
  store <8 x i32> %_6.i48.i, ptr %_68.sroa.4.0._0.sroa_idx.i, align 32, !alias.scope !4, !noalias !7
  %_68.sroa.5.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %_0, i64 64
  store <8 x i32> %_6.i55.i, ptr %_68.sroa.5.0._0.sroa_idx.i, align 32, !alias.scope !4, !noalias !7
  %_68.sroa.6.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %_0, i64 96
  store <8 x i32> %_6.i62.i, ptr %_68.sroa.6.0._0.sroa_idx.i, align 32, !alias.scope !4, !noalias !7
  %_68.sroa.7.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %_0, i64 128
  store <8 x i32> %_6.i69.i, ptr %_68.sroa.7.0._0.sroa_idx.i, align 32, !alias.scope !4, !noalias !7
  ret void
}

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite)
declare void @llvm.experimental.noalias.scope.decl(metadata) #1

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }
attributes #1 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite) }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{!5}
!5 = distinct !{!5, !6, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x46reduceB1a_NtB2_15___Impl_reduce__12__impl_reduce: %_0"}
!6 = distinct !{!6, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x46reduceB1a_NtB2_15___Impl_reduce__12__impl_reduce"}
!7 = !{!8}
!8 = distinct !{!8, !6, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x46reduceB1a_NtB2_15___Impl_reduce__12__impl_reduce: %self"}
