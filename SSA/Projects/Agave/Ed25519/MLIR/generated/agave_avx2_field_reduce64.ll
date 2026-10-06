; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_avx2_field_reduce64.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
define void @agave_avx2_field_reduce64(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([160 x i8]) align 32 captures(none) dereferenceable(160) initializes((0, 160)) %_0, ptr dead_on_return noalias nofree noundef readonly align 32 captures(none) dereferenceable(320) %z) unnamed_addr #0 {
start:
  tail call void @llvm.experimental.noalias.scope.decl(metadata !4)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !7)
  %_6.i.i = getelementptr inbounds nuw i8, ptr %z, i64 32
  %_10.i.i = load <4 x i64>, ptr %z, align 32, !alias.scope !9, !noalias !4
  %_4.i.i.i = load <4 x i64>, ptr %_6.i.i, align 32, !alias.scope !9, !noalias !4
  %_5.i13.i.i = lshr <4 x i64> %_10.i.i, splat (i64 26)
  %_6.i.i15.i.i = add <4 x i64> %_4.i.i.i, %_5.i13.i.i
  %_6.i.i17.i.i = and <4 x i64> %_10.i.i, splat (i64 67108863)
  %0 = getelementptr inbounds nuw i8, ptr %z, i64 128
  %_6.i42.i = getelementptr inbounds nuw i8, ptr %z, i64 160
  %_10.i43.i = load <4 x i64>, ptr %0, align 32, !alias.scope !12, !noalias !4
  %_4.i.i44.i = load <4 x i64>, ptr %_6.i42.i, align 32, !alias.scope !12, !noalias !4
  %_5.i13.i45.i = lshr <4 x i64> %_10.i43.i, splat (i64 26)
  %_6.i.i15.i46.i = add <4 x i64> %_4.i.i44.i, %_5.i13.i45.i
  %_6.i.i17.i48.i = and <4 x i64> %_10.i43.i, splat (i64 67108863)
  %_6.i49.i = getelementptr inbounds nuw i8, ptr %z, i64 64
  %_4.i.i51.i = load <4 x i64>, ptr %_6.i49.i, align 32, !alias.scope !15, !noalias !4
  %_5.i13.i52.i = lshr <4 x i64> %_6.i.i15.i.i, splat (i64 25)
  %_6.i.i15.i53.i = add <4 x i64> %_4.i.i51.i, %_5.i13.i52.i
  %_6.i.i17.i55.i = and <4 x i64> %_6.i.i15.i.i, splat (i64 33554431)
  %_6.i56.i = getelementptr inbounds nuw i8, ptr %z, i64 192
  %_4.i.i58.i = load <4 x i64>, ptr %_6.i56.i, align 32, !alias.scope !18, !noalias !4
  %_5.i13.i59.i = lshr <4 x i64> %_6.i.i15.i46.i, splat (i64 25)
  %_6.i.i15.i60.i = add <4 x i64> %_4.i.i58.i, %_5.i13.i59.i
  %_6.i.i17.i62.i = and <4 x i64> %_6.i.i15.i46.i, splat (i64 33554431)
  %_6.i63.i = getelementptr inbounds nuw i8, ptr %z, i64 96
  %_4.i.i65.i = load <4 x i64>, ptr %_6.i63.i, align 32, !alias.scope !21, !noalias !4
  %_5.i13.i66.i = lshr <4 x i64> %_6.i.i15.i53.i, splat (i64 26)
  %_6.i.i15.i67.i = add <4 x i64> %_4.i.i65.i, %_5.i13.i66.i
  %_6.i70.i = getelementptr inbounds nuw i8, ptr %z, i64 224
  %_4.i.i72.i = load <4 x i64>, ptr %_6.i70.i, align 32, !alias.scope !24, !noalias !4
  %_5.i13.i73.i = lshr <4 x i64> %_6.i.i15.i60.i, splat (i64 26)
  %_6.i.i15.i74.i = add <4 x i64> %_4.i.i72.i, %_5.i13.i73.i
  %_5.i13.i80.i = lshr <4 x i64> %_6.i.i15.i67.i, splat (i64 25)
  %_6.i.i15.i81.i = add nuw nsw <4 x i64> %_5.i13.i80.i, %_6.i.i17.i48.i
  %_6.i84.i = getelementptr inbounds nuw i8, ptr %z, i64 256
  %_4.i.i86.i = load <4 x i64>, ptr %_6.i84.i, align 32, !alias.scope !27, !noalias !4
  %_5.i13.i87.i = lshr <4 x i64> %_6.i.i15.i74.i, splat (i64 25)
  %_6.i.i15.i88.i = add <4 x i64> %_5.i13.i87.i, %_4.i.i86.i
  %_5.i13.i94.i = lshr <4 x i64> %_6.i.i15.i81.i, splat (i64 26)
  %_6.i.i15.i95.i = add nuw nsw <4 x i64> %_5.i13.i94.i, %_6.i.i17.i62.i
  %_6.i98.i = getelementptr inbounds nuw i8, ptr %z, i64 288
  %_4.i.i100.i = load <4 x i64>, ptr %_6.i98.i, align 32, !alias.scope !30, !noalias !4
  %_5.i13.i101.i = lshr <4 x i64> %_6.i.i15.i88.i, splat (i64 26)
  %_6.i.i15.i102.i = add <4 x i64> %_5.i13.i101.i, %_4.i.i100.i
  %_5.i.i = lshr <4 x i64> %_6.i.i15.i102.i, splat (i64 25)
  %_6.i105.i = and <4 x i64> %_5.i.i, splat (i64 67108863)
  %_5.i106.i = lshr <4 x i64> %_6.i.i15.i102.i, splat (i64 51)
  %_9.i.i = mul nuw nsw <4 x i64> %_6.i105.i, splat (i64 19)
  %_9.i113.i = mul nuw nsw <4 x i64> %_5.i106.i, splat (i64 19)
  %_6.i.i115.i = add nuw nsw <4 x i64> %_9.i.i, %_6.i.i17.i.i
  %_6.i.i117.i = add nuw nsw <4 x i64> %_9.i113.i, %_6.i.i17.i55.i
  %_5.i13.i121.i = lshr <4 x i64> %_6.i.i115.i, splat (i64 26)
  %_6.i.i15.i122.i = add nuw nsw <4 x i64> %_6.i.i117.i, %_5.i13.i121.i
  %1 = bitcast <4 x i64> %_6.i.i115.i to <8 x i32>
  %2 = and <8 x i32> %1, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %3 = bitcast <4 x i64> %_6.i.i15.i122.i to <8 x i32>
  %_16.i.i = shufflevector <8 x i32> %2, <8 x i32> %3, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  %4 = bitcast <4 x i64> %_6.i.i15.i53.i to <8 x i32>
  %5 = and <8 x i32> %4, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %6 = bitcast <4 x i64> %_6.i.i15.i67.i to <8 x i32>
  %7 = and <8 x i32> %6, <i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison>
  %_16.i128.i = shufflevector <8 x i32> %5, <8 x i32> %7, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  %8 = bitcast <4 x i64> %_6.i.i15.i95.i to <8 x i32>
  %9 = bitcast <4 x i64> %_6.i.i15.i81.i to <8 x i32>
  %10 = and <8 x i32> %9, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %_16.i131.i = shufflevector <8 x i32> %10, <8 x i32> %8, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  %11 = bitcast <4 x i64> %_6.i.i15.i60.i to <8 x i32>
  %12 = and <8 x i32> %11, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %13 = bitcast <4 x i64> %_6.i.i15.i74.i to <8 x i32>
  %14 = and <8 x i32> %13, <i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison>
  %_16.i134.i = shufflevector <8 x i32> %12, <8 x i32> %14, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  %15 = bitcast <4 x i64> %_6.i.i15.i88.i to <8 x i32>
  %16 = and <8 x i32> %15, <i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison, i32 67108863, i32 poison>
  %17 = bitcast <4 x i64> %_6.i.i15.i102.i to <8 x i32>
  %18 = and <8 x i32> %17, <i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison, i32 33554431, i32 poison>
  %_16.i137.i = shufflevector <8 x i32> %16, <8 x i32> %18, <8 x i32> <i32 0, i32 2, i32 8, i32 10, i32 4, i32 6, i32 12, i32 14>
  store <8 x i32> %_16.i.i, ptr %_0, align 32, !alias.scope !4, !noalias !7
  %_66.sroa.4.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %_0, i64 32
  store <8 x i32> %_16.i128.i, ptr %_66.sroa.4.0._0.sroa_idx.i, align 32, !alias.scope !4, !noalias !7
  %_66.sroa.5.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %_0, i64 64
  store <8 x i32> %_16.i131.i, ptr %_66.sroa.5.0._0.sroa_idx.i, align 32, !alias.scope !4, !noalias !7
  %_66.sroa.6.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %_0, i64 96
  store <8 x i32> %_16.i134.i, ptr %_66.sroa.6.0._0.sroa_idx.i, align 32, !alias.scope !4, !noalias !7
  %_66.sroa.7.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %_0, i64 128
  store <8 x i32> %_16.i137.i, ptr %_66.sroa.7.0._0.sroa_idx.i, align 32, !alias.scope !4, !noalias !7
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
!5 = distinct !{!5, !6, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x48reduce64B1a_NtB2_17___Impl_reduce64__14__impl_reduce64: %_0"}
!6 = distinct !{!6, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x48reduce64B1a_NtB2_17___Impl_reduce64__14__impl_reduce64"}
!7 = !{!8}
!8 = distinct !{!8, !6, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x48reduce64B1a_NtB2_17___Impl_reduce64__14__impl_reduce64: %z"}
!9 = !{!10, !8}
!10 = distinct !{!10, !11, !"_RNCNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtBa_18FieldElement2625x48reduce64B1c_NtB4_17___Impl_reduce64__14__impl_reduce640Bi_: %z"}
!11 = distinct !{!11, !"_RNCNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtBa_18FieldElement2625x48reduce64B1c_NtB4_17___Impl_reduce64__14__impl_reduce640Bi_"}
!12 = !{!13, !8}
!13 = distinct !{!13, !14, !"_RNCNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtBa_18FieldElement2625x48reduce64B1c_NtB4_17___Impl_reduce64__14__impl_reduce640Bi_: %z"}
!14 = distinct !{!14, !"_RNCNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtBa_18FieldElement2625x48reduce64B1c_NtB4_17___Impl_reduce64__14__impl_reduce640Bi_"}
!15 = !{!16, !8}
!16 = distinct !{!16, !17, !"_RNCNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtBa_18FieldElement2625x48reduce64B1c_NtB4_17___Impl_reduce64__14__impl_reduce640Bi_: %z"}
!17 = distinct !{!17, !"_RNCNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtBa_18FieldElement2625x48reduce64B1c_NtB4_17___Impl_reduce64__14__impl_reduce640Bi_"}
!18 = !{!19, !8}
!19 = distinct !{!19, !20, !"_RNCNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtBa_18FieldElement2625x48reduce64B1c_NtB4_17___Impl_reduce64__14__impl_reduce640Bi_: %z"}
!20 = distinct !{!20, !"_RNCNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtBa_18FieldElement2625x48reduce64B1c_NtB4_17___Impl_reduce64__14__impl_reduce640Bi_"}
!21 = !{!22, !8}
!22 = distinct !{!22, !23, !"_RNCNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtBa_18FieldElement2625x48reduce64B1c_NtB4_17___Impl_reduce64__14__impl_reduce640Bi_: %z"}
!23 = distinct !{!23, !"_RNCNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtBa_18FieldElement2625x48reduce64B1c_NtB4_17___Impl_reduce64__14__impl_reduce640Bi_"}
!24 = !{!25, !8}
!25 = distinct !{!25, !26, !"_RNCNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtBa_18FieldElement2625x48reduce64B1c_NtB4_17___Impl_reduce64__14__impl_reduce640Bi_: %z"}
!26 = distinct !{!26, !"_RNCNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtBa_18FieldElement2625x48reduce64B1c_NtB4_17___Impl_reduce64__14__impl_reduce640Bi_"}
!27 = !{!28, !8}
!28 = distinct !{!28, !29, !"_RNCNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtBa_18FieldElement2625x48reduce64B1c_NtB4_17___Impl_reduce64__14__impl_reduce640Bi_: %z"}
!29 = distinct !{!29, !"_RNCNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtBa_18FieldElement2625x48reduce64B1c_NtB4_17___Impl_reduce64__14__impl_reduce640Bi_"}
!30 = !{!31, !8}
!31 = distinct !{!31, !32, !"_RNCNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtBa_18FieldElement2625x48reduce64B1c_NtB4_17___Impl_reduce64__14__impl_reduce640Bi_: %z"}
!32 = distinct !{!32, !"_RNCNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtBa_18FieldElement2625x48reduce64B1c_NtB4_17___Impl_reduce64__14__impl_reduce640Bi_"}
