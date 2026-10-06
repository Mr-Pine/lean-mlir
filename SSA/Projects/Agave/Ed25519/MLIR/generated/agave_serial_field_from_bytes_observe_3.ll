; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_serial_field_from_bytes_observe_3.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable
define noundef range(i64 0, 2251799813685248) i64 @agave_serial_field_from_bytes_observe_3(i64 noundef %w0, i64 noundef %w1, i64 noundef %w2, i64 noundef %w3) unnamed_addr #0 {
start:
  %bytes.sroa.5 = alloca [16 x i8], align 8
  call void @llvm.lifetime.start.p0(ptr nonnull %bytes.sroa.5)
  store i64 %w2, ptr %bytes.sroa.5, align 8, !alias.scope !4, !noalias !8
  %bytes.sroa.5.8.bytes.24._50.sroa_idx2 = getelementptr inbounds nuw i8, ptr %bytes.sroa.5, i64 8
  store i64 %w3, ptr %bytes.sroa.5.8.bytes.24._50.sroa_idx2, align 8, !alias.scope !10, !noalias !14
  %bytes.sroa.5.3.bytes.19.bytes.19.bytes.19.bytes.19.bytes.19..sroa_idx1 = getelementptr inbounds nuw i8, ptr %bytes.sroa.5, i64 3
  %bytes.sroa.5.3.bytes.sroa.5.3.bytes.sroa.5.19.bytes.19.bytes.19.bytes.19.bytes.19.bytes.19._10.i3.i = load i64, ptr %bytes.sroa.5.3.bytes.19.bytes.19.bytes.19.bytes.19.bytes.19..sroa_idx1, align 1, !alias.scope !16, !noalias !21
  %_13.i = lshr i64 %bytes.sroa.5.3.bytes.sroa.5.3.bytes.sroa.5.19.bytes.19.bytes.19.bytes.19.bytes.19.bytes.19._10.i3.i, 1
  %_12.i = and i64 %_13.i, 2251799813685247
  call void @llvm.lifetime.end.p0(ptr nonnull %bytes.sroa.5)
  ret i64 %_12.i
}

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #1

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #1

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{!5, !7}
!5 = distinct !{!5, !6, !"_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519: %dest.0"}
!6 = distinct !{!6, !"_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519"}
!7 = distinct !{!7, !6, !"_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519: %src.0"}
!8 = !{!9}
!9 = distinct !{!9, !6, !"_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519: argument 2"}
!10 = !{!11, !13}
!11 = distinct !{!11, !12, !"_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519: %dest.0"}
!12 = distinct !{!12, !"_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519"}
!13 = distinct !{!13, !12, !"_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519: %src.0"}
!14 = !{!15}
!15 = distinct !{!15, !12, !"_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519: argument 2"}
!16 = !{!17, !19}
!17 = distinct !{!17, !18, !"_RNvNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB7_14FieldElement5110from_bytes8load8_at: %input.0"}
!18 = distinct !{!18, !"_RNvNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB7_14FieldElement5110from_bytes8load8_at"}
!19 = distinct !{!19, !20, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement5110from_bytes: %bytes"}
!20 = distinct !{!20, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement5110from_bytes"}
!21 = !{!22}
!22 = distinct !{!22, !20, !"_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement5110from_bytes: %_0"}
