; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_scalar_naf5.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
define void @agave_scalar_naf5(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([256 x i8]) align 1 captures(none) dereferenceable(256) initializes((0, 256)) %_0, ptr noalias nofree noundef readonly captures(none) dereferenceable(32) %a) unnamed_addr #0 personality ptr @rust_eh_personality {
start:
  %x_u64.i = alloca [40 x i8], align 8
  tail call void @llvm.experimental.noalias.scope.decl(metadata !4)
  tail call void @llvm.memset.p0.i64(ptr noundef nonnull align 1 dereferenceable(256) %_0, i8 0, i64 256, i1 false), !alias.scope !4, !noalias !7
  call void @llvm.lifetime.start.p0(ptr nonnull %x_u64.i), !noalias !9
  %0 = getelementptr inbounds nuw i8, ptr %x_u64.i, i64 32
  store i64 0, ptr %0, align 8, !noalias !9
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(32) %x_u64.i, ptr noundef nonnull readonly align 1 dereferenceable(32) %a, i64 32, i1 false), !alias.scope !10, !noalias !4
  br label %bb3.lr.ph.i

bb3.lr.ph.i:                                      ; preds = %bb11.i, %start
  %pos.sroa.0.0.ph17.i = phi i64 [ 0, %start ], [ %10, %bb11.i ]
  %carry.sroa.0.0.ph16.i = phi i64 [ 0, %start ], [ %carry.sroa.0.1.i, %bb11.i ]
  br label %bb3.i

bb3.i:                                            ; preds = %bb10.i, %bb3.lr.ph.i
  %pos.sroa.0.015.i = phi i64 [ %pos.sroa.0.0.ph17.i, %bb3.lr.ph.i ], [ %7, %bb10.i ]
  %u64_idx11.i = lshr i64 %pos.sroa.0.015.i, 6
  %bit_idx.i = and i64 %pos.sroa.0.015.i, 63
  %_20.i = icmp samesign ult i64 %bit_idx.i, 59
  %1 = getelementptr inbounds nuw i64, ptr %x_u64.i, i64 %u64_idx11.i
  %_22.i = load i64, ptr %1, align 8, !noalias !9, !noundef !14
  %2 = lshr i64 %_22.i, %bit_idx.i
  br i1 %_20.i, label %bb9.i, label %bb8.i

bb8.i:                                            ; preds = %bb3.i
  %3 = getelementptr inbounds nuw i8, ptr %1, i64 8
  %_28.i = load i64, ptr %3, align 8, !noalias !9, !noundef !14
  %_31.i = sub nsw i64 0, %pos.sroa.0.015.i
  %4 = and i64 %_31.i, 63
  %_27.i = shl i64 %_28.i, %4
  %5 = or i64 %_27.i, %2
  br label %bb9.i

bb9.i:                                            ; preds = %bb8.i, %bb3.i
  %bit_buf.sroa.0.0.i = phi i64 [ %5, %bb8.i ], [ %2, %bb3.i ]
  %_34.i = and i64 %bit_buf.sroa.0.0.i, 31
  %window.i = add nuw nsw i64 %_34.i, %carry.sroa.0.0.ph16.i
  %_35.i = and i64 %window.i, 1
  %6 = icmp eq i64 %_35.i, 0
  br i1 %6, label %bb10.i, label %bb11.i

bb10.i:                                           ; preds = %bb9.i
  %7 = add nuw nsw i64 %pos.sroa.0.015.i, 1
  %exitcond.not.i = icmp eq i64 %7, 256
  br i1 %exitcond.not.i, label %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit, label %bb3.i

bb11.i:                                           ; preds = %bb9.i
  %_36.i = icmp samesign ugt i64 %window.i, 15
  %8 = trunc nuw nsw i64 %window.i to i8
  %_40.i.neg = select i1 %_36.i, i8 -32, i8 0
  %_40.sink.i = add nsw i8 %_40.i.neg, %8
  %carry.sroa.0.1.i = zext i1 %_36.i to i64
  %9 = getelementptr inbounds nuw i8, ptr %_0, i64 %pos.sroa.0.015.i
  store i8 %_40.sink.i, ptr %9, align 1, !alias.scope !4, !noalias !7
  %10 = add nuw nsw i64 %pos.sroa.0.015.i, 5
  %_1314.i = icmp ult i64 %pos.sroa.0.015.i, 251
  br i1 %_1314.i, label %bb3.lr.ph.i, label %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit

_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit: ; preds = %bb11.i, %bb10.i
  call void @llvm.lifetime.end.p0(ptr nonnull %x_u64.i), !noalias !9
  ret void
}

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #1

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #2

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #1

; Function Attrs: nonlazybind
declare i32 @rust_eh_personality(...) unnamed_addr #3

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr writeonly captures(none), i8, i64, i1 immarg) #4

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite)
declare void @llvm.experimental.noalias.scope.decl(metadata) #5

attributes #0 = { nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #2 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #3 = { nonlazybind "target-cpu"="x86-64" }
attributes #4 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #5 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite) }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{!5}
!5 = distinct !{!5, !6, !"_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form: %naf"}
!6 = distinct !{!6, !"_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form"}
!7 = !{!8}
!8 = distinct !{!8, !6, !"_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form: %self"}
!9 = !{!5, !8}
!10 = !{!11, !13}
!11 = distinct !{!11, !12, !"_RNvNtCsjK63O35OHGN_14solana_ed255196scalar16read_le_u64_into: %dst.0"}
!12 = distinct !{!12, !"_RNvNtCsjK63O35OHGN_14solana_ed255196scalar16read_le_u64_into"}
!13 = distinct !{!13, !12, !"_RNvNtCsjK63O35OHGN_14solana_ed255196scalar16read_le_u64_into: %src.0"}
!14 = !{}
