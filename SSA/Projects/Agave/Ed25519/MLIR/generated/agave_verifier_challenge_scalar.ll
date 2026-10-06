; ModuleID = '/home/nine/Documents/anza-code/.lmf-rir-ed25519/SSA/Projects/Agave/Ed25519/MLIR/generated/agave_verifier_challenge_scalar.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@anon.2688bd6af3b9e90d4f6e608faea972d6.1 = internal unnamed_addr constant [64 x i8] c"\08\C9\BC\F3g\E6\09j;\A7\CA\84\85\AEg\BB+\F8\94\FEr\F3n<\F16\1D_:\F5O\A5\D1\82\E6\AD\7FR\0EQ\1Fl>+\8Ch\05\9Bk\BDA\FB\AB\D9\83\1Fy!~\13\19\CD\E0[", align 16

; Function Attrs: nounwind nonlazybind uwtable
define hidden fastcc void @_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey16challenge_scalar(ptr dead_on_unwind noalias nofree noundef nonnull writable writeonly align 1 captures(none) dereferenceable(32) initializes((0, 32)) %_0, ptr noalias nofree noundef nonnull readonly align 8 captures(none) dereferenceable(192) %self, ptr noalias nofree noundef nonnull readonly captures(none) dereferenceable(64) %signature, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) %msg.0, i64 noundef range(i64 0, -9223372036854775808) %msg.1) unnamed_addr #0 personality ptr @rust_eh_personality {
_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519.exit26:
  %_6.sroa.0 = alloca [127 x i8], align 16
  %_5 = alloca [208 x i8], align 16
  %_4 = alloca [208 x i8], align 16
  call void @llvm.lifetime.start.p0(ptr nonnull %_4)
  call void @llvm.lifetime.start.p0(ptr nonnull %_5)
  call void @llvm.lifetime.start.p0(ptr nonnull %_6.sroa.0)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !4)
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 16 dereferenceable(32) %_6.sroa.0, ptr noundef nonnull align 1 dereferenceable(32) %signature, i64 32, i1 false), !alias.scope !7, !noalias !10
  tail call void @llvm.experimental.noalias.scope.decl(metadata !11)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !14)
  %_6.sroa.0.32.buf_ptr1.i.i.i24.sroa_idx = getelementptr inbounds nuw i8, ptr %_6.sroa.0, i64 32
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 16 dereferenceable(32) %_6.sroa.0.32.buf_ptr1.i.i.i24.sroa_idx, ptr noundef nonnull align 8 dereferenceable(32) %self, i64 32, i1 false), !alias.scope !16, !noalias !24
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 16 dereferenceable(127) %_5, ptr noundef nonnull align 16 dereferenceable(127) %_6.sroa.0, i64 127, i1 false), !alias.scope !26, !noalias !14
  %_6.sroa.5.0._5.sroa_idx = getelementptr inbounds nuw i8, ptr %_5, i64 127
  store i8 64, ptr %_6.sroa.5.0._5.sroa_idx, align 1, !alias.scope !26, !noalias !14
  %_6.sroa.6.0._5.sroa_idx = getelementptr inbounds nuw i8, ptr %_5, i64 128
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 16 dereferenceable(64) %_6.sroa.6.0._5.sroa_idx, ptr noundef nonnull align 16 dereferenceable(64) @anon.2688bd6af3b9e90d4f6e608faea972d6.1, i64 64, i1 false), !alias.scope !26, !noalias !14
  %_6.sroa.7.0._5.sroa_idx = getelementptr inbounds nuw i8, ptr %_5, i64 192
  store i128 0, ptr %_6.sroa.7.0._5.sroa_idx, align 16, !alias.scope !26, !noalias !14
  call void @llvm.lifetime.end.p0(ptr nonnull %_6.sroa.0)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !27)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !30)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !32)
  %core.i.i27 = getelementptr inbounds nuw i8, ptr %_5, i64 128
  tail call void @llvm.experimental.noalias.scope.decl(metadata !35)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !38)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !40)
  %0 = getelementptr inbounds nuw i8, ptr %_5, i64 127
  %self.val.i.i.i28 = load i8, ptr %0, align 1, !alias.scope !42, !noalias !45, !noundef !10
  %_0.i11.i.i.i29 = zext nneg i8 %self.val.i.i.i28 to i64
  %_0.i9.i.i.i30 = icmp sgt i8 %self.val.i.i.i28, -1
  tail call void @llvm.assume(i1 %_0.i9.i.i.i30)
  %rem.i.i.i31 = sub nuw nsw i64 128, %_0.i11.i.i.i29
  %_0.i.i.i.i32 = icmp samesign ult i64 %msg.1, %rem.i.i.i31
  br i1 %_0.i.i.i.i32, label %bb2.i.i.i49, label %bb3.i.i.i33

bb3.i.i.i33:                                      ; preds = %_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519.exit26
  %1 = icmp eq i8 %self.val.i.i.i28, 0
  br i1 %1, label %bb7.i.i.i38, label %_RNvMNtCsgxBkk5gSRhY_4core5sliceSh8split_atCsjK63O35OHGN_14solana_ed25519.exit.i.i.i34

bb2.i.i.i49:                                      ; preds = %_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519.exit26
  %buf_ptr1.i.i.i50 = getelementptr inbounds nuw i8, ptr %_5, i64 %_0.i11.i.i.i29
  call void @llvm.memcpy.p0.p0.i64(ptr nonnull align 1 %buf_ptr1.i.i.i50, ptr nonnull readonly align 1 %msg.0, i64 range(i64 0, -9223372036854775808) %msg.1, i1 false), !alias.scope !46, !noalias !47
  %2 = trunc nuw nsw i64 %msg.1 to i8
  %_7.i.i.i.i51 = add nuw i8 %self.val.i.i.i28, %2
  store i8 %_7.i.i.i.i51, ptr %0, align 1, !alias.scope !48, !noalias !45
  br label %_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519.exit52

bb7.i.i.i38:                                      ; preds = %_RNvMNtCsgxBkk5gSRhY_4core5sliceSh8split_atCsjK63O35OHGN_14solana_ed25519.exit.i.i.i34, %bb3.i.i.i33
  %input.sroa.8.0.i.i.i39 = phi i64 [ %msg.1, %bb3.i.i.i33 ], [ %len.i.i.i.i.i36, %_RNvMNtCsgxBkk5gSRhY_4core5sliceSh8split_atCsjK63O35OHGN_14solana_ed25519.exit.i.i.i34 ]
  %input.sroa.0.0.i.i.i40 = phi ptr [ %msg.0, %bb3.i.i.i33 ], [ %data.i.i.i.i.i35, %_RNvMNtCsgxBkk5gSRhY_4core5sliceSh8split_atCsjK63O35OHGN_14solana_ed25519.exit.i.i.i34 ]
  %chunks_len1.i.i.i.i41 = lshr i64 %input.sroa.8.0.i.i.i39, 7
  %tail_pos.i.i.i.i42 = and i64 %input.sroa.8.0.i.i.i39, 9223372036854775680
  %tail_len.i.i.i.i43 = and i64 %input.sroa.8.0.i.i.i39, 127
  %_14.i.i.i.i44 = getelementptr inbounds nuw i8, ptr %input.sroa.0.0.i.i.i40, i64 %tail_pos.i.i.i.i42
  %3 = icmp eq i64 %chunks_len1.i.i.i.i41, 0
  br i1 %3, label %bb12.i.i.i47, label %bb10.i.i.i45

_RNvMNtCsgxBkk5gSRhY_4core5sliceSh8split_atCsjK63O35OHGN_14solana_ed25519.exit.i.i.i34: ; preds = %bb3.i.i.i33
  %data.i.i.i.i.i35 = getelementptr inbounds nuw i8, ptr %msg.0, i64 %rem.i.i.i31
  %len.i.i.i.i.i36 = sub nuw nsw i64 %msg.1, %rem.i.i.i31
  %buf_ptr.i.i.i37 = getelementptr inbounds nuw i8, ptr %_5, i64 %_0.i11.i.i.i29
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 1 dereferenceable(1) %buf_ptr.i.i.i37, ptr noundef nonnull readonly align 1 dereferenceable(1) %msg.0, i64 %rem.i.i.i31, i1 false), !alias.scope !46, !noalias !47
  %4 = getelementptr inbounds nuw i8, ptr %_5, i64 192
  %5 = load i128, ptr %4, align 16, !alias.scope !51, !noalias !52, !noundef !10
  %6 = add i128 %5, 1
  store i128 %6, ptr %4, align 16, !alias.scope !51, !noalias !52
  call void @_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512(ptr noalias nofree noundef nonnull align 16 dereferenceable(80) %core.i.i27, ptr noalias nofree noundef nonnull readonly align 16 captures(address, read_provenance) dereferenceable(208) %_5, i64 noundef 1) #6, !noalias !55
  br label %bb7.i.i.i38

bb10.i.i.i45:                                     ; preds = %bb7.i.i.i38
  %_4.i.i.i.i46 = zext nneg i64 %chunks_len1.i.i.i.i41 to i128
  %7 = getelementptr inbounds nuw i8, ptr %_5, i64 192
  %8 = load i128, ptr %7, align 16, !alias.scope !51, !noalias !56, !noundef !10
  %9 = add i128 %8, %_4.i.i.i.i46
  store i128 %9, ptr %7, align 16, !alias.scope !51, !noalias !56
  call void @_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512(ptr noalias nofree noundef nonnull align 16 dereferenceable(80) %core.i.i27, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) %input.sroa.0.0.i.i.i40, i64 noundef range(i64 1, 72057594037927936) %chunks_len1.i.i.i.i41) #6, !noalias !27
  br label %bb12.i.i.i47

bb12.i.i.i47:                                     ; preds = %bb10.i.i.i45, %bb7.i.i.i38
  %_7.i13.i.i.i48 = trunc nuw nsw i64 %tail_len.i.i.i.i43 to i8
  store i8 %_7.i13.i.i.i48, ptr %0, align 1, !alias.scope !59, !noalias !45
  call void @llvm.memcpy.p0.p0.i64(ptr nonnull align 16 dereferenceable(208) %_5, ptr nonnull align 1 %_14.i.i.i.i44, i64 %tail_len.i.i.i.i43, i1 false), !alias.scope !46, !noalias !47
  br label %_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519.exit52

_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519.exit52: ; preds = %bb12.i.i.i47, %bb2.i.i.i49
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 16 dereferenceable(208) %_4, ptr noundef nonnull align 16 dereferenceable(208) %_5, i64 208, i1 false), !alias.scope !62, !noalias !30
  call void @llvm.lifetime.end.p0(ptr nonnull %_5)
  call void @_RNvNtCsjK63O35OHGN_14solana_ed255197ed_sigs18scalar_from_sha512(ptr noalias nofree noundef nonnull sret([32 x i8]) align 1 captures(address) dereferenceable(32) %_0, ptr noalias nofree noundef nonnull readonly align 16 captures(none) dereferenceable(208) %_4) #6
  call void @llvm.lifetime.end.p0(ptr nonnull %_4)
  ret void
}

; Function Attrs: nounwind nonlazybind uwtable
declare void @_RNvNtCsjK63O35OHGN_14solana_ed255197ed_sigs18scalar_from_sha512(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([32 x i8]) align 1 captures(none) dereferenceable(32) initializes((0, 32)), ptr dead_on_return noalias nofree noundef readonly align 16 captures(none) dereferenceable(208)) unnamed_addr #0

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #1

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #2

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #1

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: write)
declare void @llvm.assume(i1 noundef) #3

; Function Attrs: nonlazybind
declare i32 @rust_eh_personality(...) unnamed_addr #4

; Function Attrs: nounwind nonlazybind uwtable
declare void @_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512(ptr noalias nofree noundef align 8 dereferenceable(64), ptr noalias nofree noundef nonnull readonly captures(address, read_provenance), i64 noundef range(i64 0, 72057594037927936)) unnamed_addr #0

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite)
declare void @llvm.experimental.noalias.scope.decl(metadata) #5

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #2 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #3 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: write) }
attributes #4 = { nonlazybind "target-cpu"="x86-64" }
attributes #5 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite) }
attributes #6 = { nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{!5}
!5 = distinct !{!5, !6, !"_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519: argument 2"}
!6 = distinct !{!6, !"_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519"}
!7 = !{!8, !5, !9}
!8 = distinct !{!8, !6, !"_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519: %self"}
!9 = distinct !{!9, !6, !"_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519: %_0"}
!10 = !{}
!11 = !{!12}
!12 = distinct !{!12, !13, !"_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519: %_0"}
!13 = distinct !{!13, !"_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519"}
!14 = !{!15}
!15 = distinct !{!15, !13, !"_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519: argument 2"}
!16 = !{!17, !19, !20, !22, !23, !15}
!17 = distinct !{!17, !18, !"_RINvMs5_Cs9ruV6Mq2l7p_12block_bufferINtB6_11BlockBufferINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIBS_IBS_IBS_IBS_IBS_IBS_IBS_NtBU_5UTermNtNtBW_3bit2B1ENtB27_2B0EB2k_EB2k_EB2k_EB2k_EB2k_EB2k_ENtB6_5EagerE13digest_blocksNCNvXss_Cs7dqAOVfn11v_4sha2NtB3x_6Sha512NtCsbCMGC99J5wG_6digest6Update6update0ECsjK63O35OHGN_14solana_ed25519: %self"}
!18 = distinct !{!18, !"_RINvMs5_Cs9ruV6Mq2l7p_12block_bufferINtB6_11BlockBufferINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIBS_IBS_IBS_IBS_IBS_IBS_IBS_NtBU_5UTermNtNtBW_3bit2B1ENtB27_2B0EB2k_EB2k_EB2k_EB2k_EB2k_EB2k_ENtB6_5EagerE13digest_blocksNCNvXss_Cs7dqAOVfn11v_4sha2NtB3x_6Sha512NtCsbCMGC99J5wG_6digest6Update6update0ECsjK63O35OHGN_14solana_ed25519"}
!19 = distinct !{!19, !18, !"_RINvMs5_Cs9ruV6Mq2l7p_12block_bufferINtB6_11BlockBufferINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIBS_IBS_IBS_IBS_IBS_IBS_IBS_NtBU_5UTermNtNtBW_3bit2B1ENtB27_2B0EB2k_EB2k_EB2k_EB2k_EB2k_EB2k_ENtB6_5EagerE13digest_blocksNCNvXss_Cs7dqAOVfn11v_4sha2NtB3x_6Sha512NtCsbCMGC99J5wG_6digest6Update6update0ECsjK63O35OHGN_14solana_ed25519: argument 1"}
!20 = distinct !{!20, !21, !"_RNvXss_Cs7dqAOVfn11v_4sha2NtB5_6Sha512NtCsbCMGC99J5wG_6digest6Update6update: %self"}
!21 = distinct !{!21, !"_RNvXss_Cs7dqAOVfn11v_4sha2NtB5_6Sha512NtCsbCMGC99J5wG_6digest6Update6update"}
!22 = distinct !{!22, !21, !"_RNvXss_Cs7dqAOVfn11v_4sha2NtB5_6Sha512NtCsbCMGC99J5wG_6digest6Update6update: %data.0"}
!23 = distinct !{!23, !13, !"_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519: %self"}
!24 = !{!25, !12}
!25 = distinct !{!25, !18, !"_RINvMs5_Cs9ruV6Mq2l7p_12block_bufferINtB6_11BlockBufferINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIBS_IBS_IBS_IBS_IBS_IBS_IBS_NtBU_5UTermNtNtBW_3bit2B1ENtB27_2B0EB2k_EB2k_EB2k_EB2k_EB2k_EB2k_ENtB6_5EagerE13digest_blocksNCNvXss_Cs7dqAOVfn11v_4sha2NtB3x_6Sha512NtCsbCMGC99J5wG_6digest6Update6update0ECsjK63O35OHGN_14solana_ed25519: argument 2"}
!26 = !{!12, !23}
!27 = !{!28}
!28 = distinct !{!28, !29, !"_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519: %_0"}
!29 = distinct !{!29, !"_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519"}
!30 = !{!31}
!31 = distinct !{!31, !29, !"_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519: argument 2"}
!32 = !{!33}
!33 = distinct !{!33, !34, !"_RNvXss_Cs7dqAOVfn11v_4sha2NtB5_6Sha512NtCsbCMGC99J5wG_6digest6Update6update: %data.0"}
!34 = distinct !{!34, !"_RNvXss_Cs7dqAOVfn11v_4sha2NtB5_6Sha512NtCsbCMGC99J5wG_6digest6Update6update"}
!35 = !{!36}
!36 = distinct !{!36, !37, !"_RINvMs5_Cs9ruV6Mq2l7p_12block_bufferINtB6_11BlockBufferINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIBS_IBS_IBS_IBS_IBS_IBS_IBS_NtBU_5UTermNtNtBW_3bit2B1ENtB27_2B0EB2k_EB2k_EB2k_EB2k_EB2k_EB2k_ENtB6_5EagerE13digest_blocksNCNvXss_Cs7dqAOVfn11v_4sha2NtB3x_6Sha512NtCsbCMGC99J5wG_6digest6Update6update0ECsjK63O35OHGN_14solana_ed25519: %self"}
!37 = distinct !{!37, !"_RINvMs5_Cs9ruV6Mq2l7p_12block_bufferINtB6_11BlockBufferINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIBS_IBS_IBS_IBS_IBS_IBS_IBS_NtBU_5UTermNtNtBW_3bit2B1ENtB27_2B0EB2k_EB2k_EB2k_EB2k_EB2k_EB2k_ENtB6_5EagerE13digest_blocksNCNvXss_Cs7dqAOVfn11v_4sha2NtB3x_6Sha512NtCsbCMGC99J5wG_6digest6Update6update0ECsjK63O35OHGN_14solana_ed25519"}
!38 = !{!39}
!39 = distinct !{!39, !37, !"_RINvMs5_Cs9ruV6Mq2l7p_12block_bufferINtB6_11BlockBufferINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIBS_IBS_IBS_IBS_IBS_IBS_IBS_NtBU_5UTermNtNtBW_3bit2B1ENtB27_2B0EB2k_EB2k_EB2k_EB2k_EB2k_EB2k_ENtB6_5EagerE13digest_blocksNCNvXss_Cs7dqAOVfn11v_4sha2NtB3x_6Sha512NtCsbCMGC99J5wG_6digest6Update6update0ECsjK63O35OHGN_14solana_ed25519: argument 1"}
!40 = !{!41}
!41 = distinct !{!41, !37, !"_RINvMs5_Cs9ruV6Mq2l7p_12block_bufferINtB6_11BlockBufferINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIBS_IBS_IBS_IBS_IBS_IBS_IBS_NtBU_5UTermNtNtBW_3bit2B1ENtB27_2B0EB2k_EB2k_EB2k_EB2k_EB2k_EB2k_ENtB6_5EagerE13digest_blocksNCNvXss_Cs7dqAOVfn11v_4sha2NtB3x_6Sha512NtCsbCMGC99J5wG_6digest6Update6update0ECsjK63O35OHGN_14solana_ed25519: argument 2"}
!42 = !{!36, !43, !44}
!43 = distinct !{!43, !34, !"_RNvXss_Cs7dqAOVfn11v_4sha2NtB5_6Sha512NtCsbCMGC99J5wG_6digest6Update6update: %self"}
!44 = distinct !{!44, !29, !"_RINvYNtCs7dqAOVfn11v_4sha26Sha512NtCsbCMGC99J5wG_6digest6Update5chainRShECsjK63O35OHGN_14solana_ed25519: %self"}
!45 = !{!39, !41, !33, !28, !31}
!46 = !{!36, !39, !43, !33, !44, !31}
!47 = !{!41, !28}
!48 = !{!49, !36, !43, !44}
!49 = distinct !{!49, !50, !"_RINvXNtCs9ruV6Mq2l7p_12block_buffer6sealedNtB5_5EagerNtB3_6Sealed7set_posINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIB1a_IB1a_IB1a_IB1a_IB1a_IB1a_IB1a_NtB1c_5UTermNtNtB1e_3bit2B1ENtB2x_2B0EB2L_EB2L_EB2L_EB2L_EB2L_EB2L_EECsjK63O35OHGN_14solana_ed25519: %buf"}
!50 = distinct !{!50, !"_RINvXNtCs9ruV6Mq2l7p_12block_buffer6sealedNtB5_5EagerNtB3_6Sealed7set_posINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIB1a_IB1a_IB1a_IB1a_IB1a_IB1a_IB1a_NtB1c_5UTermNtNtB1e_3bit2B1ENtB2x_2B0EB2L_EB2L_EB2L_EB2L_EB2L_EB2L_EECsjK63O35OHGN_14solana_ed25519"}
!51 = !{!41, !43, !44}
!52 = !{!53, !36, !39, !33, !28, !31}
!53 = distinct !{!53, !54, !"_RNCNvXss_Cs7dqAOVfn11v_4sha2NtB7_6Sha512NtCsbCMGC99J5wG_6digest6Update6update0CsjK63O35OHGN_14solana_ed25519: %blocks.0"}
!54 = distinct !{!54, !"_RNCNvXss_Cs7dqAOVfn11v_4sha2NtB7_6Sha512NtCsbCMGC99J5wG_6digest6Update6update0CsjK63O35OHGN_14solana_ed25519"}
!55 = !{!39, !33, !28, !31}
!56 = !{!57, !36, !39, !33, !28, !31}
!57 = distinct !{!57, !58, !"_RNCNvXss_Cs7dqAOVfn11v_4sha2NtB7_6Sha512NtCsbCMGC99J5wG_6digest6Update6update0CsjK63O35OHGN_14solana_ed25519: %blocks.0"}
!58 = distinct !{!58, !"_RNCNvXss_Cs7dqAOVfn11v_4sha2NtB7_6Sha512NtCsbCMGC99J5wG_6digest6Update6update0CsjK63O35OHGN_14solana_ed25519"}
!59 = !{!60, !36, !43, !44}
!60 = distinct !{!60, !61, !"_RINvXNtCs9ruV6Mq2l7p_12block_buffer6sealedNtB5_5EagerNtB3_6Sealed7set_posINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIB1a_IB1a_IB1a_IB1a_IB1a_IB1a_IB1a_NtB1c_5UTermNtNtB1e_3bit2B1ENtB2x_2B0EB2L_EB2L_EB2L_EB2L_EB2L_EB2L_EECsjK63O35OHGN_14solana_ed25519: %buf"}
!61 = distinct !{!61, !"_RINvXNtCs9ruV6Mq2l7p_12block_buffer6sealedNtB5_5EagerNtB3_6Sealed7set_posINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIB1a_IB1a_IB1a_IB1a_IB1a_IB1a_IB1a_NtB1c_5UTermNtNtB1e_3bit2B1ENtB2x_2B0EB2L_EB2L_EB2L_EB2L_EB2L_EB2L_EECsjK63O35OHGN_14solana_ed25519"}
!62 = !{!28, !44}
