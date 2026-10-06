; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_ed25519_verify.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind nonlazybind uwtable
declare noundef range(i8 -1, 3) i8 @_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey12verify_dalek(ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(192), ptr noalias nofree noundef readonly captures(none) dereferenceable(64), ptr noalias nofree noundef nonnull readonly captures(address, read_provenance), i64 noundef range(i64 0, -9223372036854775808)) unnamed_addr #0

; Function Attrs: nofree norecurse nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
declare void @_RNvXs8_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKeyINtNtCsgxBkk5gSRhY_4core7convert7TryFromNtB5_20VerificationKeyBytesE8try_from(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([200 x i8]) align 8 captures(none) dereferenceable(200) initializes((0, 1)), ptr dead_on_return noalias nofree noundef readonly align 1 captures(none) dereferenceable(32)) unnamed_addr #1

; Function Attrs: nounwind nonlazybind uwtable
define noundef zeroext i1 @agave_ed25519_verify(ptr noalias nofree noundef readonly captures(none) dereferenceable(32) %pk, ptr noalias nofree noundef readonly captures(address, read_provenance) dereferenceable(64) %sig, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) %msg.0, i64 noundef range(i64 0, -9223372036854775808) %msg.1) unnamed_addr #0 {
start:
  %_11 = alloca [64 x i8], align 1
  %_5 = alloca [200 x i8], align 8
  %vk = alloca [192 x i8], align 8
  call void @llvm.lifetime.start.p0(ptr nonnull %_5)
  call void @_RNvXs8_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKeyINtNtCsgxBkk5gSRhY_4core7convert7TryFromNtB5_20VerificationKeyBytesE8try_from(ptr noalias nofree noundef nonnull sret([200 x i8]) align 8 captures(none) dereferenceable(200) %_5, ptr noalias nofree noundef nonnull readonly align 1 captures(none) dereferenceable(32) %pk) #4
  %0 = load i8, ptr %_5, align 8, !range !4, !noundef !5
  %1 = trunc nuw i8 %0 to i1
  br i1 %1, label %bb3, label %bb2

bb3:                                              ; preds = %start
  call void @llvm.lifetime.end.p0(ptr nonnull %_5)
  br label %bb6

bb2:                                              ; preds = %start
  call void @llvm.lifetime.start.p0(ptr nonnull %vk)
  %2 = getelementptr inbounds nuw i8, ptr %_5, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(192) %vk, ptr noundef nonnull align 8 dereferenceable(192) %2, i64 192, i1 false)
  call void @llvm.lifetime.end.p0(ptr nonnull %_5)
  call void @llvm.lifetime.start.p0(ptr nonnull %_11)
  call void @_RNvMCsgDXCIgPwL6d_7ed25519NtB2_9Signature10from_bytes(ptr noalias nofree noundef nonnull sret([64 x i8]) align 1 captures(none) dereferenceable(64) %_11, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) dereferenceable(64) %sig) #4
  %_8 = call noundef i8 @_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey12verify_dalek(ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(192) %vk, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) dereferenceable(64) %_11, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) %msg.0, i64 noundef %msg.1) #4
  %3 = icmp eq i8 %_8, -1
  call void @llvm.lifetime.end.p0(ptr nonnull %_11)
  call void @llvm.lifetime.end.p0(ptr nonnull %vk)
  br label %bb6

bb6:                                              ; preds = %bb2, %bb3
  %_0.sroa.0.0 = phi i1 [ false, %bb3 ], [ %3, %bb2 ]
  ret i1 %_0.sroa.0.0
}

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #2

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #3

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #2

; Function Attrs: nounwind nonlazybind uwtable
declare void @_RNvMCsgDXCIgPwL6d_7ed25519NtB2_9Signature10from_bytes(ptr dead_on_unwind noalias nofree noundef writable sret([64 x i8]) align 1 captures(none) dereferenceable(64), ptr noalias nofree noundef readonly captures(address, read_provenance) dereferenceable(64)) unnamed_addr #0

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nofree norecurse nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #3 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #4 = { nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{i8 0, i8 2}
!5 = !{}
