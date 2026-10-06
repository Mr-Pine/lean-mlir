; ModuleID = '/home/nine/Documents/anza-code/.lmf-rir-ed25519/SSA/Projects/Agave/Ed25519/MLIR/generated/agave_verify_dalek.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_d6091242425a18f93aa551ed73483e0d = internal unnamed_addr constant [40 x i8] c"\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00", align 8
@_RNvNtNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend10cpuid_avx27STORAGE = external local_unnamed_addr global [1 x i8], align 1

; Function Attrs: mustprogress nofree noinline norecurse nounwind nonlazybind willreturn memory(inaccessiblemem: readwrite) uwtable
declare noundef i8 @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519(i8 noundef) unnamed_addr #0

; Function Attrs: nofree norecurse nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
declare void @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_18CompressedEdwardsY10decompress(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([168 x i8]) align 8 captures(none) dereferenceable(168) initializes((0, 8)), ptr noalias nofree noundef readonly captures(none) dereferenceable(32)) unnamed_addr #1

; Function Attrs: nounwind nonlazybind uwtable
define noundef range(i8 -1, 3) i8 @_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey12verify_dalek(ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(192) %self, ptr noalias nofree noundef readonly captures(none) dereferenceable(64) %signature, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) %msg.0, i64 noundef range(i64 0, -9223372036854775808) %msg.1) unnamed_addr #2 {
start:
  %_3.i.i.i = alloca [32 x i8], align 1
  %_4.i.i7.i = alloca [160 x i8], align 8
  %_3.i8.i = alloca [160 x i8], align 8
  %_4.i.i.i = alloca [160 x i8], align 8
  %_3.i.i = alloca [160 x i8], align 8
  %_27.i = alloca [160 x i8], align 8
  %expected_R.i = alloca [32 x i8], align 1
  %s.i = alloca [32 x i8], align 1
  %_9.i = alloca [168 x i8], align 8
  %_8.sroa.7.i = alloca [166 x i8], align 2
  %_7.sroa.7.i = alloca [166 x i8], align 2
  %R.i = alloca [160 x i8], align 8
  %_4 = alloca [32 x i8], align 1
  call void @llvm.lifetime.start.p0(ptr nonnull %_4)
  call fastcc void @_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey16challenge_scalar(ptr noalias nofree noundef align 1 captures(address) dereferenceable(32) %_4, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(192) %self, ptr noalias nofree noundef readonly captures(address, read_provenance) dereferenceable(64) %signature, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) %msg.0, i64 noundef %msg.1) #13
  %_5.i = getelementptr inbounds nuw i8, ptr %self, i64 32
  call void @llvm.lifetime.start.p0(ptr nonnull %_3.i.i), !noalias !4
  call void @_RNvMsx_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint12mul_by_pow_2(ptr noalias nofree noundef nonnull sret([160 x i8]) align 8 captures(address) dereferenceable(160) %_3.i.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_5.i, i32 noundef 3) #13, !noalias !11
  call void @llvm.lifetime.start.p0(ptr nonnull %_4.i.i.i), !noalias !12
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 8 dereferenceable(160) %_4.i.i.i, i8 0, i64 40, i1 false), !alias.scope !15, !noalias !12
  %0 = getelementptr inbounds nuw i8, ptr %_4.i.i.i, i64 40
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %0, ptr noundef nonnull align 8 dereferenceable(40) @alloc_d6091242425a18f93aa551ed73483e0d, i64 40, i1 false), !noalias !12
  %1 = getelementptr inbounds nuw i8, ptr %_4.i.i.i, i64 80
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %1, ptr noundef nonnull align 8 dereferenceable(40) @alloc_d6091242425a18f93aa551ed73483e0d, i64 40, i1 false), !noalias !12
  %2 = getelementptr inbounds nuw i8, ptr %_4.i.i.i, i64 120
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %2, i8 0, i64 40, i1 false), !alias.scope !15, !noalias !12
  %_2.i.i.i = call noundef i8 @_RNvXsd_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPointNtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq(ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_3.i.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_4.i.i.i) #13, !noalias !4
  %_0.i.i.not.i = icmp eq i8 %_2.i.i.i, 0
  call void @llvm.lifetime.end.p0(ptr nonnull %_4.i.i.i), !noalias !12
  call void @llvm.lifetime.end.p0(ptr nonnull %_3.i.i), !noalias !4
  br i1 %_0.i.i.not.i, label %bb3.i, label %_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey22verify_dalek_prehashed.exit

bb3.i:                                            ; preds = %start
  call void @llvm.lifetime.start.p0(ptr nonnull %R.i), !noalias !18
  call void @llvm.lifetime.start.p0(ptr nonnull %_7.sroa.7.i)
  call void @llvm.lifetime.start.p0(ptr nonnull %_8.sroa.7.i)
  call void @llvm.lifetime.start.p0(ptr nonnull %_9.i), !noalias !18
  call void @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_18CompressedEdwardsY10decompress(ptr noalias nofree noundef nonnull sret([168 x i8]) align 8 captures(none) dereferenceable(168) %_9.i, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) dereferenceable(64) %signature) #13, !noalias !19
  %_34.i = load i64, ptr %_9.i, align 8, !range !20, !noalias !18, !noundef !21
  %3 = trunc nuw i64 %_34.i to i1
  br i1 %3, label %bb18.i, label %bb17.i

bb18.i:                                           ; preds = %bb3.i
  %4 = getelementptr inbounds nuw i8, ptr %_9.i, i64 8
  %_8.sroa.7.8..sroa_idx.i = getelementptr inbounds nuw i8, ptr %_8.sroa.7.i, i64 6
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 2 dereferenceable(160) %_8.sroa.7.8..sroa_idx.i, ptr noundef nonnull align 8 dereferenceable(160) %4, i64 160, i1 false), !noalias !18
  call void @llvm.lifetime.end.p0(ptr nonnull %_9.i), !noalias !18
  %_7.sroa.7.8..sroa_idx.i = getelementptr inbounds nuw i8, ptr %_7.sroa.7.i, i64 6
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 2 dereferenceable(160) %_7.sroa.7.8..sroa_idx.i, ptr noundef nonnull align 2 dereferenceable(160) %_8.sroa.7.8..sroa_idx.i, i64 160, i1 false), !noalias !18
  call void @llvm.lifetime.end.p0(ptr nonnull %_8.sroa.7.i)
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(160) %R.i, ptr noundef nonnull align 2 dereferenceable(160) %_7.sroa.7.8..sroa_idx.i, i64 160, i1 false), !noalias !18
  call void @llvm.lifetime.end.p0(ptr nonnull %_7.sroa.7.i)
  call void @llvm.lifetime.start.p0(ptr nonnull %_3.i8.i), !noalias !22
  call void @_RNvMsx_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint12mul_by_pow_2(ptr noalias nofree noundef nonnull sret([160 x i8]) align 8 captures(address) dereferenceable(160) %_3.i8.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %R.i, i32 noundef 3) #13, !noalias !18
  call void @llvm.lifetime.start.p0(ptr nonnull %_4.i.i7.i), !noalias !25
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 8 dereferenceable(160) %_4.i.i7.i, i8 0, i64 40, i1 false), !alias.scope !28, !noalias !25
  %5 = getelementptr inbounds nuw i8, ptr %_4.i.i7.i, i64 40
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %5, ptr noundef nonnull align 8 dereferenceable(40) @alloc_d6091242425a18f93aa551ed73483e0d, i64 40, i1 false), !noalias !25
  %6 = getelementptr inbounds nuw i8, ptr %_4.i.i7.i, i64 80
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %6, ptr noundef nonnull align 8 dereferenceable(40) @alloc_d6091242425a18f93aa551ed73483e0d, i64 40, i1 false), !noalias !25
  %7 = getelementptr inbounds nuw i8, ptr %_4.i.i7.i, i64 120
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %7, i8 0, i64 40, i1 false), !alias.scope !28, !noalias !25
  %_2.i.i9.i = call noundef i8 @_RNvXsd_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPointNtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq(ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_3.i8.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_4.i.i7.i) #13, !noalias !22
  %_0.i.i10.not.i = icmp eq i8 %_2.i.i9.i, 0
  call void @llvm.lifetime.end.p0(ptr nonnull %_4.i.i7.i), !noalias !25
  call void @llvm.lifetime.end.p0(ptr nonnull %_3.i8.i), !noalias !22
  br i1 %_0.i.i10.not.i, label %bb8.i, label %bb16.sink.split.i

bb17.i:                                           ; preds = %bb3.i
  call void @llvm.lifetime.end.p0(ptr nonnull %_9.i), !noalias !18
  call void @llvm.lifetime.end.p0(ptr nonnull %_8.sroa.7.i)
  call void @llvm.lifetime.end.p0(ptr nonnull %_7.sroa.7.i)
  br label %bb16.sink.split.i

bb8.i:                                            ; preds = %bb18.i
  call void @llvm.lifetime.start.p0(ptr nonnull %s.i), !noalias !18
  %8 = getelementptr inbounds nuw i8, ptr %signature, i64 32
  %_22.i.sroa.0.0.copyload = load i8, ptr %8, align 1, !noalias !19
  %_22.i.sroa.41.0..sroa_idx = getelementptr inbounds nuw i8, ptr %signature, i64 63
  %_22.i.sroa.41.0.copyload = load i8, ptr %_22.i.sroa.41.0..sroa_idx, align 1, !noalias !19
  %isnotneg.i.i = icmp sgt i8 %_22.i.sroa.41.0.copyload, -1
  %_11.i.i = zext i1 %isnotneg.i.i to i8
  %high_bit_unset.i.i = tail call noundef i8 @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519(i8 noundef %_11.i.i) #14
  call void @llvm.lifetime.start.p0(ptr nonnull %_3.i.i.i), !noalias !31
  call fastcc void @_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar6reduce(ptr noalias nofree noundef align 1 captures(address) dereferenceable(32) %_3.i.i.i, ptr noalias nofree noundef nonnull readonly align 1 captures(address, read_provenance) dereferenceable(32) %8) #13, !noalias !19
  %_0.i.i.i.i = call fastcc noundef i8 @_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519(ptr noalias nofree noundef nonnull readonly align 1 captures(address, read_provenance) dereferenceable(32) %8, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) dereferenceable(32) %_3.i.i.i) #15
  call void @llvm.lifetime.end.p0(ptr nonnull %_3.i.i.i), !noalias !31
  %_13.i.i = and i8 %_0.i.i.i.i, %high_bit_unset.i.i
  %_15.i.i = tail call noundef i8 @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519(i8 noundef %_13.i.i) #14
  %9 = icmp eq i8 %_15.i.i, 1
  br i1 %9, label %bb19.i, label %bb20.i

bb19.i:                                           ; preds = %bb8.i
  %10 = getelementptr inbounds nuw i8, ptr %signature, i64 33
  %val1.sroa.4.0.s.sroa_idx.i = getelementptr inbounds nuw i8, ptr %s.i, i64 1
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 1 dereferenceable(31) %val1.sroa.4.0.s.sroa_idx.i, ptr noundef nonnull readonly align 1 dereferenceable(31) %10, i64 31, i1 false), !noalias !19
  store i8 %_22.i.sroa.0.0.copyload, ptr %s.i, align 1, !noalias !18
  call void @llvm.lifetime.start.p0(ptr nonnull %expected_R.i), !noalias !18
  call void @llvm.lifetime.start.p0(ptr nonnull %_27.i), !noalias !18
  %11 = load atomic i8, ptr @_RNvNtNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend10cpuid_avx27STORAGE monotonic, align 1, !noalias !37
  %12 = icmp eq i8 %11, -1
  br i1 %12, label %bb4.i.i.i.i, label %_RNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend.exit.i.i.i, !prof !48

bb4.i.i.i.i:                                      ; preds = %bb19.i
  %_1.i.i.i.i = tail call noundef zeroext i1 @_RNvNvNtNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend10cpuid_avx28init_get10init_inner() #13, !noalias !37
  br label %_RNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend.exit.i.i.i

_RNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend.exit.i.i.i: ; preds = %bb4.i.i.i.i, %bb19.i
  %13 = load atomic i8, ptr @_RNvNtNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend10cpuid_avx27STORAGE monotonic, align 1, !noalias !37
  %.not.i.i.i = icmp eq i8 %13, 1
  br i1 %.not.i.i.i, label %bb4.i.i.i, label %bb3.i.i.i

bb3.i.i.i:                                        ; preds = %_RNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend.exit.i.i.i
  call fastcc void @_RNvNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial10scalar_mul19vartime_double_base3mul(ptr noalias nofree noundef nonnull align 8 captures(address) dereferenceable(160) %_27.i, ptr noalias nofree noundef nonnull readonly align 1 captures(address, read_provenance) dereferenceable(32) %_4, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_5.i, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) dereferenceable(32) %s.i) #13, !noalias !49
  br label %_RNvMsw_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint.exit.i

bb4.i.i.i:                                        ; preds = %_RNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend.exit.i.i.i
  call fastcc void @_RNvNvNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector10scalar_mul19vartime_double_base9spec_avx23mul9__impl_mul(ptr noalias nofree noundef nonnull align 8 captures(address) dereferenceable(160) %_27.i, ptr noalias nofree noundef nonnull readonly align 1 captures(address, read_provenance) dereferenceable(32) %_4, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_5.i, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) dereferenceable(32) %s.i) #13, !noalias !49
  br label %_RNvMsw_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint.exit.i

_RNvMsw_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint.exit.i: ; preds = %bb4.i.i.i, %bb3.i.i.i
  call void @_RNvMsg_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint8compress(ptr noalias nofree noundef nonnull sret([32 x i8]) align 1 captures(none) dereferenceable(32) %expected_R.i, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_27.i) #13, !noalias !18
  call void @llvm.lifetime.end.p0(ptr nonnull %_27.i), !noalias !18
  %bcmp.i = call i32 @bcmp(ptr noundef nonnull dereferenceable(32) %expected_R.i, ptr noundef nonnull readonly dereferenceable(64) %signature, i64 32), !noalias !19
  %_31.i = icmp eq i32 %bcmp.i, 0
  %..i = select i1 %_31.i, i8 -1, i8 2
  call void @llvm.lifetime.end.p0(ptr nonnull %expected_R.i), !noalias !18
  call void @llvm.lifetime.end.p0(ptr nonnull %s.i), !noalias !18
  br label %bb16.sink.split.i

bb20.i:                                           ; preds = %bb8.i
  call void @llvm.lifetime.end.p0(ptr nonnull %s.i), !noalias !18
  br label %bb16.sink.split.i

bb16.sink.split.i:                                ; preds = %bb20.i, %_RNvMsw_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint.exit.i, %bb17.i, %bb18.i
  %_0.sroa.0.2.ph.i = phi i8 [ %..i, %_RNvMsw_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint.exit.i ], [ 2, %bb18.i ], [ 2, %bb20.i ], [ 2, %bb17.i ]
  call void @llvm.lifetime.end.p0(ptr nonnull %R.i), !noalias !18
  br label %_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey22verify_dalek_prehashed.exit

_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey22verify_dalek_prehashed.exit: ; preds = %bb16.sink.split.i, %start
  %_0.sroa.0.2.i = phi i8 [ 2, %start ], [ %_0.sroa.0.2.ph.i, %bb16.sink.split.i ]
  call void @llvm.lifetime.end.p0(ptr nonnull %_4)
  ret i8 %_0.sroa.0.2.i
}

; Function Attrs: nounwind nonlazybind uwtable
declare hidden fastcc void @_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey16challenge_scalar(ptr dead_on_unwind noalias nofree noundef nonnull writable writeonly align 1 captures(none) dereferenceable(32) initializes((0, 32)), ptr noalias nofree noundef nonnull readonly align 8 captures(none) dereferenceable(192), ptr noalias nofree noundef nonnull readonly captures(none) dereferenceable(64), ptr noalias nofree noundef nonnull readonly captures(address, read_provenance), i64 noundef range(i64 0, -9223372036854775808)) unnamed_addr #2

; Function Attrs: nofree norecurse nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
declare void @_RNvMsg_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint8compress(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([32 x i8]) align 1 captures(none) dereferenceable(32) initializes((0, 32)), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160)) unnamed_addr #1

; Function Attrs: nofree norecurse nounwind nonlazybind uwtable
declare hidden fastcc void @_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar6reduce(ptr dead_on_unwind noalias nofree noundef nonnull writable writeonly align 1 captures(none) dereferenceable(32) initializes((0, 32)), ptr noalias nofree noundef nonnull readonly captures(none) dereferenceable(32)) unnamed_addr #3

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
declare void @_RNvMsx_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint12mul_by_pow_2(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([160 x i8]) align 8 captures(none) dereferenceable(160), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160), i32 noundef) unnamed_addr #4

; Function Attrs: nounwind nonlazybind uwtable
declare hidden fastcc void @_RNvNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial10scalar_mul19vartime_double_base3mul(ptr dead_on_unwind noalias nofree noundef nonnull writable writeonly align 8 captures(none) dereferenceable(160), ptr noalias nofree noundef nonnull readonly captures(none) dereferenceable(32), ptr noalias nofree noundef nonnull readonly align 8 captures(none) dereferenceable(160), ptr noalias nofree noundef nonnull readonly captures(none) dereferenceable(32)) unnamed_addr #2

; Function Attrs: nounwind nonlazybind uwtable
declare hidden fastcc void @_RNvNvNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector10scalar_mul19vartime_double_base9spec_avx23mul9__impl_mul(ptr dead_on_unwind noalias nofree noundef nonnull writable writeonly align 8 captures(none) dereferenceable(160), ptr noalias nofree noundef nonnull readonly captures(none) dereferenceable(32), ptr noalias nofree noundef nonnull readonly align 8 captures(none) dereferenceable(160), ptr noalias nofree noundef nonnull readonly captures(none) dereferenceable(32)) unnamed_addr #5

; Function Attrs: cold nounwind nonlazybind uwtable
declare noundef zeroext i1 @_RNvNvNtNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend10cpuid_avx28init_get10init_inner() unnamed_addr #6

; Function Attrs: inlinehint mustprogress nofree norecurse nounwind nonlazybind willreturn memory(argmem: read, inaccessiblemem: readwrite) uwtable
declare hidden fastcc noundef i8 @_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519(ptr noalias nofree noundef nonnull readonly captures(none), ptr noalias nofree noundef nonnull readonly captures(none)) unnamed_addr #7

; Function Attrs: mustprogress nofree norecurse nounwind nonlazybind willreturn memory(argmem: read, inaccessiblemem: readwrite) uwtable
declare noundef i8 @_RNvXsd_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPointNtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq(ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160)) unnamed_addr #8

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #9

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #10

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #9

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr writeonly captures(none), i8, i64, i1 immarg) #11

; Function Attrs: nocallback nofree nounwind nonlazybind willreturn memory(argmem: read)
declare i32 @bcmp(ptr captures(none), ptr captures(none), i64) local_unnamed_addr #12

attributes #0 = { mustprogress nofree noinline norecurse nounwind nonlazybind willreturn memory(inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nofree norecurse nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { nofree norecurse nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #4 = { nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #5 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }
attributes #6 = { cold nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #7 = { inlinehint mustprogress nofree norecurse nounwind nonlazybind willreturn memory(argmem: read, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #8 = { mustprogress nofree norecurse nounwind nonlazybind willreturn memory(argmem: read, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #9 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #10 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #11 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #12 = { nocallback nofree nounwind nonlazybind willreturn memory(argmem: read) }
attributes #13 = { nounwind }
attributes #14 = { noinline nounwind }
attributes #15 = { inlinehint nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{!5, !7, !9, !10}
!5 = distinct !{!5, !6, !"_RNvMsx_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint14is_small_order: %self"}
!6 = distinct !{!6, !"_RNvMsx_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint14is_small_order"}
!7 = distinct !{!7, !8, !"_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey22verify_dalek_prehashed: %self"}
!8 = distinct !{!8, !"_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey22verify_dalek_prehashed"}
!9 = distinct !{!9, !8, !"_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey22verify_dalek_prehashed: %signature"}
!10 = distinct !{!10, !8, !"_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey22verify_dalek_prehashed: %h"}
!11 = !{!9, !10}
!12 = !{!13, !5, !7, !9, !10}
!13 = distinct !{!13, !14, !"_RNvXNtCsjK63O35OHGN_14solana_ed255196traitsNtNtB4_7edwards12EdwardsPointNtB2_10IsIdentity11is_identityB4_: %self"}
!14 = distinct !{!14, !"_RNvXNtCsjK63O35OHGN_14solana_ed255196traitsNtNtB4_7edwards12EdwardsPointNtB2_10IsIdentity11is_identityB4_"}
!15 = !{!16}
!16 = distinct !{!16, !17, !"_RNvXs7_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPointNtNtB7_6traits8Identity8identity: %_0"}
!17 = distinct !{!17, !"_RNvXs7_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPointNtNtB7_6traits8Identity8identity"}
!18 = !{!7, !9, !10}
!19 = !{!7, !10}
!20 = !{i64 0, i64 2}
!21 = !{}
!22 = !{!23, !7, !9, !10}
!23 = distinct !{!23, !24, !"_RNvMsx_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint14is_small_order: %self"}
!24 = distinct !{!24, !"_RNvMsx_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint14is_small_order"}
!25 = !{!26, !23, !7, !9, !10}
!26 = distinct !{!26, !27, !"_RNvXNtCsjK63O35OHGN_14solana_ed255196traitsNtNtB4_7edwards12EdwardsPointNtB2_10IsIdentity11is_identityB4_: %self"}
!27 = distinct !{!27, !"_RNvXNtCsjK63O35OHGN_14solana_ed255196traitsNtNtB4_7edwards12EdwardsPointNtB2_10IsIdentity11is_identityB4_"}
!28 = !{!29}
!29 = distinct !{!29, !30, !"_RNvXs7_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPointNtNtB7_6traits8Identity8identity: %_0"}
!30 = distinct !{!30, !"_RNvXs7_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPointNtNtB7_6traits8Identity8identity"}
!31 = !{!32, !34, !36, !7, !9, !10}
!32 = distinct !{!32, !33, !"_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar12is_canonical: %self"}
!33 = distinct !{!33, !"_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar12is_canonical"}
!34 = distinct !{!34, !35, !"_RNvMNtCsjK63O35OHGN_14solana_ed255196scalarNtB2_6Scalar20from_canonical_bytes: %_0"}
!35 = distinct !{!35, !"_RNvMNtCsjK63O35OHGN_14solana_ed255196scalarNtB2_6Scalar20from_canonical_bytes"}
!36 = distinct !{!36, !35, !"_RNvMNtCsjK63O35OHGN_14solana_ed255196scalarNtB2_6Scalar20from_canonical_bytes: %bytes"}
!37 = !{!38, !40, !41, !42, !43, !45, !46, !47, !7, !9, !10}
!38 = distinct !{!38, !39, !"_RNvNtCsjK63O35OHGN_14solana_ed255197backend23vartime_double_base_mul: %_0"}
!39 = distinct !{!39, !"_RNvNtCsjK63O35OHGN_14solana_ed255197backend23vartime_double_base_mul"}
!40 = distinct !{!40, !39, !"_RNvNtCsjK63O35OHGN_14solana_ed255197backend23vartime_double_base_mul: %a"}
!41 = distinct !{!41, !39, !"_RNvNtCsjK63O35OHGN_14solana_ed255197backend23vartime_double_base_mul: %A"}
!42 = distinct !{!42, !39, !"_RNvNtCsjK63O35OHGN_14solana_ed255197backend23vartime_double_base_mul: %b"}
!43 = distinct !{!43, !44, !"_RNvMsw_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint: %_0"}
!44 = distinct !{!44, !"_RNvMsw_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint"}
!45 = distinct !{!45, !44, !"_RNvMsw_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint: %a"}
!46 = distinct !{!46, !44, !"_RNvMsw_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint: %A"}
!47 = distinct !{!47, !44, !"_RNvMsw_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint: %b"}
!48 = !{!"branch_weights", !"expected", i32 1, i32 2000}
!49 = !{!9}
