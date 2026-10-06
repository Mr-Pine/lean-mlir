; ModuleID = '/home/nine/Documents/anza-code/.lmf-rir-ed25519/SSA/Projects/Agave/Ed25519/MLIR/generated/agave_verification_key_from_bytes.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nofree norecurse nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
declare void @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_18CompressedEdwardsY10decompress(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([168 x i8]) align 8 captures(none) dereferenceable(168) initializes((0, 8)), ptr noalias nofree noundef readonly captures(none) dereferenceable(32)) unnamed_addr #0

; Function Attrs: nofree norecurse nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
define void @_RNvXs8_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKeyINtNtCsgxBkk5gSRhY_4core7convert7TryFromNtB5_20VerificationKeyBytesE8try_from(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([200 x i8]) align 8 captures(none) dereferenceable(200) initializes((0, 1)) %_0, ptr dead_on_return noalias nofree noundef readonly align 1 captures(none) dereferenceable(32) %bytes) unnamed_addr #0 {
start:
  %_4 = alloca [168 x i8], align 8
  call void @llvm.lifetime.start.p0(ptr nonnull %_4)
  call void @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_18CompressedEdwardsY10decompress(ptr noalias nofree noundef nonnull sret([168 x i8]) align 8 captures(none) dereferenceable(168) %_4, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) dereferenceable(32) %bytes) #3
  %_12 = load i64, ptr %_4, align 8, !range !4, !noundef !5
  %0 = trunc nuw i64 %_12 to i1
  br i1 %0, label %bb6, label %bb5

bb6:                                              ; preds = %start
  %1 = getelementptr inbounds nuw i8, ptr %_4, i64 8
  %_13.sroa.4.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_4, i64 16
  %_13.sroa.6.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_4, i64 32
  %_13.sroa.8.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_4, i64 48
  %_10.sroa.9.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 80
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %_10.sroa.9.0..sroa_idx, ptr noundef nonnull align 8 dereferenceable(40) %_13.sroa.8.0..sroa_idx, i64 40, i1 false)
  %_13.sroa.9.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_4, i64 88
  %_10.sroa.10.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 120
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %_10.sroa.10.0..sroa_idx, ptr noundef nonnull align 8 dereferenceable(40) %_13.sroa.9.0..sroa_idx, i64 40, i1 false)
  %_13.sroa.10.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_4, i64 128
  %_13.sroa.11.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_4, i64 136
  %_13.sroa.13.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_4, i64 152
  %2 = getelementptr inbounds nuw i8, ptr %_0, i64 8
  %_10.sroa.4.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 40
  %_10.sroa.5.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 48
  %3 = load <2 x i64>, ptr %1, align 8
  %4 = load <2 x i64>, ptr %_13.sroa.4.0..sroa_idx, align 8
  %5 = sub <2 x i64> <i64 36028797018963664, i64 36028797018963952>, %3
  %6 = sub <2 x i64> splat (i64 36028797018963952), %4
  %7 = lshr <2 x i64> %5, splat (i64 51)
  %8 = extractelement <2 x i64> %5, i64 0
  %9 = and i64 %8, 2251799813685247
  %10 = and <2 x i64> %6, splat (i64 2251799813685247)
  %11 = add nuw nsw <2 x i64> %10, %7
  %_10.sroa.7.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 64
  %12 = load <2 x i64>, ptr %_13.sroa.6.0..sroa_idx, align 8
  %13 = sub <2 x i64> splat (i64 36028797018963952), %12
  %14 = extractelement <2 x i64> %13, i64 1
  %_21.i.i.i.i = lshr i64 %14, 51
  %15 = and <2 x i64> %13, splat (i64 2251799813685247)
  %_23.i.i.i.i = mul nuw nsw i64 %_21.i.i.i.i, 19
  %16 = shufflevector <2 x i64> %6, <2 x i64> %13, <2 x i32> <i32 1, i32 2>
  %17 = lshr <2 x i64> %16, splat (i64 51)
  %18 = add nuw nsw i64 %_23.i.i.i.i, %9
  %19 = add nuw nsw <2 x i64> %15, %17
  %_10.sroa.11.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 160
  %_10.sroa.12.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 168
  %20 = load <2 x i64>, ptr %_13.sroa.10.0..sroa_idx, align 8
  %21 = load <2 x i64>, ptr %_13.sroa.11.0..sroa_idx, align 8
  %22 = sub <2 x i64> <i64 36028797018963664, i64 36028797018963952>, %20
  %23 = sub <2 x i64> splat (i64 36028797018963952), %21
  %24 = lshr <2 x i64> %22, splat (i64 51)
  %25 = extractelement <2 x i64> %22, i64 0
  %26 = and i64 %25, 2251799813685247
  %27 = and <2 x i64> %23, splat (i64 2251799813685247)
  %28 = add nuw nsw <2 x i64> %27, %24
  %_10.sroa.14.0..sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 184
  %29 = load <2 x i64>, ptr %_13.sroa.13.0..sroa_idx, align 8
  %30 = sub <2 x i64> splat (i64 36028797018963952), %29
  %31 = extractelement <2 x i64> %30, i64 1
  %_21.i.i19.i.i = lshr i64 %31, 51
  %32 = and <2 x i64> %30, splat (i64 2251799813685247)
  %_23.i.i20.i.i = mul nuw nsw i64 %_21.i.i19.i.i, 19
  %33 = shufflevector <2 x i64> %23, <2 x i64> %30, <2 x i32> <i32 1, i32 2>
  %34 = lshr <2 x i64> %33, splat (i64 51)
  %35 = add nuw nsw i64 %_23.i.i20.i.i, %26
  %36 = add nuw nsw <2 x i64> %32, %34
  call void @llvm.lifetime.end.p0(ptr nonnull %_4)
  tail call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(32) %2, ptr noundef nonnull align 1 dereferenceable(32) %bytes, i64 32, i1 false)
  store i64 %18, ptr %_10.sroa.4.0..sroa_idx, align 8
  store <2 x i64> %11, ptr %_10.sroa.5.0..sroa_idx, align 8
  store <2 x i64> %19, ptr %_10.sroa.7.0..sroa_idx, align 8
  store i64 %35, ptr %_10.sroa.11.0..sroa_idx, align 8
  store <2 x i64> %28, ptr %_10.sroa.12.0..sroa_idx, align 8
  store <2 x i64> %36, ptr %_10.sroa.14.0..sroa_idx, align 8
  br label %bb4

bb5:                                              ; preds = %start
  call void @llvm.lifetime.end.p0(ptr nonnull %_4)
  %37 = getelementptr inbounds nuw i8, ptr %_0, i64 1
  store i8 1, ptr %37, align 1
  br label %bb4

bb4:                                              ; preds = %bb5, %bb6
  %.sink = phi i8 [ 0, %bb6 ], [ 1, %bb5 ]
  store i8 %.sink, ptr %_0, align 8
  ret void
}

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #1

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #2

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #1

attributes #0 = { nofree norecurse nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #2 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #3 = { nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{i64 0, i64 2}
!5 = !{}
