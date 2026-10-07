; ModuleID = '/home/nine/Documents/anza-code/.lmf-rir-ed25519/SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/generated/fd_sha512_fini.ll'
source_filename = "src/ballet/sha512/fd_sha512.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: nofree norecurse nosync nounwind memory(argmem: readwrite) uwtable
declare hidden fastcc void @fd_sha512_core_ref(ptr noundef captures(none), ptr noundef readonly captures(none), i64 noundef range(i64 1, 144115188075855872)) unnamed_addr #0

; Function Attrs: nofree norecurse nosync nounwind memory(argmem: readwrite) uwtable
define dso_local noundef ptr @fd_sha512_fini(ptr noundef captures(none) %0, ptr noundef returned writeonly captures(ret: address, provenance) initializes((0, 64)) %1) local_unnamed_addr #0 {
  %3 = getelementptr inbounds nuw i8, ptr %0, i64 128
  %4 = getelementptr inbounds nuw i8, ptr %0, i64 200
  %5 = load i64, ptr %4, align 8, !tbaa !5
  %6 = getelementptr inbounds nuw i8, ptr %0, i64 208
  %7 = load i64, ptr %6, align 16, !tbaa !10
  %8 = getelementptr inbounds nuw i8, ptr %0, i64 216
  %9 = load i64, ptr %8, align 8, !tbaa !11
  %10 = getelementptr inbounds nuw i8, ptr %0, i64 %5
  store i8 -128, ptr %10, align 1, !tbaa !12
  %11 = add i64 %5, 1
  %12 = icmp ugt i64 %11, 112
  br i1 %12, label %13, label %16, !prof !13

13:                                               ; preds = %2
  %14 = getelementptr inbounds nuw i8, ptr %0, i64 %11
  %15 = sub i64 127, %5
  tail call void @llvm.memset.p0.i64(ptr nonnull align 1 %14, i8 0, i64 range(i64 129, 113) %15, i1 false)
  tail call fastcc void @fd_sha512_core_ref(ptr noundef nonnull %3, ptr noundef %0, i64 noundef 1)
  br label %16

16:                                               ; preds = %13, %2
  %17 = phi i64 [ 0, %13 ], [ %11, %2 ]
  %18 = getelementptr inbounds nuw i8, ptr %0, i64 %17
  %19 = sub nuw nsw i64 112, %17
  tail call void @llvm.memset.p0.i64(ptr align 1 %18, i8 0, i64 range(i64 129, 113) %19, i1 false)
  %20 = tail call noundef i64 @llvm.bswap.i64(i64 %9)
  %21 = getelementptr inbounds nuw i8, ptr %0, i64 112
  store i64 %20, ptr %21, align 8, !tbaa !14
  %22 = tail call noundef i64 @llvm.bswap.i64(i64 %7)
  %23 = getelementptr inbounds nuw i8, ptr %0, i64 120
  store i64 %22, ptr %23, align 8, !tbaa !14
  tail call fastcc void @fd_sha512_core_ref(ptr noundef nonnull %3, ptr noundef %0, i64 noundef 1)
  %24 = load i64, ptr %3, align 8, !tbaa !14
  %25 = tail call noundef i64 @llvm.bswap.i64(i64 %24)
  store i64 %25, ptr %1, align 8
  %26 = getelementptr inbounds nuw i8, ptr %0, i64 136
  %27 = load i64, ptr %26, align 8, !tbaa !14
  %28 = tail call noundef i64 @llvm.bswap.i64(i64 %27)
  %29 = getelementptr inbounds nuw i8, ptr %1, i64 8
  store i64 %28, ptr %29, align 8
  %30 = getelementptr inbounds nuw i8, ptr %0, i64 144
  %31 = load i64, ptr %30, align 8, !tbaa !14
  %32 = tail call noundef i64 @llvm.bswap.i64(i64 %31)
  %33 = getelementptr inbounds nuw i8, ptr %1, i64 16
  store i64 %32, ptr %33, align 8
  %34 = getelementptr inbounds nuw i8, ptr %0, i64 152
  %35 = load i64, ptr %34, align 8, !tbaa !14
  %36 = tail call noundef i64 @llvm.bswap.i64(i64 %35)
  %37 = getelementptr inbounds nuw i8, ptr %1, i64 24
  store i64 %36, ptr %37, align 8
  %38 = getelementptr inbounds nuw i8, ptr %0, i64 160
  %39 = load i64, ptr %38, align 8, !tbaa !14
  %40 = tail call noundef i64 @llvm.bswap.i64(i64 %39)
  %41 = getelementptr inbounds nuw i8, ptr %1, i64 32
  store i64 %40, ptr %41, align 8
  %42 = getelementptr inbounds nuw i8, ptr %0, i64 168
  %43 = load i64, ptr %42, align 8, !tbaa !14
  %44 = tail call noundef i64 @llvm.bswap.i64(i64 %43)
  %45 = getelementptr inbounds nuw i8, ptr %1, i64 40
  store i64 %44, ptr %45, align 8
  %46 = getelementptr inbounds nuw i8, ptr %0, i64 176
  %47 = load i64, ptr %46, align 8, !tbaa !14
  %48 = tail call noundef i64 @llvm.bswap.i64(i64 %47)
  %49 = getelementptr inbounds nuw i8, ptr %1, i64 48
  store i64 %48, ptr %49, align 8
  %50 = getelementptr inbounds nuw i8, ptr %0, i64 184
  %51 = load i64, ptr %50, align 8, !tbaa !14
  %52 = tail call noundef i64 @llvm.bswap.i64(i64 %51)
  %53 = getelementptr inbounds nuw i8, ptr %1, i64 56
  store i64 %52, ptr %53, align 8
  ret ptr %1
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr writeonly captures(none), i8, i64, i1 immarg) #1

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.bswap.i64(i64) #2

attributes #0 = { nofree norecurse nosync nounwind memory(argmem: readwrite) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #2 = { nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none) }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{!"Ubuntu clang version 21.1.8 (6ubuntu1)"}
!5 = !{!6, !9, i64 200}
!6 = !{!"fd_sha512_private", !7, i64 0, !7, i64 128, !9, i64 192, !9, i64 200, !9, i64 208, !9, i64 216}
!7 = !{!"omnipotent char", !8, i64 0}
!8 = !{!"Simple C/C++ TBAA"}
!9 = !{!"long", !7, i64 0}
!10 = !{!6, !9, i64 208}
!11 = !{!6, !9, i64 216}
!12 = !{!7, !7, i64 0}
!13 = !{!"branch_weights", !"expected", i32 1, i32 2000}
!14 = !{!9, !9, i64 0}
