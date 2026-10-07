; ModuleID = '/home/nine/Documents/anza-code/.lmf-rir-ed25519/SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/generated/fd_sha512_append.ll'
source_filename = "src/ballet/sha512/fd_sha512.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: nofree norecurse nosync nounwind memory(argmem: readwrite) uwtable
define dso_local noundef ptr @fd_sha512_append(ptr noundef returned captures(ret: address, provenance) %0, ptr noundef readonly captures(none) %1, i64 noundef %2) local_unnamed_addr #0 {
  %4 = icmp eq i64 %2, 0
  br i1 %4, label %46, label %5, !prof !5

5:                                                ; preds = %3
  %6 = getelementptr inbounds nuw i8, ptr %0, i64 128
  %7 = getelementptr inbounds nuw i8, ptr %0, i64 200
  %8 = load i64, ptr %7, align 8, !tbaa !6
  %9 = getelementptr inbounds nuw i8, ptr %0, i64 208
  %10 = load i64, ptr %9, align 16, !tbaa !11
  %11 = getelementptr inbounds nuw i8, ptr %0, i64 216
  %12 = load i64, ptr %11, align 8, !tbaa !12
  %13 = shl i64 %2, 3
  %14 = add i64 %10, %13
  %15 = lshr i64 %2, 61
  %16 = add i64 %12, %15
  %17 = icmp ult i64 %14, %10
  %18 = zext i1 %17 to i64
  %19 = add i64 %16, %18
  store i64 %14, ptr %9, align 16, !tbaa !11
  store i64 %19, ptr %11, align 8, !tbaa !12
  %20 = icmp eq i64 %8, 0
  br i1 %20, label %34, label %21, !prof !13

21:                                               ; preds = %5
  %22 = sub i64 128, %8
  %23 = icmp ult i64 %2, %22
  %24 = getelementptr inbounds nuw i8, ptr %0, i64 %8
  br i1 %23, label %25, label %27, !prof !5

25:                                               ; preds = %21
  tail call void @llvm.memcpy.p0.p0.i64(ptr nonnull align 1 %24, ptr readonly align 1 %1, i64 %2, i1 false), !alias.scope !14
  %26 = add i64 %8, %2
  br label %30

27:                                               ; preds = %21
  tail call void @llvm.memcpy.p0.p0.i64(ptr nonnull align 1 %24, ptr readonly align 1 %1, i64 %22, i1 false), !alias.scope !18
  %28 = getelementptr inbounds nuw i8, ptr %1, i64 %22
  %29 = sub nuw i64 %2, %22
  tail call fastcc void @fd_sha512_core_ref(ptr noundef nonnull %6, ptr noundef %0, i64 noundef 1)
  br label %30

30:                                               ; preds = %27, %25
  %31 = phi i64 [ 0, %27 ], [ %26, %25 ]
  %32 = phi ptr [ %28, %27 ], [ %1, %25 ]
  %33 = phi i64 [ %29, %27 ], [ %2, %25 ]
  store i64 %31, ptr %7, align 8, !tbaa !6
  br i1 %23, label %46, label %34

34:                                               ; preds = %30, %5
  %35 = phi ptr [ %32, %30 ], [ %1, %5 ]
  %36 = phi i64 [ %33, %30 ], [ %2, %5 ]
  %37 = icmp ult i64 %36, 128
  br i1 %37, label %40, label %38, !prof !5

38:                                               ; preds = %34
  %39 = lshr i64 %36, 7
  tail call fastcc void @fd_sha512_core_ref(ptr noundef nonnull %6, ptr noundef %35, i64 noundef %39)
  br label %40

40:                                               ; preds = %38, %34
  %41 = and i64 %36, 127
  %42 = icmp eq i64 %41, 0
  br i1 %42, label %46, label %43, !prof !13

43:                                               ; preds = %40
  %44 = and i64 %36, -128
  %45 = getelementptr inbounds nuw i8, ptr %35, i64 %44
  tail call void @llvm.memcpy.p0.p0.i64(ptr align 1 %0, ptr readonly align 1 %45, i64 %41, i1 false), !alias.scope !22
  store i64 %41, ptr %7, align 8, !tbaa !6
  br label %46

46:                                               ; preds = %43, %40, %30, %3
  ret ptr %0
}

; Function Attrs: nofree norecurse nosync nounwind memory(argmem: readwrite) uwtable
declare hidden fastcc void @fd_sha512_core_ref(ptr noundef captures(none), ptr noundef readonly captures(none), i64 noundef range(i64 1, 144115188075855872)) unnamed_addr #0

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #1

attributes #0 = { nofree norecurse nosync nounwind memory(argmem: readwrite) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{!"Ubuntu clang version 21.1.8 (6ubuntu1)"}
!5 = !{!"branch_weights", !"expected", i32 1, i32 2000}
!6 = !{!7, !10, i64 200}
!7 = !{!"fd_sha512_private", !8, i64 0, !8, i64 128, !10, i64 192, !10, i64 200, !10, i64 208, !10, i64 216}
!8 = !{!"omnipotent char", !9, i64 0}
!9 = !{!"Simple C/C++ TBAA"}
!10 = !{!"long", !8, i64 0}
!11 = !{!7, !10, i64 208}
!12 = !{!7, !10, i64 216}
!13 = !{!"branch_weights", !"expected", i32 2000, i32 1}
!14 = !{!15, !17}
!15 = distinct !{!15, !16, !"fd_memcpy: argument 0"}
!16 = distinct !{!16, !"fd_memcpy"}
!17 = distinct !{!17, !16, !"fd_memcpy: argument 1"}
!18 = !{!19, !21}
!19 = distinct !{!19, !20, !"fd_memcpy: argument 0"}
!20 = distinct !{!20, !"fd_memcpy"}
!21 = distinct !{!21, !20, !"fd_memcpy: argument 1"}
!22 = !{!23, !25}
!23 = distinct !{!23, !24, !"fd_memcpy: argument 0"}
!24 = distinct !{!24, !"fd_memcpy"}
!25 = distinct !{!25, !24, !"fd_memcpy: argument 1"}
