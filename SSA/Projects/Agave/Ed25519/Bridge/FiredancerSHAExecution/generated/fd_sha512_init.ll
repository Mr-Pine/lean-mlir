; ModuleID = '/home/nine/Documents/anza-code/.lmf-rir-ed25519/SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/generated/fd_sha512_init.ll'
source_filename = "src/ballet/sha512/fd_sha512.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(argmem: write) uwtable
define dso_local noundef ptr @fd_sha512_init(ptr noundef returned writeonly captures(ret: address, provenance) initializes((128, 192), (200, 224)) %0) local_unnamed_addr #0 {
  %2 = getelementptr inbounds nuw i8, ptr %0, i64 128
  store i64 7640891576956012808, ptr %2, align 128, !tbaa !5
  %3 = getelementptr inbounds nuw i8, ptr %0, i64 136
  store i64 -4942790177534073029, ptr %3, align 8, !tbaa !5
  %4 = getelementptr inbounds nuw i8, ptr %0, i64 144
  store i64 4354685564936845355, ptr %4, align 16, !tbaa !5
  %5 = getelementptr inbounds nuw i8, ptr %0, i64 152
  store i64 -6534734903238641935, ptr %5, align 8, !tbaa !5
  %6 = getelementptr inbounds nuw i8, ptr %0, i64 160
  store i64 5840696475078001361, ptr %6, align 32, !tbaa !5
  %7 = getelementptr inbounds nuw i8, ptr %0, i64 168
  store i64 -7276294671716946913, ptr %7, align 8, !tbaa !5
  %8 = getelementptr inbounds nuw i8, ptr %0, i64 176
  store i64 2270897969802886507, ptr %8, align 16, !tbaa !5
  %9 = getelementptr inbounds nuw i8, ptr %0, i64 184
  store i64 6620516959819538809, ptr %9, align 8, !tbaa !5
  %10 = getelementptr inbounds nuw i8, ptr %0, i64 200
  tail call void @llvm.memset.p0.i64(ptr noundef nonnull align 8 dereferenceable(24) %10, i8 0, i64 24, i1 false)
  ret ptr %0
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr writeonly captures(none), i8, i64, i1 immarg) #1

attributes #0 = { mustprogress nofree norecurse nosync nounwind willreturn memory(argmem: write) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback nofree nounwind willreturn memory(argmem: write) }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{!"Ubuntu clang version 21.1.8 (6ubuntu1)"}
!5 = !{!6, !6, i64 0}
!6 = !{!"long", !7, i64 0}
!7 = !{!"omnipotent char", !8, i64 0}
!8 = !{!"Simple C/C++ TBAA"}
