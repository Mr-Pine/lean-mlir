; ModuleID = '/home/nine/Documents/anza-code/.lmf-rir-ed25519/SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/generated/fd_sha512_core_ref.ll'
source_filename = "src/ballet/sha512/fd_sha512.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@fd_sha512_core_ref.K = internal unnamed_addr constant [80 x i64] [i64 4794697086780616226, i64 8158064640168781261, i64 -5349999486874862801, i64 -1606136188198331460, i64 4131703408338449720, i64 6480981068601479193, i64 -7908458776815382629, i64 -6116909921290321640, i64 -2880145864133508542, i64 1334009975649890238, i64 2608012711638119052, i64 6128411473006802146, i64 8268148722764581231, i64 -9160688886553864527, i64 -7215885187991268811, i64 -4495734319001033068, i64 -1973867731355612462, i64 -1171420211273849373, i64 1135362057144423861, i64 2597628984639134821, i64 3308224258029322869, i64 5365058923640841347, i64 6679025012923562964, i64 8573033837759648693, i64 -7476448914759557205, i64 -6327057829258317296, i64 -5763719355590565569, i64 -4658551843659510044, i64 -4116276920077217854, i64 -3051310485924567259, i64 489312712824947311, i64 1452737877330783856, i64 2861767655752347644, i64 3322285676063803686, i64 5560940570517711597, i64 5996557281743188959, i64 7280758554555802590, i64 8532644243296465576, i64 -9096487096722542874, i64 -7894198246740708037, i64 -6719396339535248540, i64 -6333637450476146687, i64 -4446306890439682159, i64 -4076793802049405392, i64 -3345356375505022440, i64 -2983346525034927856, i64 -860691631967231958, i64 1182934255886127544, i64 1847814050463011016, i64 2177327727835720531, i64 2830643537854262169, i64 3796741975233480872, i64 4115178125766777443, i64 5681478168544905931, i64 6601373596472566643, i64 7507060721942968483, i64 8399075790359081724, i64 8693463985226723168, i64 -8878714635349349518, i64 -8302665154208450068, i64 -8016688836872298968, i64 -6606660893046293015, i64 -4685533653050689259, i64 -4147400797238176981, i64 -3880063495543823972, i64 -3348786107499101689, i64 -1523767162380948706, i64 -757361751448694408, i64 500013540394364858, i64 748580250866718886, i64 1242879168328830382, i64 1977374033974150939, i64 2944078676154940804, i64 3659926193048069267, i64 4368137639120453308, i64 4836135668995329356, i64 5532061633213252278, i64 6448918945643986474, i64 6902733635092675308, i64 7801388544844847127], align 16

; Function Attrs: nofree norecurse nosync nounwind memory(argmem: readwrite) uwtable
define hidden fastcc void @fd_sha512_core_ref(ptr noundef captures(none) %0, ptr noundef readonly captures(none) %1, i64 noundef range(i64 1, 144115188075855872) %2) unnamed_addr #0 {
  %4 = alloca [16 x i64], align 16
  %5 = getelementptr inbounds nuw i8, ptr %0, i64 8
  %6 = getelementptr inbounds nuw i8, ptr %0, i64 16
  %7 = getelementptr inbounds nuw i8, ptr %0, i64 24
  %8 = getelementptr inbounds nuw i8, ptr %0, i64 32
  %9 = getelementptr inbounds nuw i8, ptr %0, i64 40
  %10 = getelementptr inbounds nuw i8, ptr %0, i64 48
  %11 = getelementptr inbounds nuw i8, ptr %0, i64 56
  %12 = load i64, ptr %0, align 8, !tbaa !5
  %13 = load i64, ptr %5, align 8, !tbaa !5
  %14 = load i64, ptr %6, align 8, !tbaa !5
  %15 = load i64, ptr %7, align 8, !tbaa !5
  %16 = load i64, ptr %8, align 8, !tbaa !5
  %17 = load i64, ptr %9, align 8, !tbaa !5
  %18 = load i64, ptr %10, align 8, !tbaa !5
  %19 = load i64, ptr %11, align 8, !tbaa !5
  br label %20

20:                                               ; preds = %141, %3
  %21 = phi i64 [ %19, %3 ], [ %149, %141 ]
  %22 = phi i64 [ %18, %3 ], [ %148, %141 ]
  %23 = phi i64 [ %17, %3 ], [ %147, %141 ]
  %24 = phi i64 [ %16, %3 ], [ %146, %141 ]
  %25 = phi i64 [ %15, %3 ], [ %145, %141 ]
  %26 = phi i64 [ %14, %3 ], [ %144, %141 ]
  %27 = phi i64 [ %13, %3 ], [ %143, %141 ]
  %28 = phi i64 [ %12, %3 ], [ %142, %141 ]
  %29 = phi ptr [ %1, %3 ], [ %150, %141 ]
  %30 = phi i64 [ %2, %3 ], [ %151, %141 ]
  call void @llvm.lifetime.start.p0(ptr %4)
  br label %31

31:                                               ; preds = %31, %20
  %32 = phi i64 [ %28, %20 ], [ %72, %31 ]
  %33 = phi i64 [ %27, %20 ], [ %32, %31 ]
  %34 = phi i64 [ %26, %20 ], [ %33, %31 ]
  %35 = phi i64 [ %25, %20 ], [ %34, %31 ]
  %36 = phi i64 [ %24, %20 ], [ %71, %31 ]
  %37 = phi i64 [ %23, %20 ], [ %36, %31 ]
  %38 = phi i64 [ 0, %20 ], [ %73, %31 ]
  %39 = phi i64 [ %21, %20 ], [ %40, %31 ]
  %40 = phi i64 [ %22, %20 ], [ %37, %31 ]
  %41 = shl nuw nsw i64 %38, 3
  %42 = getelementptr inbounds nuw i8, ptr %29, i64 %41
  %43 = load i64, ptr %42, align 1
  %44 = tail call noundef i64 @llvm.bswap.i64(i64 %43)
  %45 = getelementptr inbounds nuw [16 x i64], ptr %4, i64 0, i64 %38
  store i64 %44, ptr %45, align 8, !tbaa !5
  %46 = tail call i64 @llvm.fshl.i64(i64 %36, i64 %36, i64 50)
  %47 = tail call i64 @llvm.fshl.i64(i64 %36, i64 %36, i64 46)
  %48 = xor i64 %46, %47
  %49 = tail call i64 @llvm.fshl.i64(i64 %36, i64 %36, i64 23)
  %50 = xor i64 %48, %49
  %51 = and i64 %36, %37
  %52 = xor i64 %36, -1
  %53 = and i64 %40, %52
  %54 = or i64 %51, %53
  %55 = getelementptr inbounds nuw [80 x i64], ptr @fd_sha512_core_ref.K, i64 0, i64 %38
  %56 = load i64, ptr %55, align 8, !tbaa !5
  %57 = add i64 %54, %39
  %58 = add i64 %57, %50
  %59 = add i64 %58, %44
  %60 = add i64 %59, %56
  %61 = tail call i64 @llvm.fshl.i64(i64 %32, i64 %32, i64 36)
  %62 = tail call i64 @llvm.fshl.i64(i64 %32, i64 %32, i64 30)
  %63 = xor i64 %61, %62
  %64 = tail call i64 @llvm.fshl.i64(i64 %32, i64 %32, i64 25)
  %65 = xor i64 %63, %64
  %66 = xor i64 %33, %34
  %67 = and i64 %32, %66
  %68 = and i64 %33, %34
  %69 = xor i64 %67, %68
  %70 = add i64 %65, %69
  %71 = add i64 %60, %35
  %72 = add i64 %70, %60
  %73 = add nuw nsw i64 %38, 1
  %74 = icmp eq i64 %73, 16
  br i1 %74, label %75, label %31, !llvm.loop !9

75:                                               ; preds = %75, %31
  %76 = phi i64 [ %139, %75 ], [ %72, %31 ]
  %77 = phi i64 [ %76, %75 ], [ %32, %31 ]
  %78 = phi i64 [ %77, %75 ], [ %33, %31 ]
  %79 = phi i64 [ %78, %75 ], [ %34, %31 ]
  %80 = phi i64 [ %138, %75 ], [ %71, %31 ]
  %81 = phi i64 [ %80, %75 ], [ %36, %31 ]
  %82 = phi i64 [ %85, %75 ], [ 16, %31 ]
  %83 = phi i64 [ %84, %75 ], [ %40, %31 ]
  %84 = phi i64 [ %81, %75 ], [ %37, %31 ]
  %85 = add nuw nsw i64 %82, 1
  %86 = and i64 %85, 15
  %87 = getelementptr inbounds nuw [16 x i64], ptr %4, i64 0, i64 %86
  %88 = load i64, ptr %87, align 8, !tbaa !5
  %89 = add nuw nsw i64 %82, 14
  %90 = and i64 %89, 15
  %91 = getelementptr inbounds nuw [16 x i64], ptr %4, i64 0, i64 %90
  %92 = load i64, ptr %91, align 8, !tbaa !5
  %93 = tail call i64 @llvm.fshl.i64(i64 %88, i64 %88, i64 63)
  %94 = tail call i64 @llvm.fshl.i64(i64 %88, i64 %88, i64 56)
  %95 = xor i64 %93, %94
  %96 = lshr i64 %88, 7
  %97 = xor i64 %95, %96
  %98 = tail call i64 @llvm.fshl.i64(i64 %92, i64 %92, i64 45)
  %99 = tail call i64 @llvm.fshl.i64(i64 %92, i64 %92, i64 3)
  %100 = xor i64 %98, %99
  %101 = lshr i64 %92, 6
  %102 = xor i64 %100, %101
  %103 = add nuw nsw i64 %82, 9
  %104 = and i64 %103, 15
  %105 = getelementptr inbounds nuw [16 x i64], ptr %4, i64 0, i64 %104
  %106 = load i64, ptr %105, align 8, !tbaa !5
  %107 = and i64 %82, 15
  %108 = getelementptr inbounds nuw [16 x i64], ptr %4, i64 0, i64 %107
  %109 = load i64, ptr %108, align 8, !tbaa !5
  %110 = add i64 %97, %106
  %111 = add i64 %110, %109
  %112 = add i64 %111, %102
  store i64 %112, ptr %108, align 8, !tbaa !5
  %113 = tail call i64 @llvm.fshl.i64(i64 %80, i64 %80, i64 50)
  %114 = tail call i64 @llvm.fshl.i64(i64 %80, i64 %80, i64 46)
  %115 = xor i64 %113, %114
  %116 = tail call i64 @llvm.fshl.i64(i64 %80, i64 %80, i64 23)
  %117 = xor i64 %115, %116
  %118 = and i64 %80, %81
  %119 = xor i64 %80, -1
  %120 = and i64 %84, %119
  %121 = or i64 %118, %120
  %122 = getelementptr inbounds nuw [80 x i64], ptr @fd_sha512_core_ref.K, i64 0, i64 %82
  %123 = load i64, ptr %122, align 8, !tbaa !5
  %124 = add i64 %121, %83
  %125 = add i64 %124, %117
  %126 = add i64 %125, %123
  %127 = add i64 %126, %112
  %128 = tail call i64 @llvm.fshl.i64(i64 %76, i64 %76, i64 36)
  %129 = tail call i64 @llvm.fshl.i64(i64 %76, i64 %76, i64 30)
  %130 = xor i64 %128, %129
  %131 = tail call i64 @llvm.fshl.i64(i64 %76, i64 %76, i64 25)
  %132 = xor i64 %130, %131
  %133 = xor i64 %77, %78
  %134 = and i64 %76, %133
  %135 = and i64 %77, %78
  %136 = xor i64 %134, %135
  %137 = add i64 %132, %136
  %138 = add i64 %127, %79
  %139 = add i64 %137, %127
  %140 = icmp eq i64 %85, 80
  br i1 %140, label %141, label %75, !llvm.loop !12

141:                                              ; preds = %75
  %142 = add i64 %139, %28
  store i64 %142, ptr %0, align 8, !tbaa !5
  %143 = add i64 %76, %27
  store i64 %143, ptr %5, align 8, !tbaa !5
  %144 = add i64 %77, %26
  store i64 %144, ptr %6, align 8, !tbaa !5
  %145 = add i64 %78, %25
  store i64 %145, ptr %7, align 8, !tbaa !5
  %146 = add i64 %138, %24
  store i64 %146, ptr %8, align 8, !tbaa !5
  %147 = add i64 %80, %23
  store i64 %147, ptr %9, align 8, !tbaa !5
  %148 = add i64 %81, %22
  store i64 %148, ptr %10, align 8, !tbaa !5
  %149 = add i64 %84, %21
  store i64 %149, ptr %11, align 8, !tbaa !5
  %150 = getelementptr inbounds nuw i8, ptr %29, i64 128
  call void @llvm.lifetime.end.p0(ptr %4)
  %151 = add nsw i64 %30, -1
  %152 = icmp eq i64 %151, 0
  br i1 %152, label %153, label %20, !llvm.loop !13

153:                                              ; preds = %141
  ret void
}

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.bswap.i64(i64) #1

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.fshl.i64(i64, i64, i64) #1

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #2

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #2

attributes #0 = { nofree norecurse nosync nounwind memory(argmem: readwrite) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none) }
attributes #2 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }

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
!9 = distinct !{!9, !10, !11}
!10 = !{!"llvm.loop.mustprogress"}
!11 = !{!"llvm.loop.unroll.disable"}
!12 = distinct !{!12, !10, !11}
!13 = distinct !{!13, !10, !11}
