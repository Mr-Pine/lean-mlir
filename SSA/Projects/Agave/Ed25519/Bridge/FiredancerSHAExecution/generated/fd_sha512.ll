; ModuleID = 'src/ballet/sha512/fd_sha512.c'
source_filename = "src/ballet/sha512/fd_sha512.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [30 x i8] c"src/ballet/sha512/fd_sha512.c\00", align 1
@__func__.fd_sha512_new = private unnamed_addr constant [14 x i8] c"fd_sha512_new\00", align 1
@.str.1 = private unnamed_addr constant [11 x i8] c"NULL shmem\00", align 1
@.str.2 = private unnamed_addr constant [17 x i8] c"misaligned shmem\00", align 1
@__func__.fd_sha512_join = private unnamed_addr constant [15 x i8] c"fd_sha512_join\00", align 1
@.str.3 = private unnamed_addr constant [11 x i8] c"NULL shsha\00", align 1
@.str.4 = private unnamed_addr constant [17 x i8] c"misaligned shsha\00", align 1
@.str.5 = private unnamed_addr constant [10 x i8] c"bad magic\00", align 1
@__func__.fd_sha512_leave = private unnamed_addr constant [16 x i8] c"fd_sha512_leave\00", align 1
@.str.6 = private unnamed_addr constant [9 x i8] c"NULL sha\00", align 1
@__func__.fd_sha512_delete = private unnamed_addr constant [17 x i8] c"fd_sha512_delete\00", align 1
@fd_sha512_core_ref.K = internal unnamed_addr constant [80 x i64] [i64 4794697086780616226, i64 8158064640168781261, i64 -5349999486874862801, i64 -1606136188198331460, i64 4131703408338449720, i64 6480981068601479193, i64 -7908458776815382629, i64 -6116909921290321640, i64 -2880145864133508542, i64 1334009975649890238, i64 2608012711638119052, i64 6128411473006802146, i64 8268148722764581231, i64 -9160688886553864527, i64 -7215885187991268811, i64 -4495734319001033068, i64 -1973867731355612462, i64 -1171420211273849373, i64 1135362057144423861, i64 2597628984639134821, i64 3308224258029322869, i64 5365058923640841347, i64 6679025012923562964, i64 8573033837759648693, i64 -7476448914759557205, i64 -6327057829258317296, i64 -5763719355590565569, i64 -4658551843659510044, i64 -4116276920077217854, i64 -3051310485924567259, i64 489312712824947311, i64 1452737877330783856, i64 2861767655752347644, i64 3322285676063803686, i64 5560940570517711597, i64 5996557281743188959, i64 7280758554555802590, i64 8532644243296465576, i64 -9096487096722542874, i64 -7894198246740708037, i64 -6719396339535248540, i64 -6333637450476146687, i64 -4446306890439682159, i64 -4076793802049405392, i64 -3345356375505022440, i64 -2983346525034927856, i64 -860691631967231958, i64 1182934255886127544, i64 1847814050463011016, i64 2177327727835720531, i64 2830643537854262169, i64 3796741975233480872, i64 4115178125766777443, i64 5681478168544905931, i64 6601373596472566643, i64 7507060721942968483, i64 8399075790359081724, i64 8693463985226723168, i64 -8878714635349349518, i64 -8302665154208450068, i64 -8016688836872298968, i64 -6606660893046293015, i64 -4685533653050689259, i64 -4147400797238176981, i64 -3880063495543823972, i64 -3348786107499101689, i64 -1523767162380948706, i64 -757361751448694408, i64 500013540394364858, i64 748580250866718886, i64 1242879168328830382, i64 1977374033974150939, i64 2944078676154940804, i64 3659926193048069267, i64 4368137639120453308, i64 4836135668995329356, i64 5532061633213252278, i64 6448918945643986474, i64 6902733635092675308, i64 7801388544844847127], align 16

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local noundef i64 @fd_sha512_align() local_unnamed_addr #0 {
  ret i64 128
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local noundef i64 @fd_sha512_footprint() local_unnamed_addr #0 {
  ret i64 256
}

; Function Attrs: nounwind uwtable
define dso_local noundef ptr @fd_sha512_new(ptr noundef %0) local_unnamed_addr #1 {
  %2 = icmp eq ptr %0, null
  br i1 %2, label %3, label %6, !prof !5

3:                                                ; preds = %1
  %4 = tail call i64 @fd_log_wallclock() #10
  %5 = tail call ptr (ptr, ...) @fd_log_private_0(ptr noundef nonnull @.str.1) #10
  tail call void @fd_log_private_1(i32 noundef 3, i64 noundef %4, ptr noundef nonnull @.str, i32 noundef 22, ptr noundef nonnull @__func__.fd_sha512_new, ptr noundef %5) #10
  br label %15

6:                                                ; preds = %1
  %7 = ptrtoint ptr %0 to i64
  %8 = and i64 %7, 127
  %9 = icmp eq i64 %8, 0
  br i1 %9, label %13, label %10, !prof !6

10:                                               ; preds = %6
  %11 = tail call i64 @fd_log_wallclock() #10
  %12 = tail call ptr (ptr, ...) @fd_log_private_0(ptr noundef nonnull @.str.2) #10
  tail call void @fd_log_private_1(i32 noundef 3, i64 noundef %11, ptr noundef nonnull @.str, i32 noundef 27, ptr noundef nonnull @__func__.fd_sha512_new, ptr noundef %12) #10
  br label %15

13:                                               ; preds = %6
  tail call void @llvm.memset.p0.i64(ptr noundef nonnull align 1 dereferenceable(256) %0, i8 0, i64 256, i1 false)
  tail call void asm sideeffect "# FD_COMPILER_MFENCE()@src/ballet/sha512/fd_sha512.c(35)", "~{memory},~{dirflag},~{fpsr},~{flags}"() #10, !srcloc !7
  %14 = getelementptr inbounds nuw i8, ptr %0, i64 192
  store volatile i64 -1045158177143107296, ptr %14, align 64, !tbaa !8
  tail call void asm sideeffect "# FD_COMPILER_MFENCE()@src/ballet/sha512/fd_sha512.c(37)", "~{memory},~{dirflag},~{fpsr},~{flags}"() #10, !srcloc !12
  br label %15

15:                                               ; preds = %13, %10, %3
  %16 = phi ptr [ null, %3 ], [ null, %10 ], [ %0, %13 ]
  ret ptr %16
}

; Function Attrs: mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(i64 immarg, ptr captures(none)) #2

declare i64 @fd_log_wallclock() local_unnamed_addr #3

declare void @fd_log_private_1(i32 noundef, i64 noundef, ptr noundef, i32 noundef, ptr noundef, ptr noundef) local_unnamed_addr #3

declare ptr @fd_log_private_0(ptr noundef, ...) local_unnamed_addr #3

; Function Attrs: mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(i64 immarg, ptr captures(none)) #2

; Function Attrs: nounwind uwtable
define dso_local noundef ptr @fd_sha512_join(ptr noundef %0) local_unnamed_addr #1 {
  %2 = icmp eq ptr %0, null
  br i1 %2, label %11, label %3, !prof !5

3:                                                ; preds = %1
  %4 = ptrtoint ptr %0 to i64
  %5 = and i64 %4, 127
  %6 = icmp eq i64 %5, 0
  br i1 %6, label %7, label %11, !prof !6

7:                                                ; preds = %3
  %8 = getelementptr inbounds nuw i8, ptr %0, i64 192
  %9 = load i64, ptr %8, align 64, !tbaa !13
  %10 = icmp eq i64 %9, -1045158177143107296
  br i1 %10, label %16, label %11, !prof !6

11:                                               ; preds = %7, %3, %1
  %12 = phi ptr [ @.str.3, %1 ], [ @.str.4, %3 ], [ @.str.5, %7 ]
  %13 = phi i32 [ 46, %1 ], [ 51, %3 ], [ 58, %7 ]
  %14 = tail call i64 @fd_log_wallclock() #10
  %15 = tail call ptr (ptr, ...) @fd_log_private_0(ptr noundef nonnull %12) #10
  tail call void @fd_log_private_1(i32 noundef 3, i64 noundef %14, ptr noundef nonnull @.str, i32 noundef %13, ptr noundef nonnull @__func__.fd_sha512_join, ptr noundef %15) #10
  br label %16

16:                                               ; preds = %11, %7
  %17 = phi ptr [ %0, %7 ], [ null, %11 ]
  ret ptr %17
}

; Function Attrs: nounwind uwtable
define dso_local noundef ptr @fd_sha512_leave(ptr noundef readnone captures(address_is_null, ret: address, provenance) %0) local_unnamed_addr #1 {
  %2 = icmp eq ptr %0, null
  br i1 %2, label %3, label %6, !prof !5

3:                                                ; preds = %1
  %4 = tail call i64 @fd_log_wallclock() #10
  %5 = tail call ptr (ptr, ...) @fd_log_private_0(ptr noundef nonnull @.str.6) #10
  tail call void @fd_log_private_1(i32 noundef 3, i64 noundef %4, ptr noundef nonnull @.str, i32 noundef 69, ptr noundef nonnull @__func__.fd_sha512_leave, ptr noundef %5) #10
  br label %6

6:                                                ; preds = %1, %3
  %7 = phi ptr [ null, %3 ], [ %0, %1 ]
  ret ptr %7
}

; Function Attrs: nounwind uwtable
define dso_local noundef ptr @fd_sha512_delete(ptr noundef %0) local_unnamed_addr #1 {
  %2 = icmp eq ptr %0, null
  br i1 %2, label %3, label %6, !prof !5

3:                                                ; preds = %1
  %4 = tail call i64 @fd_log_wallclock() #10
  %5 = tail call ptr (ptr, ...) @fd_log_private_0(ptr noundef nonnull @.str.3) #10
  tail call void @fd_log_private_1(i32 noundef 3, i64 noundef %4, ptr noundef nonnull @.str, i32 noundef 80, ptr noundef nonnull @__func__.fd_sha512_delete, ptr noundef %5) #10
  br label %21

6:                                                ; preds = %1
  %7 = ptrtoint ptr %0 to i64
  %8 = and i64 %7, 127
  %9 = icmp eq i64 %8, 0
  br i1 %9, label %13, label %10, !prof !6

10:                                               ; preds = %6
  %11 = tail call i64 @fd_log_wallclock() #10
  %12 = tail call ptr (ptr, ...) @fd_log_private_0(ptr noundef nonnull @.str.4) #10
  tail call void @fd_log_private_1(i32 noundef 3, i64 noundef %11, ptr noundef nonnull @.str, i32 noundef 85, ptr noundef nonnull @__func__.fd_sha512_delete, ptr noundef %12) #10
  br label %21

13:                                               ; preds = %6
  %14 = getelementptr inbounds nuw i8, ptr %0, i64 192
  %15 = load i64, ptr %14, align 64, !tbaa !13
  %16 = icmp eq i64 %15, -1045158177143107296
  br i1 %16, label %20, label %17, !prof !6

17:                                               ; preds = %13
  %18 = tail call i64 @fd_log_wallclock() #10
  %19 = tail call ptr (ptr, ...) @fd_log_private_0(ptr noundef nonnull @.str.5) #10
  tail call void @fd_log_private_1(i32 noundef 3, i64 noundef %18, ptr noundef nonnull @.str, i32 noundef 92, ptr noundef nonnull @__func__.fd_sha512_delete, ptr noundef %19) #10
  br label %21

20:                                               ; preds = %13
  tail call void asm sideeffect "# FD_COMPILER_MFENCE()@src/ballet/sha512/fd_sha512.c(96)", "~{memory},~{dirflag},~{fpsr},~{flags}"() #10, !srcloc !15
  store volatile i64 0, ptr %14, align 64, !tbaa !8
  tail call void asm sideeffect "# FD_COMPILER_MFENCE()@src/ballet/sha512/fd_sha512.c(98)", "~{memory},~{dirflag},~{fpsr},~{flags}"() #10, !srcloc !16
  br label %21

21:                                               ; preds = %17, %20, %10, %3
  %22 = phi ptr [ null, %3 ], [ null, %10 ], [ null, %17 ], [ %0, %20 ]
  ret ptr %22
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(argmem: write) uwtable
define dso_local noundef ptr @fd_sha384_init(ptr noundef returned writeonly captures(ret: address, provenance) initializes((128, 192), (200, 224)) %0) local_unnamed_addr #4 {
  %2 = getelementptr inbounds nuw i8, ptr %0, i64 128
  store i64 -3766243637369397544, ptr %2, align 128, !tbaa !8
  %3 = getelementptr inbounds nuw i8, ptr %0, i64 136
  store i64 7105036623409894663, ptr %3, align 8, !tbaa !8
  %4 = getelementptr inbounds nuw i8, ptr %0, i64 144
  store i64 -7973340178411365097, ptr %4, align 16, !tbaa !8
  %5 = getelementptr inbounds nuw i8, ptr %0, i64 152
  store i64 1526699215303891257, ptr %5, align 8, !tbaa !8
  %6 = getelementptr inbounds nuw i8, ptr %0, i64 160
  store i64 7436329637833083697, ptr %6, align 32, !tbaa !8
  %7 = getelementptr inbounds nuw i8, ptr %0, i64 168
  store i64 -8163818279084223215, ptr %7, align 8, !tbaa !8
  %8 = getelementptr inbounds nuw i8, ptr %0, i64 176
  store i64 -2662702644619276377, ptr %8, align 16, !tbaa !8
  %9 = getelementptr inbounds nuw i8, ptr %0, i64 184
  store i64 5167115440072839076, ptr %9, align 8, !tbaa !8
  %10 = getelementptr inbounds nuw i8, ptr %0, i64 200
  tail call void @llvm.memset.p0.i64(ptr noundef nonnull align 8 dereferenceable(24) %10, i8 0, i64 24, i1 false)
  ret ptr %0
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(argmem: write) uwtable
define dso_local noundef ptr @fd_sha512_init(ptr noundef returned writeonly captures(ret: address, provenance) initializes((128, 192), (200, 224)) %0) local_unnamed_addr #4 {
  %2 = getelementptr inbounds nuw i8, ptr %0, i64 128
  store i64 7640891576956012808, ptr %2, align 128, !tbaa !8
  %3 = getelementptr inbounds nuw i8, ptr %0, i64 136
  store i64 -4942790177534073029, ptr %3, align 8, !tbaa !8
  %4 = getelementptr inbounds nuw i8, ptr %0, i64 144
  store i64 4354685564936845355, ptr %4, align 16, !tbaa !8
  %5 = getelementptr inbounds nuw i8, ptr %0, i64 152
  store i64 -6534734903238641935, ptr %5, align 8, !tbaa !8
  %6 = getelementptr inbounds nuw i8, ptr %0, i64 160
  store i64 5840696475078001361, ptr %6, align 32, !tbaa !8
  %7 = getelementptr inbounds nuw i8, ptr %0, i64 168
  store i64 -7276294671716946913, ptr %7, align 8, !tbaa !8
  %8 = getelementptr inbounds nuw i8, ptr %0, i64 176
  store i64 2270897969802886507, ptr %8, align 16, !tbaa !8
  %9 = getelementptr inbounds nuw i8, ptr %0, i64 184
  store i64 6620516959819538809, ptr %9, align 8, !tbaa !8
  %10 = getelementptr inbounds nuw i8, ptr %0, i64 200
  tail call void @llvm.memset.p0.i64(ptr noundef nonnull align 8 dereferenceable(24) %10, i8 0, i64 24, i1 false)
  ret ptr %0
}

; Function Attrs: nofree norecurse nosync nounwind memory(argmem: readwrite) uwtable
define dso_local noundef ptr @fd_sha512_append(ptr noundef returned captures(ret: address, provenance) %0, ptr noundef readonly captures(none) %1, i64 noundef %2) local_unnamed_addr #5 {
  %4 = icmp eq i64 %2, 0
  br i1 %4, label %46, label %5, !prof !5

5:                                                ; preds = %3
  %6 = getelementptr inbounds nuw i8, ptr %0, i64 128
  %7 = getelementptr inbounds nuw i8, ptr %0, i64 200
  %8 = load i64, ptr %7, align 8, !tbaa !17
  %9 = getelementptr inbounds nuw i8, ptr %0, i64 208
  %10 = load i64, ptr %9, align 16, !tbaa !18
  %11 = getelementptr inbounds nuw i8, ptr %0, i64 216
  %12 = load i64, ptr %11, align 8, !tbaa !19
  %13 = shl i64 %2, 3
  %14 = add i64 %10, %13
  %15 = lshr i64 %2, 61
  %16 = add i64 %12, %15
  %17 = icmp ult i64 %14, %10
  %18 = zext i1 %17 to i64
  %19 = add i64 %16, %18
  store i64 %14, ptr %9, align 16, !tbaa !18
  store i64 %19, ptr %11, align 8, !tbaa !19
  %20 = icmp eq i64 %8, 0
  br i1 %20, label %34, label %21, !prof !6

21:                                               ; preds = %5
  %22 = sub i64 128, %8
  %23 = icmp ult i64 %2, %22
  %24 = getelementptr inbounds nuw i8, ptr %0, i64 %8
  br i1 %23, label %25, label %27, !prof !5

25:                                               ; preds = %21
  tail call void @llvm.memcpy.p0.p0.i64(ptr nonnull align 1 %24, ptr readonly align 1 %1, i64 %2, i1 false), !alias.scope !20
  %26 = add i64 %8, %2
  br label %30

27:                                               ; preds = %21
  tail call void @llvm.memcpy.p0.p0.i64(ptr nonnull align 1 %24, ptr readonly align 1 %1, i64 %22, i1 false), !alias.scope !24
  %28 = getelementptr inbounds nuw i8, ptr %1, i64 %22
  %29 = sub nuw i64 %2, %22
  tail call fastcc void @fd_sha512_core_ref(ptr noundef nonnull %6, ptr noundef %0, i64 noundef 1)
  br label %30

30:                                               ; preds = %27, %25
  %31 = phi i64 [ 0, %27 ], [ %26, %25 ]
  %32 = phi ptr [ %28, %27 ], [ %1, %25 ]
  %33 = phi i64 [ %29, %27 ], [ %2, %25 ]
  store i64 %31, ptr %7, align 8, !tbaa !17
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
  br i1 %42, label %46, label %43, !prof !6

43:                                               ; preds = %40
  %44 = and i64 %36, -128
  %45 = getelementptr inbounds nuw i8, ptr %35, i64 %44
  tail call void @llvm.memcpy.p0.p0.i64(ptr align 1 %0, ptr readonly align 1 %45, i64 %41, i1 false), !alias.scope !28
  store i64 %41, ptr %7, align 8, !tbaa !17
  br label %46

46:                                               ; preds = %30, %43, %40, %3
  ret ptr %0
}

; Function Attrs: nofree norecurse nosync nounwind memory(argmem: readwrite) uwtable
define internal fastcc void @fd_sha512_core_ref(ptr noundef captures(none) %0, ptr noundef readonly captures(none) %1, i64 noundef range(i64 1, 144115188075855872) %2) unnamed_addr #5 {
  %4 = alloca [16 x i64], align 16
  %5 = getelementptr inbounds nuw i8, ptr %0, i64 8
  %6 = getelementptr inbounds nuw i8, ptr %0, i64 16
  %7 = getelementptr inbounds nuw i8, ptr %0, i64 24
  %8 = getelementptr inbounds nuw i8, ptr %0, i64 32
  %9 = getelementptr inbounds nuw i8, ptr %0, i64 40
  %10 = getelementptr inbounds nuw i8, ptr %0, i64 48
  %11 = getelementptr inbounds nuw i8, ptr %0, i64 56
  %12 = load i64, ptr %0, align 8, !tbaa !8
  %13 = load i64, ptr %5, align 8, !tbaa !8
  %14 = load i64, ptr %6, align 8, !tbaa !8
  %15 = load i64, ptr %7, align 8, !tbaa !8
  %16 = load i64, ptr %8, align 8, !tbaa !8
  %17 = load i64, ptr %9, align 8, !tbaa !8
  %18 = load i64, ptr %10, align 8, !tbaa !8
  %19 = load i64, ptr %11, align 8, !tbaa !8
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
  call void @llvm.lifetime.start.p0(i64 128, ptr nonnull %4) #10
  br label %31

31:                                               ; preds = %20, %31
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
  store i64 %44, ptr %45, align 8, !tbaa !8
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
  %56 = load i64, ptr %55, align 8, !tbaa !8
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
  br i1 %74, label %75, label %31, !llvm.loop !32

75:                                               ; preds = %31, %75
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
  %88 = load i64, ptr %87, align 8, !tbaa !8
  %89 = add nuw nsw i64 %82, 14
  %90 = and i64 %89, 15
  %91 = getelementptr inbounds nuw [16 x i64], ptr %4, i64 0, i64 %90
  %92 = load i64, ptr %91, align 8, !tbaa !8
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
  %106 = load i64, ptr %105, align 8, !tbaa !8
  %107 = and i64 %82, 15
  %108 = getelementptr inbounds nuw [16 x i64], ptr %4, i64 0, i64 %107
  %109 = load i64, ptr %108, align 8, !tbaa !8
  %110 = add i64 %97, %106
  %111 = add i64 %110, %109
  %112 = add i64 %111, %102
  store i64 %112, ptr %108, align 8, !tbaa !8
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
  %123 = load i64, ptr %122, align 8, !tbaa !8
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
  br i1 %140, label %141, label %75, !llvm.loop !35

141:                                              ; preds = %75
  %142 = add i64 %139, %28
  store i64 %142, ptr %0, align 8, !tbaa !8
  %143 = add i64 %76, %27
  store i64 %143, ptr %5, align 8, !tbaa !8
  %144 = add i64 %77, %26
  store i64 %144, ptr %6, align 8, !tbaa !8
  %145 = add i64 %78, %25
  store i64 %145, ptr %7, align 8, !tbaa !8
  %146 = add i64 %138, %24
  store i64 %146, ptr %8, align 8, !tbaa !8
  %147 = add i64 %80, %23
  store i64 %147, ptr %9, align 8, !tbaa !8
  %148 = add i64 %81, %22
  store i64 %148, ptr %10, align 8, !tbaa !8
  %149 = add i64 %84, %21
  store i64 %149, ptr %11, align 8, !tbaa !8
  %150 = getelementptr inbounds nuw i8, ptr %29, i64 128
  call void @llvm.lifetime.end.p0(i64 128, ptr nonnull %4) #10
  %151 = add nsw i64 %30, -1
  %152 = icmp eq i64 %151, 0
  br i1 %152, label %153, label %20, !llvm.loop !36

153:                                              ; preds = %141
  ret void
}

; Function Attrs: nofree norecurse nosync nounwind memory(argmem: readwrite) uwtable
define dso_local noundef ptr @fd_sha512_fini(ptr noundef captures(none) %0, ptr noundef returned writeonly captures(ret: address, provenance) initializes((0, 64)) %1) local_unnamed_addr #5 {
  %3 = getelementptr inbounds nuw i8, ptr %0, i64 128
  %4 = getelementptr inbounds nuw i8, ptr %0, i64 200
  %5 = load i64, ptr %4, align 8, !tbaa !17
  %6 = getelementptr inbounds nuw i8, ptr %0, i64 208
  %7 = load i64, ptr %6, align 16, !tbaa !18
  %8 = getelementptr inbounds nuw i8, ptr %0, i64 216
  %9 = load i64, ptr %8, align 8, !tbaa !19
  %10 = getelementptr inbounds nuw i8, ptr %0, i64 %5
  store i8 -128, ptr %10, align 1, !tbaa !37
  %11 = add i64 %5, 1
  %12 = icmp ugt i64 %11, 112
  br i1 %12, label %13, label %16, !prof !5

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
  store i64 %20, ptr %21, align 8, !tbaa !8
  %22 = tail call noundef i64 @llvm.bswap.i64(i64 %7)
  %23 = getelementptr inbounds nuw i8, ptr %0, i64 120
  store i64 %22, ptr %23, align 8, !tbaa !8
  tail call fastcc void @fd_sha512_core_ref(ptr noundef nonnull %3, ptr noundef %0, i64 noundef 1)
  %24 = load i64, ptr %3, align 8, !tbaa !8
  %25 = tail call noundef i64 @llvm.bswap.i64(i64 %24)
  store i64 %25, ptr %1, align 8
  %26 = getelementptr inbounds nuw i8, ptr %0, i64 136
  %27 = load i64, ptr %26, align 8, !tbaa !8
  %28 = tail call noundef i64 @llvm.bswap.i64(i64 %27)
  %29 = getelementptr inbounds nuw i8, ptr %1, i64 8
  store i64 %28, ptr %29, align 8
  %30 = getelementptr inbounds nuw i8, ptr %0, i64 144
  %31 = load i64, ptr %30, align 8, !tbaa !8
  %32 = tail call noundef i64 @llvm.bswap.i64(i64 %31)
  %33 = getelementptr inbounds nuw i8, ptr %1, i64 16
  store i64 %32, ptr %33, align 8
  %34 = getelementptr inbounds nuw i8, ptr %0, i64 152
  %35 = load i64, ptr %34, align 8, !tbaa !8
  %36 = tail call noundef i64 @llvm.bswap.i64(i64 %35)
  %37 = getelementptr inbounds nuw i8, ptr %1, i64 24
  store i64 %36, ptr %37, align 8
  %38 = getelementptr inbounds nuw i8, ptr %0, i64 160
  %39 = load i64, ptr %38, align 8, !tbaa !8
  %40 = tail call noundef i64 @llvm.bswap.i64(i64 %39)
  %41 = getelementptr inbounds nuw i8, ptr %1, i64 32
  store i64 %40, ptr %41, align 8
  %42 = getelementptr inbounds nuw i8, ptr %0, i64 168
  %43 = load i64, ptr %42, align 8, !tbaa !8
  %44 = tail call noundef i64 @llvm.bswap.i64(i64 %43)
  %45 = getelementptr inbounds nuw i8, ptr %1, i64 40
  store i64 %44, ptr %45, align 8
  %46 = getelementptr inbounds nuw i8, ptr %0, i64 176
  %47 = load i64, ptr %46, align 8, !tbaa !8
  %48 = tail call noundef i64 @llvm.bswap.i64(i64 %47)
  %49 = getelementptr inbounds nuw i8, ptr %1, i64 48
  store i64 %48, ptr %49, align 8
  %50 = getelementptr inbounds nuw i8, ptr %0, i64 184
  %51 = load i64, ptr %50, align 8, !tbaa !8
  %52 = tail call noundef i64 @llvm.bswap.i64(i64 %51)
  %53 = getelementptr inbounds nuw i8, ptr %1, i64 56
  store i64 %52, ptr %53, align 8
  ret ptr %1
}

; Function Attrs: mustprogress nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #6

; Function Attrs: nofree norecurse nosync nounwind memory(argmem: readwrite) uwtable
define dso_local noundef ptr @fd_sha384_fini(ptr noundef captures(none) %0, ptr noundef returned writeonly captures(ret: address, provenance) initializes((0, 48)) %1) local_unnamed_addr #5 {
  %3 = getelementptr inbounds nuw i8, ptr %0, i64 128
  %4 = getelementptr inbounds nuw i8, ptr %0, i64 200
  %5 = load i64, ptr %4, align 8, !tbaa !17
  %6 = getelementptr inbounds nuw i8, ptr %0, i64 208
  %7 = load i64, ptr %6, align 16, !tbaa !18
  %8 = getelementptr inbounds nuw i8, ptr %0, i64 216
  %9 = load i64, ptr %8, align 8, !tbaa !19
  %10 = getelementptr inbounds nuw i8, ptr %0, i64 %5
  store i8 -128, ptr %10, align 1, !tbaa !37
  %11 = add i64 %5, 1
  %12 = icmp ugt i64 %11, 112
  br i1 %12, label %13, label %16, !prof !5

13:                                               ; preds = %2
  %14 = getelementptr inbounds nuw i8, ptr %0, i64 %11
  %15 = sub i64 127, %5
  tail call void @llvm.memset.p0.i64(ptr nonnull align 1 %14, i8 0, i64 range(i64 129, 113) %15, i1 false)
  tail call fastcc void @fd_sha512_core_ref(ptr noundef nonnull %3, ptr noundef %0, i64 noundef 1)
  br label %16

16:                                               ; preds = %2, %13
  %17 = phi i64 [ 0, %13 ], [ %11, %2 ]
  %18 = getelementptr inbounds nuw i8, ptr %0, i64 %17
  %19 = sub nuw nsw i64 112, %17
  tail call void @llvm.memset.p0.i64(ptr align 1 %18, i8 0, i64 range(i64 129, 113) %19, i1 false)
  %20 = tail call noundef i64 @llvm.bswap.i64(i64 %9)
  %21 = getelementptr inbounds nuw i8, ptr %0, i64 112
  store i64 %20, ptr %21, align 8, !tbaa !8
  %22 = tail call noundef i64 @llvm.bswap.i64(i64 %7)
  %23 = getelementptr inbounds nuw i8, ptr %0, i64 120
  store i64 %22, ptr %23, align 8, !tbaa !8
  tail call fastcc void @fd_sha512_core_ref(ptr noundef nonnull %3, ptr noundef %0, i64 noundef 1)
  %24 = load i64, ptr %3, align 8, !tbaa !8
  %25 = tail call noundef i64 @llvm.bswap.i64(i64 %24)
  %26 = getelementptr inbounds nuw i8, ptr %0, i64 136
  %27 = load i64, ptr %26, align 8, !tbaa !8
  %28 = tail call noundef i64 @llvm.bswap.i64(i64 %27)
  %29 = getelementptr inbounds nuw i8, ptr %0, i64 144
  %30 = load i64, ptr %29, align 8, !tbaa !8
  %31 = tail call noundef i64 @llvm.bswap.i64(i64 %30)
  %32 = getelementptr inbounds nuw i8, ptr %0, i64 152
  %33 = load i64, ptr %32, align 8, !tbaa !8
  %34 = tail call noundef i64 @llvm.bswap.i64(i64 %33)
  %35 = getelementptr inbounds nuw i8, ptr %0, i64 160
  %36 = load i64, ptr %35, align 8, !tbaa !8
  %37 = tail call noundef i64 @llvm.bswap.i64(i64 %36)
  %38 = getelementptr inbounds nuw i8, ptr %0, i64 168
  %39 = load i64, ptr %38, align 8, !tbaa !8
  %40 = tail call noundef i64 @llvm.bswap.i64(i64 %39)
  store i64 %25, ptr %1, align 1
  %41 = getelementptr inbounds nuw i8, ptr %1, i64 8
  store i64 %28, ptr %41, align 1
  %42 = getelementptr inbounds nuw i8, ptr %1, i64 16
  store i64 %31, ptr %42, align 1
  %43 = getelementptr inbounds nuw i8, ptr %1, i64 24
  store i64 %34, ptr %43, align 1
  %44 = getelementptr inbounds nuw i8, ptr %1, i64 32
  store i64 %37, ptr %44, align 1
  %45 = getelementptr inbounds nuw i8, ptr %1, i64 40
  store i64 %40, ptr %45, align 1
  ret ptr %1
}

; Function Attrs: nofree norecurse nosync nounwind memory(argmem: readwrite) uwtable
define dso_local noundef ptr @fd_sha512_hash(ptr noundef readonly captures(none) %0, i64 noundef %1, ptr noundef returned writeonly captures(ret: address, provenance) initializes((0, 64)) %2) local_unnamed_addr #5 {
  %4 = alloca [128 x i8], align 128
  %5 = alloca [8 x i64], align 64
  call void @llvm.lifetime.start.p0(i64 128, ptr nonnull %4) #10
  call void @llvm.lifetime.start.p0(i64 64, ptr nonnull %5) #10
  store i64 7640891576956012808, ptr %5, align 64, !tbaa !8
  %6 = getelementptr inbounds nuw i8, ptr %5, i64 8
  store i64 -4942790177534073029, ptr %6, align 8, !tbaa !8
  %7 = getelementptr inbounds nuw i8, ptr %5, i64 16
  store i64 4354685564936845355, ptr %7, align 16, !tbaa !8
  %8 = getelementptr inbounds nuw i8, ptr %5, i64 24
  store i64 -6534734903238641935, ptr %8, align 8, !tbaa !8
  %9 = getelementptr inbounds nuw i8, ptr %5, i64 32
  store i64 5840696475078001361, ptr %9, align 32, !tbaa !8
  %10 = getelementptr inbounds nuw i8, ptr %5, i64 40
  store i64 -7276294671716946913, ptr %10, align 8, !tbaa !8
  %11 = getelementptr inbounds nuw i8, ptr %5, i64 48
  store i64 2270897969802886507, ptr %11, align 16, !tbaa !8
  %12 = getelementptr inbounds nuw i8, ptr %5, i64 56
  store i64 6620516959819538809, ptr %12, align 8, !tbaa !8
  %13 = icmp ult i64 %1, 128
  br i1 %13, label %16, label %14, !prof !5

14:                                               ; preds = %3
  %15 = lshr i64 %1, 7
  call fastcc void @fd_sha512_core_ref(ptr noundef nonnull %5, ptr noundef %0, i64 noundef %15)
  br label %16

16:                                               ; preds = %14, %3
  %17 = and i64 %1, 127
  %18 = icmp eq i64 %17, 0
  br i1 %18, label %22, label %19, !prof !6

19:                                               ; preds = %16
  %20 = and i64 %1, -128
  %21 = getelementptr inbounds nuw i8, ptr %0, i64 %20
  call void @llvm.memcpy.p0.p0.i64(ptr nonnull align 128 %4, ptr readonly align 1 %21, i64 %17, i1 false), !alias.scope !38
  br label %22

22:                                               ; preds = %19, %16
  %23 = getelementptr inbounds nuw [128 x i8], ptr %4, i64 0, i64 %17
  store i8 -128, ptr %23, align 1, !tbaa !37
  %24 = add nuw nsw i64 %17, 1
  %25 = icmp samesign ugt i64 %17, 111
  br i1 %25, label %26, label %29, !prof !5

26:                                               ; preds = %22
  %27 = getelementptr inbounds nuw i8, ptr %4, i64 %24
  %28 = xor i64 %17, 127
  call void @llvm.memset.p0.i64(ptr nonnull align 1 %27, i8 0, i64 range(i64 129, 113) %28, i1 false)
  call fastcc void @fd_sha512_core_ref(ptr noundef nonnull %5, ptr noundef nonnull %4, i64 noundef 1)
  br label %29

29:                                               ; preds = %26, %22
  %30 = phi i64 [ 0, %26 ], [ %24, %22 ]
  %31 = shl i64 %1, 3
  %32 = getelementptr inbounds nuw i8, ptr %4, i64 %30
  %33 = sub nuw nsw i64 112, %30
  call void @llvm.memset.p0.i64(ptr nonnull align 1 %32, i8 0, i64 range(i64 129, 113) %33, i1 false)
  %34 = lshr i64 %1, 5
  %35 = and i64 %34, 504403158265495552
  %36 = getelementptr inbounds nuw i8, ptr %4, i64 112
  store i64 %35, ptr %36, align 16, !tbaa !8
  %37 = tail call noundef i64 @llvm.bswap.i64(i64 %31)
  %38 = getelementptr inbounds nuw i8, ptr %4, i64 120
  store i64 %37, ptr %38, align 8, !tbaa !8
  call fastcc void @fd_sha512_core_ref(ptr noundef nonnull %5, ptr noundef nonnull %4, i64 noundef 1)
  %39 = load i64, ptr %5, align 64, !tbaa !8
  %40 = tail call noundef i64 @llvm.bswap.i64(i64 %39)
  store i64 %40, ptr %2, align 8
  %41 = load i64, ptr %6, align 8, !tbaa !8
  %42 = tail call noundef i64 @llvm.bswap.i64(i64 %41)
  %43 = getelementptr inbounds nuw i8, ptr %2, i64 8
  store i64 %42, ptr %43, align 8
  %44 = load i64, ptr %7, align 16, !tbaa !8
  %45 = tail call noundef i64 @llvm.bswap.i64(i64 %44)
  %46 = getelementptr inbounds nuw i8, ptr %2, i64 16
  store i64 %45, ptr %46, align 8
  %47 = load i64, ptr %8, align 8, !tbaa !8
  %48 = tail call noundef i64 @llvm.bswap.i64(i64 %47)
  %49 = getelementptr inbounds nuw i8, ptr %2, i64 24
  store i64 %48, ptr %49, align 8
  %50 = load i64, ptr %9, align 32, !tbaa !8
  %51 = tail call noundef i64 @llvm.bswap.i64(i64 %50)
  %52 = getelementptr inbounds nuw i8, ptr %2, i64 32
  store i64 %51, ptr %52, align 8
  %53 = load i64, ptr %10, align 8, !tbaa !8
  %54 = tail call noundef i64 @llvm.bswap.i64(i64 %53)
  %55 = getelementptr inbounds nuw i8, ptr %2, i64 40
  store i64 %54, ptr %55, align 8
  %56 = load i64, ptr %11, align 16, !tbaa !8
  %57 = tail call noundef i64 @llvm.bswap.i64(i64 %56)
  %58 = getelementptr inbounds nuw i8, ptr %2, i64 48
  store i64 %57, ptr %58, align 8
  %59 = load i64, ptr %12, align 8, !tbaa !8
  %60 = tail call noundef i64 @llvm.bswap.i64(i64 %59)
  %61 = getelementptr inbounds nuw i8, ptr %2, i64 56
  store i64 %60, ptr %61, align 8
  call void @llvm.lifetime.end.p0(i64 64, ptr nonnull %5) #10
  call void @llvm.lifetime.end.p0(i64 128, ptr nonnull %4) #10
  ret ptr %2
}

; Function Attrs: nofree norecurse nosync nounwind memory(argmem: readwrite) uwtable
define dso_local noundef ptr @fd_sha384_hash(ptr noundef readonly captures(none) %0, i64 noundef %1, ptr noundef returned writeonly captures(ret: address, provenance) initializes((0, 48)) %2) local_unnamed_addr #5 {
  %4 = alloca [128 x i8], align 128
  %5 = alloca [8 x i64], align 64
  call void @llvm.lifetime.start.p0(i64 128, ptr nonnull %4) #10
  call void @llvm.lifetime.start.p0(i64 64, ptr nonnull %5) #10
  store i64 -3766243637369397544, ptr %5, align 64, !tbaa !8
  %6 = getelementptr inbounds nuw i8, ptr %5, i64 8
  store i64 7105036623409894663, ptr %6, align 8, !tbaa !8
  %7 = getelementptr inbounds nuw i8, ptr %5, i64 16
  store i64 -7973340178411365097, ptr %7, align 16, !tbaa !8
  %8 = getelementptr inbounds nuw i8, ptr %5, i64 24
  store i64 1526699215303891257, ptr %8, align 8, !tbaa !8
  %9 = getelementptr inbounds nuw i8, ptr %5, i64 32
  store i64 7436329637833083697, ptr %9, align 32, !tbaa !8
  %10 = getelementptr inbounds nuw i8, ptr %5, i64 40
  store i64 -8163818279084223215, ptr %10, align 8, !tbaa !8
  %11 = getelementptr inbounds nuw i8, ptr %5, i64 48
  store i64 -2662702644619276377, ptr %11, align 16, !tbaa !8
  %12 = getelementptr inbounds nuw i8, ptr %5, i64 56
  store i64 5167115440072839076, ptr %12, align 8, !tbaa !8
  %13 = icmp ult i64 %1, 128
  br i1 %13, label %16, label %14, !prof !5

14:                                               ; preds = %3
  %15 = lshr i64 %1, 7
  call fastcc void @fd_sha512_core_ref(ptr noundef nonnull %5, ptr noundef %0, i64 noundef %15)
  br label %16

16:                                               ; preds = %14, %3
  %17 = and i64 %1, 127
  %18 = icmp eq i64 %17, 0
  br i1 %18, label %22, label %19, !prof !6

19:                                               ; preds = %16
  %20 = and i64 %1, -128
  %21 = getelementptr inbounds nuw i8, ptr %0, i64 %20
  call void @llvm.memcpy.p0.p0.i64(ptr nonnull align 128 %4, ptr readonly align 1 %21, i64 %17, i1 false), !alias.scope !42
  br label %22

22:                                               ; preds = %19, %16
  %23 = getelementptr inbounds nuw [128 x i8], ptr %4, i64 0, i64 %17
  store i8 -128, ptr %23, align 1, !tbaa !37
  %24 = add nuw nsw i64 %17, 1
  %25 = icmp samesign ugt i64 %17, 111
  br i1 %25, label %26, label %29, !prof !5

26:                                               ; preds = %22
  %27 = getelementptr inbounds nuw i8, ptr %4, i64 %24
  %28 = xor i64 %17, 127
  call void @llvm.memset.p0.i64(ptr nonnull align 1 %27, i8 0, i64 range(i64 129, 113) %28, i1 false)
  call fastcc void @fd_sha512_core_ref(ptr noundef nonnull %5, ptr noundef nonnull %4, i64 noundef 1)
  br label %29

29:                                               ; preds = %26, %22
  %30 = phi i64 [ 0, %26 ], [ %24, %22 ]
  %31 = shl i64 %1, 3
  %32 = getelementptr inbounds nuw i8, ptr %4, i64 %30
  %33 = sub nuw nsw i64 112, %30
  call void @llvm.memset.p0.i64(ptr nonnull align 1 %32, i8 0, i64 range(i64 129, 113) %33, i1 false)
  %34 = lshr i64 %1, 5
  %35 = and i64 %34, 504403158265495552
  %36 = getelementptr inbounds nuw i8, ptr %4, i64 112
  store i64 %35, ptr %36, align 16, !tbaa !8
  %37 = tail call noundef i64 @llvm.bswap.i64(i64 %31)
  %38 = getelementptr inbounds nuw i8, ptr %4, i64 120
  store i64 %37, ptr %38, align 8, !tbaa !8
  call fastcc void @fd_sha512_core_ref(ptr noundef nonnull %5, ptr noundef nonnull %4, i64 noundef 1)
  %39 = load i64, ptr %5, align 64, !tbaa !8
  %40 = tail call noundef i64 @llvm.bswap.i64(i64 %39)
  store i64 %40, ptr %2, align 8
  %41 = load i64, ptr %6, align 8, !tbaa !8
  %42 = tail call noundef i64 @llvm.bswap.i64(i64 %41)
  %43 = getelementptr inbounds nuw i8, ptr %2, i64 8
  store i64 %42, ptr %43, align 8
  %44 = load i64, ptr %7, align 16, !tbaa !8
  %45 = tail call noundef i64 @llvm.bswap.i64(i64 %44)
  %46 = getelementptr inbounds nuw i8, ptr %2, i64 16
  store i64 %45, ptr %46, align 8
  %47 = load i64, ptr %8, align 8, !tbaa !8
  %48 = tail call noundef i64 @llvm.bswap.i64(i64 %47)
  %49 = getelementptr inbounds nuw i8, ptr %2, i64 24
  store i64 %48, ptr %49, align 8
  %50 = load i64, ptr %9, align 32, !tbaa !8
  %51 = tail call noundef i64 @llvm.bswap.i64(i64 %50)
  %52 = getelementptr inbounds nuw i8, ptr %2, i64 32
  store i64 %51, ptr %52, align 8
  %53 = load i64, ptr %10, align 8, !tbaa !8
  %54 = tail call noundef i64 @llvm.bswap.i64(i64 %53)
  %55 = getelementptr inbounds nuw i8, ptr %2, i64 40
  store i64 %54, ptr %55, align 8
  call void @llvm.lifetime.end.p0(i64 64, ptr nonnull %5) #10
  call void @llvm.lifetime.end.p0(i64 128, ptr nonnull %4) #10
  ret ptr %2
}

; Function Attrs: mustprogress nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr writeonly captures(none), i8, i64, i1 immarg) #7

; Function Attrs: mustprogress nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.bswap.i64(i64) #8

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.fshl.i64(i64, i64, i64) #9

attributes #0 = { mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nounwind uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #3 = { "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { mustprogress nofree norecurse nosync nounwind willreturn memory(argmem: write) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #5 = { nofree norecurse nosync nounwind memory(argmem: readwrite) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #6 = { mustprogress nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #7 = { mustprogress nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #8 = { mustprogress nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #9 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #10 = { nounwind }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{!"Ubuntu clang version 21.1.8 (6ubuntu1)"}
!5 = !{!"branch_weights", !"expected", i32 1, i32 2000}
!6 = !{!"branch_weights", !"expected", i32 2000, i32 1}
!7 = !{i64 2148243586}
!8 = !{!9, !9, i64 0}
!9 = !{!"long", !10, i64 0}
!10 = !{!"omnipotent char", !11, i64 0}
!11 = !{!"Simple C/C++ TBAA"}
!12 = !{i64 2148243860}
!13 = !{!14, !9, i64 192}
!14 = !{!"fd_sha512_private", !10, i64 0, !10, i64 128, !9, i64 192, !9, i64 200, !9, i64 208, !9, i64 216}
!15 = !{i64 2148246066}
!16 = !{i64 2148246319}
!17 = !{!14, !9, i64 200}
!18 = !{!14, !9, i64 208}
!19 = !{!14, !9, i64 216}
!20 = !{!21, !23}
!21 = distinct !{!21, !22, !"fd_memcpy: argument 0"}
!22 = distinct !{!22, !"fd_memcpy"}
!23 = distinct !{!23, !22, !"fd_memcpy: argument 1"}
!24 = !{!25, !27}
!25 = distinct !{!25, !26, !"fd_memcpy: argument 0"}
!26 = distinct !{!26, !"fd_memcpy"}
!27 = distinct !{!27, !26, !"fd_memcpy: argument 1"}
!28 = !{!29, !31}
!29 = distinct !{!29, !30, !"fd_memcpy: argument 0"}
!30 = distinct !{!30, !"fd_memcpy"}
!31 = distinct !{!31, !30, !"fd_memcpy: argument 1"}
!32 = distinct !{!32, !33, !34}
!33 = !{!"llvm.loop.mustprogress"}
!34 = !{!"llvm.loop.unroll.disable"}
!35 = distinct !{!35, !33, !34}
!36 = distinct !{!36, !33, !34}
!37 = !{!10, !10, i64 0}
!38 = !{!39, !41}
!39 = distinct !{!39, !40, !"fd_memcpy: argument 0"}
!40 = distinct !{!40, !"fd_memcpy"}
!41 = distinct !{!41, !40, !"fd_memcpy: argument 1"}
!42 = !{!43, !45}
!43 = distinct !{!43, !44, !"fd_memcpy: argument 0"}
!44 = distinct !{!44, !"fd_memcpy"}
!45 = distinct !{!45, !44, !"fd_memcpy: argument 1"}
