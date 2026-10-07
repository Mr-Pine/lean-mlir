define internal fastcc void @_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx28compress(ptr noalias nofree noundef nonnull align 8 captures(none) dereferenceable(64) %state, ptr noalias nofree noundef nonnull readonly captures(none) %blocks.0, i64 noundef range(i64 0, 72057594037927936) %blocks.1) unnamed_addr #2 personality ptr @rust_eh_personality {
start:
  %ms.i = alloca [128 x i8], align 16
  %t2 = alloca [640 x i8], align 16
  %ms = alloca [128 x i8], align 16
  %_4 = and i64 %blocks.1, 1
  %0 = icmp eq i64 %_4, 0
  br i1 %0, label %bb5, label %bb2

bb5:                                              ; preds = %start, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx212rounds_64_79.exit.i
  %start_block.sroa.0.0 = phi i64 [ 0, %start ], [ 1, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx212rounds_64_79.exit.i ]
  call void @llvm.lifetime.start.p0(ptr nonnull %ms)
  call void @llvm.lifetime.start.p0(ptr nonnull %t2)
  %1 = getelementptr inbounds nuw i8, ptr %t2, i64 128
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 16 dereferenceable(512) %1, i8 0, i64 512, i1 false)
  %inner_len.sroa.0.0.i.i.i = tail call i64 @llvm.usub.sat.i64(i64 range(i64 0, 72057594037927936) %blocks.1, i64 range(i64 0, 2) %start_block.sroa.0.0)
  %d9.i.i.i = lshr i64 %inner_len.sroa.0.0.i.i.i, 1
  %yield_count.sroa.0.0.i.i.i = sub nsw i64 %inner_len.sroa.0.0.i.i.i, %d9.i.i.i
  %_6.not.i.i1202 = icmp eq i64 %yield_count.sroa.0.0.i.i.i, 0
  br i1 %_6.not.i.i1202, label %bb15, label %bb14.lr.ph

bb2:                                              ; preds = %start
  tail call void @llvm.experimental.noalias.scope.decl(metadata !93)
  call void @llvm.lifetime.start.p0(ptr nonnull %ms.i), !noalias !96
  %current_state.i.sroa.0.0.copyload = load i64, ptr %state, align 8, !noalias !98
  %current_state.i.sroa.8.0.state.sroa_idx = getelementptr inbounds nuw i8, ptr %state, i64 8
  %current_state.i.sroa.8.0.copyload = load i64, ptr %current_state.i.sroa.8.0.state.sroa_idx, align 8, !noalias !98
  %current_state.i.sroa.13.0.state.sroa_idx = getelementptr inbounds nuw i8, ptr %state, i64 16
  %current_state.i.sroa.13.0.copyload = load i64, ptr %current_state.i.sroa.13.0.state.sroa_idx, align 8, !noalias !98
  %current_state.i.sroa.18.0.state.sroa_idx = getelementptr inbounds nuw i8, ptr %state, i64 24
  %current_state.i.sroa.18.0.copyload = load i64, ptr %current_state.i.sroa.18.0.state.sroa_idx, align 8, !noalias !98
  %current_state.i.sroa.23.0.state.sroa_idx = getelementptr inbounds nuw i8, ptr %state, i64 32
  %current_state.i.sroa.23.0.copyload = load i64, ptr %current_state.i.sroa.23.0.state.sroa_idx, align 8, !noalias !98
  %current_state.i.sroa.28.0.state.sroa_idx = getelementptr inbounds nuw i8, ptr %state, i64 40
  %current_state.i.sroa.28.0.copyload = load i64, ptr %current_state.i.sroa.28.0.state.sroa_idx, align 8, !noalias !98
  %current_state.i.sroa.33.0.state.sroa_idx = getelementptr inbounds nuw i8, ptr %state, i64 48
  %current_state.i.sroa.33.0.copyload = load i64, ptr %current_state.i.sroa.33.0.state.sroa_idx, align 8, !noalias !98
  %current_state.i.sroa.38.0.state.sroa_idx = getelementptr inbounds nuw i8, ptr %state, i64 56
  %current_state.i.sroa.38.0.copyload = load i64, ptr %current_state.i.sroa.38.0.state.sroa_idx, align 8, !noalias !98
  tail call void @llvm.experimental.noalias.scope.decl(metadata !99)
  %dst.sroa.0.0.copyload.i922 = load <16 x i8>, ptr %blocks.0, align 1, !noalias !102
  %_3.i = shufflevector <16 x i8> %dst.sroa.0.0.copyload.i922, <16 x i8> poison, <16 x i32> <i32 7, i32 6, i32 5, i32 4, i32 3, i32 2, i32 1, i32 0, i32 15, i32 14, i32 13, i32 12, i32 11, i32 10, i32 9, i32 8>
  %2 = bitcast <16 x i8> %_3.i to <2 x i64>
  %_3.i343 = add <2 x i64> %2, <i64 4794697086780616226, i64 8158064640168781261>
  store <2 x i64> %_3.i343, ptr %ms.i, align 16, !alias.scope !99, !noalias !106
  %_14.i.i = getelementptr inbounds nuw i8, ptr %blocks.0, i64 16
  %dst.sroa.0.0.copyload.i344923 = load <16 x i8>, ptr %_14.i.i, align 1, !noalias !107
  %_3.i345 = shufflevector <16 x i8> %dst.sroa.0.0.copyload.i344923, <16 x i8> poison, <16 x i32> <i32 7, i32 6, i32 5, i32 4, i32 3, i32 2, i32 1, i32 0, i32 15, i32 14, i32 13, i32 12, i32 11, i32 10, i32 9, i32 8>
  %3 = bitcast <16 x i8> %_3.i345 to <2 x i64>
  %_3.i346 = add <2 x i64> %3, <i64 -5349999486874862801, i64 -1606136188198331460>
  %4 = getelementptr inbounds nuw i8, ptr %ms.i, i64 16
  store <2 x i64> %_3.i346, ptr %4, align 16, !alias.scope !99, !noalias !106
  %_25.i.i = getelementptr inbounds nuw i8, ptr %blocks.0, i64 32
  %dst.sroa.0.0.copyload.i347924 = load <16 x i8>, ptr %_25.i.i, align 1, !noalias !110
  %_3.i348 = shufflevector <16 x i8> %dst.sroa.0.0.copyload.i347924, <16 x i8> poison, <16 x i32> <i32 7, i32 6, i32 5, i32 4, i32 3, i32 2, i32 1, i32 0, i32 15, i32 14, i32 13, i32 12, i32 11, i32 10, i32 9, i32 8>
  %5 = bitcast <16 x i8> %_3.i348 to <2 x i64>
  %_3.i349 = add <2 x i64> %5, <i64 4131703408338449720, i64 6480981068601479193>
  %6 = getelementptr inbounds nuw i8, ptr %ms.i, i64 32
  store <2 x i64> %_3.i349, ptr %6, align 16, !alias.scope !99, !noalias !106
  %_36.i.i = getelementptr inbounds nuw i8, ptr %blocks.0, i64 48
  %dst.sroa.0.0.copyload.i350925 = load <16 x i8>, ptr %_36.i.i, align 1, !noalias !113
  %_3.i351 = shufflevector <16 x i8> %dst.sroa.0.0.copyload.i350925, <16 x i8> poison, <16 x i32> <i32 7, i32 6, i32 5, i32 4, i32 3, i32 2, i32 1, i32 0, i32 15, i32 14, i32 13, i32 12, i32 11, i32 10, i32 9, i32 8>
  %7 = bitcast <16 x i8> %_3.i351 to <2 x i64>
  %_3.i352 = add <2 x i64> %7, <i64 -7908458776815382629, i64 -6116909921290321640>
  %8 = getelementptr inbounds nuw i8, ptr %ms.i, i64 48
  store <2 x i64> %_3.i352, ptr %8, align 16, !alias.scope !99, !noalias !106
  %_47.i.i = getelementptr inbounds nuw i8, ptr %blocks.0, i64 64
  %dst.sroa.0.0.copyload.i353926 = load <16 x i8>, ptr %_47.i.i, align 1, !noalias !116
  %_3.i354 = shufflevector <16 x i8> %dst.sroa.0.0.copyload.i353926, <16 x i8> poison, <16 x i32> <i32 7, i32 6, i32 5, i32 4, i32 3, i32 2, i32 1, i32 0, i32 15, i32 14, i32 13, i32 12, i32 11, i32 10, i32 9, i32 8>
  %9 = bitcast <16 x i8> %_3.i354 to <2 x i64>
  %_3.i355 = add <2 x i64> %9, <i64 -2880145864133508542, i64 1334009975649890238>
  %10 = getelementptr inbounds nuw i8, ptr %ms.i, i64 64
  store <2 x i64> %_3.i355, ptr %10, align 16, !alias.scope !99, !noalias !106
  %_58.i.i = getelementptr inbounds nuw i8, ptr %blocks.0, i64 80
  %dst.sroa.0.0.copyload.i356927 = load <16 x i8>, ptr %_58.i.i, align 1, !noalias !119
  %_3.i357 = shufflevector <16 x i8> %dst.sroa.0.0.copyload.i356927, <16 x i8> poison, <16 x i32> <i32 7, i32 6, i32 5, i32 4, i32 3, i32 2, i32 1, i32 0, i32 15, i32 14, i32 13, i32 12, i32 11, i32 10, i32 9, i32 8>
  %11 = bitcast <16 x i8> %_3.i357 to <2 x i64>
  %_3.i358 = add <2 x i64> %11, <i64 2608012711638119052, i64 6128411473006802146>
  %12 = getelementptr inbounds nuw i8, ptr %ms.i, i64 80
  store <2 x i64> %_3.i358, ptr %12, align 16, !alias.scope !99, !noalias !106
  %_69.i.i = getelementptr inbounds nuw i8, ptr %blocks.0, i64 96
  %dst.sroa.0.0.copyload.i359928 = load <16 x i8>, ptr %_69.i.i, align 1, !noalias !122
  %_3.i360 = shufflevector <16 x i8> %dst.sroa.0.0.copyload.i359928, <16 x i8> poison, <16 x i32> <i32 7, i32 6, i32 5, i32 4, i32 3, i32 2, i32 1, i32 0, i32 15, i32 14, i32 13, i32 12, i32 11, i32 10, i32 9, i32 8>
  %13 = bitcast <16 x i8> %_3.i360 to <2 x i64>
  %_3.i361 = add <2 x i64> %13, <i64 8268148722764581231, i64 -9160688886553864527>
  %14 = getelementptr inbounds nuw i8, ptr %ms.i, i64 96
  store <2 x i64> %_3.i361, ptr %14, align 16, !alias.scope !99, !noalias !106
  %_80.i.i = getelementptr inbounds nuw i8, ptr %blocks.0, i64 112
  %dst.sroa.0.0.copyload.i362929 = load <16 x i8>, ptr %_80.i.i, align 1, !noalias !125
  %_3.i363 = shufflevector <16 x i8> %dst.sroa.0.0.copyload.i362929, <16 x i8> poison, <16 x i32> <i32 7, i32 6, i32 5, i32 4, i32 3, i32 2, i32 1, i32 0, i32 15, i32 14, i32 13, i32 12, i32 11, i32 10, i32 9, i32 8>
  %15 = bitcast <16 x i8> %_3.i363 to <2 x i64>
  %_3.i364 = add <2 x i64> %15, <i64 -7215885187991268811, i64 -4495734319001033068>
  %16 = getelementptr inbounds nuw i8, ptr %ms.i, i64 112
  store <2 x i64> %_3.i364, ptr %16, align 16, !alias.scope !99, !noalias !106
  tail call void @llvm.experimental.noalias.scope.decl(metadata !128)
  br label %bb10.i.i

bb1.i6.i.loopexit:                                ; preds = %bb15.i.i
  %_28.0.i.i = add nuw nsw i32 %iter.sroa.0.0.i7.i1026, 1
  %exitcond1206.not = icmp eq i32 %_28.0.i.i, 4
  br i1 %exitcond1206.not, label %bb2.i.i, label %bb10.i.i

bb10.i.i:                                         ; preds = %bb2, %bb1.i6.i.loopexit
  %k64_idx.sroa.0.0.i.i1027 = phi i64 [ 16, %bb2 ], [ %31, %bb1.i6.i.loopexit ]
  %iter.sroa.0.0.i7.i1026 = phi i32 [ 0, %bb2 ], [ %_28.0.i.i, %bb1.i6.i.loopexit ]
  %_3.i367932.lcssa9801025 = phi <2 x i64> [ %3, %bb2 ], [ %_39.i373941971, %bb1.i6.i.loopexit ]
  %_3.i367932933.lcssa9821024 = phi <2 x i64> [ %2, %bb2 ], [ %_3.i367932976, %bb1.i6.i.loopexit ]
  %_5.i369935.lcssa9831023 = phi <2 x i64> [ %11, %bb2 ], [ %_43.i375945969, %bb1.i6.i.loopexit ]
  %_6.i370937.lcssa9851022 = phi <2 x i64> [ %9, %bb2 ], [ %_5.i369935974, %bb1.i6.i.loopexit ]
  %_20.i372939.lcssa9871021 = phi <2 x i64> [ %15, %bb2 ], [ %_3.i12.i, %bb1.i6.i.loopexit ]
  %_39.i373941.lcssa9891020 = phi <2 x i64> [ %5, %bb2 ], [ %_40.i374943970, %bb1.i6.i.loopexit ]
  %_40.i374943.lcssa9911019 = phi <2 x i64> [ %7, %bb2 ], [ %_6.i370937973, %bb1.i6.i.loopexit ]
  %_43.i375945.lcssa9931018 = phi <2 x i64> [ %13, %bb2 ], [ %_20.i372939972, %bb1.i6.i.loopexit ]
  %_22.i62947.lcssa9951017 = phi i64 [ %current_state.i.sroa.38.0.copyload, %bb2 ], [ %_43.i102953965, %bb1.i6.i.loopexit ]
  %_43.i64949.lcssa9971016 = phi i64 [ %current_state.i.sroa.23.0.copyload, %bb2 ], [ %_43.i64, %bb1.i6.i.loopexit ]
  %_43.i64949951.lcssa9991015 = phi i64 [ %current_state.i.sroa.33.0.copyload, %bb2 ], [ %_43.i64949967, %bb1.i6.i.loopexit ]
  %_43.i102953.lcssa10011014 = phi i64 [ %current_state.i.sroa.28.0.copyload, %bb2 ], [ %_43.i102, %bb1.i6.i.loopexit ]
  %_22.i100954.lcssa10031013 = phi i64 [ %current_state.i.sroa.0.0.copyload, %bb2 ], [ %_22.i62, %bb1.i6.i.loopexit ]
  %_22.i100956.lcssa10051012 = phi i64 [ %current_state.i.sroa.8.0.copyload, %bb2 ], [ %_22.i100, %bb1.i6.i.loopexit ]
  %_22.i100954958.lcssa10071011 = phi i64 [ %current_state.i.sroa.13.0.copyload, %bb2 ], [ %_22.i100954964, %bb1.i6.i.loopexit ]
  %_43.i64960.lcssa10091010 = phi i64 [ %current_state.i.sroa.18.0.copyload, %bb2 ], [ %_22.i100956963, %bb1.i6.i.loopexit ]
  br label %bb15.i.i

bb15.i.i:                                         ; preds = %bb10.i.i, %bb15.i.i
  %k64_idx.sroa.0.1.i.i978 = phi i64 [ %k64_idx.sroa.0.0.i.i1027, %bb10.i.i ], [ %31, %bb15.i.i ]
  %iter1.sroa.0.0.i.i977 = phi i64 [ 0, %bb10.i.i ], [ %17, %bb15.i.i ]
  %_3.i367932976 = phi <2 x i64> [ %_3.i367932.lcssa9801025, %bb10.i.i ], [ %_39.i373941971, %bb15.i.i ]
  %_3.i367932933975 = phi <2 x i64> [ %_3.i367932933.lcssa9821024, %bb10.i.i ], [ %_3.i367932976, %bb15.i.i ]
  %_5.i369935974 = phi <2 x i64> [ %_5.i369935.lcssa9831023, %bb10.i.i ], [ %_43.i375945969, %bb15.i.i ]
  %_6.i370937973 = phi <2 x i64> [ %_6.i370937.lcssa9851022, %bb10.i.i ], [ %_5.i369935974, %bb15.i.i ]
  %_20.i372939972 = phi <2 x i64> [ %_20.i372939.lcssa9871021, %bb10.i.i ], [ %_3.i12.i, %bb15.i.i ]
  %_39.i373941971 = phi <2 x i64> [ %_39.i373941.lcssa9891020, %bb10.i.i ], [ %_40.i374943970, %bb15.i.i ]
  %_40.i374943970 = phi <2 x i64> [ %_40.i374943.lcssa9911019, %bb10.i.i ], [ %_6.i370937973, %bb15.i.i ]
  %_43.i375945969 = phi <2 x i64> [ %_43.i375945.lcssa9931018, %bb10.i.i ], [ %_20.i372939972, %bb15.i.i ]
  %_22.i62947968 = phi i64 [ %_22.i62947.lcssa9951017, %bb10.i.i ], [ %_43.i102953965, %bb15.i.i ]
  %_43.i64949967 = phi i64 [ %_43.i64949.lcssa9971016, %bb10.i.i ], [ %_43.i64, %bb15.i.i ]
  %_43.i64949951966 = phi i64 [ %_43.i64949951.lcssa9991015, %bb10.i.i ], [ %_43.i64949967, %bb15.i.i ]
  %_43.i102953965 = phi i64 [ %_43.i102953.lcssa10011014, %bb10.i.i ], [ %_43.i102, %bb15.i.i ]
  %_22.i100954964 = phi i64 [ %_22.i100954.lcssa10031013, %bb10.i.i ], [ %_22.i62, %bb15.i.i ]
  %_22.i100956963 = phi i64 [ %_22.i100956.lcssa10051012, %bb10.i.i ], [ %_22.i100, %bb15.i.i ]
  %_22.i100954958962 = phi i64 [ %_22.i100954958.lcssa10071011, %bb10.i.i ], [ %_22.i100954964, %bb15.i.i ]
  %_43.i64960961 = phi i64 [ %_43.i64960.lcssa10091010, %bb10.i.i ], [ %_22.i100956963, %bb15.i.i ]
  %17 = add nuw nsw i64 %iter1.sroa.0.0.i.i977, 1
  %_9.i.i = getelementptr inbounds nuw i64, ptr @alloc_448aca044373cb4cde6849f95106f1ce, i64 %k64_idx.sroa.0.1.i.i978
  %dst.sroa.0.0.copyload.i365 = load <2 x i64>, ptr %_9.i.i, align 8, !noalias !131
  %18 = shufflevector <2 x i64> %_3.i367932933975, <2 x i64> %_3.i367932976, <2 x i32> <i32 1, i32 2>
  %19 = shufflevector <2 x i64> %_6.i370937973, <2 x i64> %_5.i369935974, <2 x i32> <i32 1, i32 2>
  %_3.i.i = lshr <2 x i64> %18, splat (i64 1)
  %_3.i1.i = add <2 x i64> %_3.i367932933975, %19
  %_3.i2.i = lshr <2 x i64> %18, splat (i64 7)
  %_3.i3.i = shl <2 x i64> %18, splat (i64 56)
  %_3.i4.i = lshr <2 x i64> %18, splat (i64 8)
  %20 = xor <2 x i64> %_3.i.i, %_3.i3.i
  %_3.i5.i = shl <2 x i64> %18, splat (i64 63)
  %21 = xor <2 x i64> %20, %_3.i4.i
  %22 = xor <2 x i64> %21, %_3.i5.i
  %23 = xor <2 x i64> %22, %_3.i2.i
  %_3.i6.i = lshr <2 x i64> %_20.i372939972, splat (i64 6)
  %_3.i7.i = shl <2 x i64> %_20.i372939972, splat (i64 3)
  %_3.i8.i = add <2 x i64> %_3.i1.i, %23
  %_3.i9.i = lshr <2 x i64> %_20.i372939972, splat (i64 19)
  %_3.i10.i = shl <2 x i64> %_20.i372939972, splat (i64 45)
  %24 = xor <2 x i64> %_3.i7.i, %_3.i9.i
  %_3.i11.i = lshr <2 x i64> %_20.i372939972, splat (i64 61)
  %25 = xor <2 x i64> %24, %_3.i10.i
  %26 = xor <2 x i64> %25, %_3.i11.i
  %27 = xor <2 x i64> %26, %_3.i6.i
  %_3.i12.i = add <2 x i64> %_3.i8.i, %27
  %_3.i13.i = add <2 x i64> %_3.i12.i, %dst.sroa.0.0.copyload.i365
  %.idx = shl nuw nsw i64 %iter1.sroa.0.0.i.i977, 4
  %28 = getelementptr inbounds nuw i8, ptr %ms.i, i64 %.idx
  %_16.i.i = load i64, ptr %28, align 16, !alias.scope !128, !noalias !134, !noundef !137
  %_5.i71 = add i64 %_22.i62947968, %_16.i.i
  %_0.i376 = tail call i64 @llvm.fshl.i64(i64 %_43.i64949967, i64 %_43.i64949967, i64 50)
  %_0.i377 = tail call i64 @llvm.fshl.i64(i64 %_43.i64949967, i64 %_43.i64949967, i64 46)
  %_8.i75 = xor i64 %_0.i376, %_0.i377
  %_0.i378 = tail call i64 @llvm.fshl.i64(i64 %_43.i64949967, i64 %_43.i64949967, i64 23)
  %_7.i77 = xor i64 %_8.i75, %_0.i378
  %_4.i78 = add i64 %_5.i71, %_7.i77
  %_19.i82 = xor i64 %_43.i102953965, %_43.i64949951966
  %_17.i83 = and i64 %_19.i82, %_43.i64949967
  %_15.i84 = xor i64 %_17.i83, %_43.i64949951966
  %t.i85 = add i64 %_4.i78, %_15.i84
  %_0.i379 = tail call i64 @llvm.fshl.i64(i64 %_22.i100954964, i64 %_22.i100954964, i64 36)
  %_0.i380 = tail call i64 @llvm.fshl.i64(i64 %_22.i100954964, i64 %_22.i100954964, i64 30)
  %_25.i89 = xor i64 %_0.i379, %_0.i380
  %_0.i381 = tail call i64 @llvm.fshl.i64(i64 %_22.i100954964, i64 %_22.i100954964, i64 25)
  %_24.i91 = xor i64 %_25.i89, %_0.i381
  %_23.i92 = add i64 %t.i85, %_24.i91
  %_371.i96 = xor i64 %_22.i100954958962, %_22.i100956963
  %_33.i97 = and i64 %_371.i96, %_22.i100954964
  %_40.i98 = and i64 %_22.i100954958962, %_22.i100956963
  %_32.i99 = xor i64 %_33.i97, %_40.i98
  %_22.i100 = add i64 %_23.i92, %_32.i99
  %_43.i102 = add i64 %_43.i64960961, %t.i85
  %29 = getelementptr inbounds nuw i8, ptr %28, i64 8
  %_20.i.i = load i64, ptr %29, align 8, !alias.scope !128, !noalias !134, !noundef !137
  %_0.i382 = tail call i64 @llvm.fshl.i64(i64 %_43.i102, i64 %_43.i102, i64 50)
  %_0.i383 = tail call i64 @llvm.fshl.i64(i64 %_43.i102, i64 %_43.i102, i64 46)
  %_8.i47 = xor i64 %_0.i382, %_0.i383
  %_0.i384 = tail call i64 @llvm.fshl.i64(i64 %_43.i102, i64 %_43.i102, i64 23)
  %_7.i49 = xor i64 %_8.i47, %_0.i384
  %_19.i = xor i64 %_43.i102953965, %_43.i64949967
  %_17.i52 = and i64 %_43.i102, %_19.i
  %_15.i = xor i64 %_17.i52, %_43.i102953965
  %_5.i44 = add i64 %_15.i, %_43.i64949951966
  %_4.i50 = add i64 %_5.i44, %_7.i49
  %t.i53 = add i64 %_4.i50, %_20.i.i
  %_0.i385 = tail call i64 @llvm.fshl.i64(i64 %_22.i100, i64 %_22.i100, i64 36)
  %_0.i386 = tail call i64 @llvm.fshl.i64(i64 %_22.i100, i64 %_22.i100, i64 30)
  %_25.i56 = xor i64 %_0.i385, %_0.i386
  %_0.i387 = tail call i64 @llvm.fshl.i64(i64 %_22.i100, i64 %_22.i100, i64 25)
  %_24.i58 = xor i64 %_25.i56, %_0.i387
  %_371.i = xor i64 %_22.i100956963, %_22.i100954964
  %_33.i60 = and i64 %_22.i100, %_371.i
  %_40.i61 = and i64 %_22.i100956963, %_22.i100954964
  %_32.i = xor i64 %_33.i60, %_40.i61
  %_23.i59 = add i64 %_24.i58, %_32.i
  %_22.i62 = add i64 %_23.i59, %t.i53
  %_43.i64 = add i64 %t.i53, %_22.i100954958962
  %30 = getelementptr inbounds nuw <2 x i64>, ptr %ms.i, i64 %iter1.sroa.0.0.i.i977
  store <2 x i64> %_3.i13.i, ptr %30, align 16, !alias.scope !128, !noalias !134
  %31 = add i64 %k64_idx.sroa.0.1.i.i978, 2
  %exitcond.not = icmp eq i64 %17, 8
  br i1 %exitcond.not, label %bb1.i6.i.loopexit, label %bb15.i.i

bb2.i.i:                                          ; preds = %bb1.i6.i.loopexit, %bb2.i.i
  %iter.sroa.0.0.i.i1051 = phi i64 [ %32, %bb2.i.i ], [ 64, %bb1.i6.i.loopexit ]
  %_16.i11910291050 = phi i64 [ %_20.i12110331048, %bb2.i.i ], [ %_43.i102953965, %bb1.i6.i.loopexit ]
  %_43.i14210311049 = phi i64 [ %_43.i142, %bb2.i.i ], [ %_43.i64, %bb1.i6.i.loopexit ]
  %_20.i12110331048 = phi i64 [ %_43.i142103110351047, %bb2.i.i ], [ %_43.i64949967, %bb1.i6.i.loopexit ]
  %_43.i142103110351047 = phi i64 [ %_43.i14210311049, %bb2.i.i ], [ %_43.i102, %bb1.i6.i.loopexit ]
  %_22.i14010361046 = phi i64 [ %_22.i140, %bb2.i.i ], [ %_22.i62, %bb1.i6.i.loopexit ]
  %_22.i140103610381045 = phi i64 [ %_22.i14010361046, %bb2.i.i ], [ %_22.i100, %bb1.i6.i.loopexit ]
  %_22.i1401036103810401044 = phi i64 [ %_22.i140103610381045, %bb2.i.i ], [ %_22.i100954964, %bb1.i6.i.loopexit ]
  %_22.i14010361038104010421043 = phi i64 [ %_22.i1401036103810401044, %bb2.i.i ], [ %_22.i100956963, %bb1.i6.i.loopexit ]
  %_7.i.i = and i64 %iter.sroa.0.0.i.i1051, 15
  %32 = add nuw nsw i64 %iter.sroa.0.0.i.i1051, 1
  %33 = getelementptr inbounds nuw i64, ptr %ms.i, i64 %_7.i.i
  %_6.i.i = load i64, ptr %33, align 8, !alias.scope !138, !noalias !141, !noundef !137
  %_0.i388 = tail call i64 @llvm.fshl.i64(i64 %_43.i14210311049, i64 %_43.i14210311049, i64 50)
  %_0.i389 = tail call i64 @llvm.fshl.i64(i64 %_43.i14210311049, i64 %_43.i14210311049, i64 46)
  %_8.i115 = xor i64 %_0.i388, %_0.i389
  %_0.i390 = tail call i64 @llvm.fshl.i64(i64 %_43.i14210311049, i64 %_43.i14210311049, i64 23)
  %_19.i122 = xor i64 %_43.i142103110351047, %_20.i12110331048
  %_0.i391 = tail call i64 @llvm.fshl.i64(i64 %_22.i14010361046, i64 %_22.i14010361046, i64 36)
  %_0.i392 = tail call i64 @llvm.fshl.i64(i64 %_22.i14010361046, i64 %_22.i14010361046, i64 30)
  %_25.i129 = xor i64 %_0.i391, %_0.i392
  %_0.i393 = tail call i64 @llvm.fshl.i64(i64 %_22.i14010361046, i64 %_22.i14010361046, i64 25)
  %_24.i131 = xor i64 %_25.i129, %_0.i393
  %_371.i136 = xor i64 %_22.i1401036103810401044, %_22.i140103610381045
  %_33.i137 = and i64 %_371.i136, %_22.i14010361046
  %_40.i138 = and i64 %_22.i1401036103810401044, %_22.i140103610381045
  %_32.i139 = xor i64 %_33.i137, %_40.i138
  %_5.i111 = add i64 %_16.i11910291050, %_6.i.i
  %_7.i117 = xor i64 %_8.i115, %_0.i390
  %_4.i118 = add i64 %_5.i111, %_7.i117
  %_17.i123 = and i64 %_19.i122, %_43.i14210311049
  %_15.i124 = xor i64 %_17.i123, %_20.i12110331048
  %t.i125 = add i64 %_4.i118, %_15.i124
  %_23.i132 = add i64 %t.i125, %_24.i131
  %_22.i140 = add i64 %_23.i132, %_32.i139
  %_43.i142 = add i64 %_22.i14010361038104010421043, %t.i125
  %exitcond1207.not = icmp eq i64 %32, 80
  br i1 %exitcond1207.not, label %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx212rounds_64_79.exit.i, label %bb2.i.i

_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx212rounds_64_79.exit.i: ; preds = %bb2.i.i
  %34 = load <4 x i64>, ptr %state, align 8, !alias.scope !143, !noalias !146
  %35 = insertelement <4 x i64> poison, i64 %_22.i140, i64 0
  %36 = insertelement <4 x i64> %35, i64 %_22.i14010361046, i64 1
  %37 = insertelement <4 x i64> %36, i64 %_22.i140103610381045, i64 2
  %38 = insertelement <4 x i64> %37, i64 %_22.i1401036103810401044, i64 3
  %39 = add <4 x i64> %38, %34
  store <4 x i64> %39, ptr %state, align 8, !alias.scope !143, !noalias !146
  %40 = load <4 x i64>, ptr %current_state.i.sroa.23.0.state.sroa_idx, align 8, !alias.scope !143, !noalias !146
  %41 = insertelement <4 x i64> poison, i64 %_43.i142, i64 0
  %42 = insertelement <4 x i64> %41, i64 %_43.i14210311049, i64 1
  %43 = insertelement <4 x i64> %42, i64 %_43.i142103110351047, i64 2
  %44 = insertelement <4 x i64> %43, i64 %_20.i12110331048, i64 3
  %45 = add <4 x i64> %44, %40
  store <4 x i64> %45, ptr %current_state.i.sroa.23.0.state.sroa_idx, align 8, !alias.scope !143, !noalias !146
  call void @llvm.lifetime.end.p0(ptr nonnull %ms.i), !noalias !96
  br label %bb5

bb14.lr.ph:                                       ; preds = %bb5
  %46 = getelementptr inbounds nuw i8, ptr %ms, i64 16
  %47 = getelementptr inbounds nuw i8, ptr %t2, i64 16
  %48 = getelementptr inbounds nuw i8, ptr %ms, i64 32
  %49 = getelementptr inbounds nuw i8, ptr %t2, i64 32
  %50 = getelementptr inbounds nuw i8, ptr %ms, i64 48
  %51 = getelementptr inbounds nuw i8, ptr %t2, i64 48
  %52 = getelementptr inbounds nuw i8, ptr %ms, i64 64
  %53 = getelementptr inbounds nuw i8, ptr %t2, i64 64
  %54 = getelementptr inbounds nuw i8, ptr %ms, i64 80
  %55 = getelementptr inbounds nuw i8, ptr %t2, i64 80
  %56 = getelementptr inbounds nuw i8, ptr %ms, i64 96
  %57 = getelementptr inbounds nuw i8, ptr %t2, i64 96
  %58 = getelementptr inbounds nuw i8, ptr %ms, i64 112
  %59 = getelementptr inbounds nuw i8, ptr %t2, i64 112
  %current_state.sroa.12.0.state.sroa_idx = getelementptr inbounds nuw i8, ptr %state, i64 8
  %current_state.sroa.20.0.state.sroa_idx = getelementptr inbounds nuw i8, ptr %state, i64 16
  %current_state.sroa.28.0.state.sroa_idx = getelementptr inbounds nuw i8, ptr %state, i64 24
  %current_state.sroa.36.0.state.sroa_idx = getelementptr inbounds nuw i8, ptr %state, i64 32
  %current_state.sroa.44.0.state.sroa_idx = getelementptr inbounds nuw i8, ptr %state, i64 40
  %current_state.sroa.52.0.state.sroa_idx = getelementptr inbounds nuw i8, ptr %state, i64 48
  %current_state.sroa.60.0.state.sroa_idx = getelementptr inbounds nuw i8, ptr %state, i64 56
  %state.promoted = load i64, ptr %state, align 8
  %current_state.sroa.12.0.state.sroa_idx.promoted = load i64, ptr %current_state.sroa.12.0.state.sroa_idx, align 8
  %current_state.sroa.20.0.state.sroa_idx.promoted = load i64, ptr %current_state.sroa.20.0.state.sroa_idx, align 8
  %current_state.sroa.28.0.state.sroa_idx.promoted = load i64, ptr %current_state.sroa.28.0.state.sroa_idx, align 8
  %current_state.sroa.36.0.state.sroa_idx.promoted = load i64, ptr %current_state.sroa.36.0.state.sroa_idx, align 8
  %current_state.sroa.44.0.state.sroa_idx.promoted = load i64, ptr %current_state.sroa.44.0.state.sroa_idx, align 8
  %current_state.sroa.52.0.state.sroa_idx.promoted = load i64, ptr %current_state.sroa.52.0.state.sroa_idx, align 8
  %current_state.sroa.60.0.state.sroa_idx.promoted = load i64, ptr %current_state.sroa.60.0.state.sroa_idx, align 8
  br label %bb14

bb14:                                             ; preds = %bb14.lr.ph, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx220process_second_block.exit
  %_5.i.71261 = phi i64 [ %current_state.sroa.60.0.state.sroa_idx.promoted, %bb14.lr.ph ], [ %_5.i.7, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx220process_second_block.exit ]
  %_5.i.61260 = phi i64 [ %current_state.sroa.52.0.state.sroa_idx.promoted, %bb14.lr.ph ], [ %_5.i.6, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx220process_second_block.exit ]
  %_5.i.51259 = phi i64 [ %current_state.sroa.44.0.state.sroa_idx.promoted, %bb14.lr.ph ], [ %_5.i.5, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx220process_second_block.exit ]
  %_5.i.41258 = phi i64 [ %current_state.sroa.36.0.state.sroa_idx.promoted, %bb14.lr.ph ], [ %_5.i.4, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx220process_second_block.exit ]
  %_5.i.31257 = phi i64 [ %current_state.sroa.28.0.state.sroa_idx.promoted, %bb14.lr.ph ], [ %_5.i.3, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx220process_second_block.exit ]
  %_5.i.21256 = phi i64 [ %current_state.sroa.20.0.state.sroa_idx.promoted, %bb14.lr.ph ], [ %_5.i.2, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx220process_second_block.exit ]
  %_5.i.11255 = phi i64 [ %current_state.sroa.12.0.state.sroa_idx.promoted, %bb14.lr.ph ], [ %_5.i.1, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx220process_second_block.exit ]
  %current_state.sroa.0.0.copyload1254 = phi i64 [ %state.promoted, %bb14.lr.ph ], [ %_5.i, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx220process_second_block.exit ]
  %iter.sroa.0.01204 = phi i64 [ %start_block.sroa.0.0, %bb14.lr.ph ], [ %_8.i.i396, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx220process_second_block.exit ]
  %iter.sroa.5.01203 = phi i64 [ %yield_count.sroa.0.0.i.i.i, %bb14.lr.ph ], [ %89, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx220process_second_block.exit ]
  %_0.i = getelementptr inbounds nuw [128 x i8], ptr %blocks.0, i64 %iter.sroa.0.01204
  tail call void @llvm.experimental.noalias.scope.decl(metadata !148)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !151)
  %_9.i = getelementptr inbounds nuw i8, ptr %_0.i, i64 128
  %dst.sroa.0.0.copyload.i397 = load <2 x i64>, ptr %_9.i, align 1, !noalias !153
  %dst.sroa.0.0.copyload.i398 = load <2 x i64>, ptr %_0.i, align 1, !noalias !157
  %dst2.i400 = shufflevector <2 x i64> %dst.sroa.0.0.copyload.i398, <2 x i64> %dst.sroa.0.0.copyload.i397, <4 x i32> <i32 0, i32 1, i32 2, i32 3>
  %60 = bitcast <4 x i64> %dst2.i400 to <32 x i8>
  %_3.i401 = shufflevector <32 x i8> %60, <32 x i8> poison, <32 x i32> <i32 7, i32 6, i32 5, i32 4, i32 3, i32 2, i32 1, i32 0, i32 15, i32 14, i32 13, i32 12, i32 11, i32 10, i32 9, i32 8, i32 23, i32 22, i32 21, i32 20, i32 19, i32 18, i32 17, i32 16, i32 31, i32 30, i32 29, i32 28, i32 27, i32 26, i32 25, i32 24>
  %61 = bitcast <32 x i8> %_3.i401 to <4 x i64>
  %_3.i403 = add <4 x i64> %61, <i64 4794697086780616226, i64 8158064640168781261, i64 4794697086780616226, i64 8158064640168781261>
  %dst.i404 = shufflevector <4 x i64> %_3.i403, <4 x i64> poison, <2 x i32> <i32 0, i32 1>
  store <2 x i64> %dst.i404, ptr %ms, align 16, !alias.scope !148, !noalias !160
  %dst.i405 = shufflevector <4 x i64> %_3.i403, <4 x i64> poison, <2 x i32> <i32 2, i32 3>
  store <2 x i64> %dst.i405, ptr %t2, align 16, !alias.scope !151, !noalias !161
  %_26.i = getelementptr inbounds nuw i8, ptr %_0.i, i64 144
  %dst.sroa.0.0.copyload.i406 = load <2 x i64>, ptr %_26.i, align 1, !noalias !162
  %_30.i = getelementptr inbounds nuw i8, ptr %_0.i, i64 16
  %dst.sroa.0.0.copyload.i409 = load <2 x i64>, ptr %_30.i, align 1, !noalias !165
  %dst2.i411 = shufflevector <2 x i64> %dst.sroa.0.0.copyload.i409, <2 x i64> %dst.sroa.0.0.copyload.i406, <4 x i32> <i32 0, i32 1, i32 2, i32 3>
  %62 = bitcast <4 x i64> %dst2.i411 to <32 x i8>
  %_3.i412 = shufflevector <32 x i8> %62, <32 x i8> poison, <32 x i32> <i32 7, i32 6, i32 5, i32 4, i32 3, i32 2, i32 1, i32 0, i32 15, i32 14, i32 13, i32 12, i32 11, i32 10, i32 9, i32 8, i32 23, i32 22, i32 21, i32 20, i32 19, i32 18, i32 17, i32 16, i32 31, i32 30, i32 29, i32 28, i32 27, i32 26, i32 25, i32 24>
  %63 = bitcast <32 x i8> %_3.i412 to <4 x i64>
  %_3.i414 = add <4 x i64> %63, <i64 -5349999486874862801, i64 -1606136188198331460, i64 -5349999486874862801, i64 -1606136188198331460>
  %dst.i415 = shufflevector <4 x i64> %_3.i414, <4 x i64> poison, <2 x i32> <i32 0, i32 1>
  store <2 x i64> %dst.i415, ptr %46, align 16, !alias.scope !148, !noalias !160
  %dst.i416 = shufflevector <4 x i64> %_3.i414, <4 x i64> poison, <2 x i32> <i32 2, i32 3>
  store <2 x i64> %dst.i416, ptr %47, align 16, !alias.scope !151, !noalias !161
  %_46.i = getelementptr inbounds nuw i8, ptr %_0.i, i64 160
  %dst.sroa.0.0.copyload.i417 = load <2 x i64>, ptr %_46.i, align 1, !noalias !168
  %_50.i = getelementptr inbounds nuw i8, ptr %_0.i, i64 32
  %dst.sroa.0.0.copyload.i420 = load <2 x i64>, ptr %_50.i, align 1, !noalias !171
  %dst2.i422 = shufflevector <2 x i64> %dst.sroa.0.0.copyload.i420, <2 x i64> %dst.sroa.0.0.copyload.i417, <4 x i32> <i32 0, i32 1, i32 2, i32 3>
  %64 = bitcast <4 x i64> %dst2.i422 to <32 x i8>
  %_3.i423 = shufflevector <32 x i8> %64, <32 x i8> poison, <32 x i32> <i32 7, i32 6, i32 5, i32 4, i32 3, i32 2, i32 1, i32 0, i32 15, i32 14, i32 13, i32 12, i32 11, i32 10, i32 9, i32 8, i32 23, i32 22, i32 21, i32 20, i32 19, i32 18, i32 17, i32 16, i32 31, i32 30, i32 29, i32 28, i32 27, i32 26, i32 25, i32 24>
  %65 = bitcast <32 x i8> %_3.i423 to <4 x i64>
  %_3.i425 = add <4 x i64> %65, <i64 4131703408338449720, i64 6480981068601479193, i64 4131703408338449720, i64 6480981068601479193>
  %dst.i426 = shufflevector <4 x i64> %_3.i425, <4 x i64> poison, <2 x i32> <i32 0, i32 1>
  store <2 x i64> %dst.i426, ptr %48, align 16, !alias.scope !148, !noalias !160
  %dst.i427 = shufflevector <4 x i64> %_3.i425, <4 x i64> poison, <2 x i32> <i32 2, i32 3>
  store <2 x i64> %dst.i427, ptr %49, align 16, !alias.scope !151, !noalias !161
  %_66.i = getelementptr inbounds nuw i8, ptr %_0.i, i64 176
  %dst.sroa.0.0.copyload.i428 = load <2 x i64>, ptr %_66.i, align 1, !noalias !174
  %_70.i = getelementptr inbounds nuw i8, ptr %_0.i, i64 48
  %dst.sroa.0.0.copyload.i431 = load <2 x i64>, ptr %_70.i, align 1, !noalias !177
  %dst2.i433 = shufflevector <2 x i64> %dst.sroa.0.0.copyload.i431, <2 x i64> %dst.sroa.0.0.copyload.i428, <4 x i32> <i32 0, i32 1, i32 2, i32 3>
  %66 = bitcast <4 x i64> %dst2.i433 to <32 x i8>
  %_3.i434 = shufflevector <32 x i8> %66, <32 x i8> poison, <32 x i32> <i32 7, i32 6, i32 5, i32 4, i32 3, i32 2, i32 1, i32 0, i32 15, i32 14, i32 13, i32 12, i32 11, i32 10, i32 9, i32 8, i32 23, i32 22, i32 21, i32 20, i32 19, i32 18, i32 17, i32 16, i32 31, i32 30, i32 29, i32 28, i32 27, i32 26, i32 25, i32 24>
  %67 = bitcast <32 x i8> %_3.i434 to <4 x i64>
  %_3.i436 = add <4 x i64> %67, <i64 -7908458776815382629, i64 -6116909921290321640, i64 -7908458776815382629, i64 -6116909921290321640>
  %dst.i437 = shufflevector <4 x i64> %_3.i436, <4 x i64> poison, <2 x i32> <i32 0, i32 1>
  store <2 x i64> %dst.i437, ptr %50, align 16, !alias.scope !148, !noalias !160
  %dst.i438 = shufflevector <4 x i64> %_3.i436, <4 x i64> poison, <2 x i32> <i32 2, i32 3>
  store <2 x i64> %dst.i438, ptr %51, align 16, !alias.scope !151, !noalias !161
  %_86.i = getelementptr inbounds nuw i8, ptr %_0.i, i64 192
  %dst.sroa.0.0.copyload.i439 = load <2 x i64>, ptr %_86.i, align 1, !noalias !180
  %_90.i = getelementptr inbounds nuw i8, ptr %_0.i, i64 64
  %dst.sroa.0.0.copyload.i442 = load <2 x i64>, ptr %_90.i, align 1, !noalias !183
  %dst2.i444 = shufflevector <2 x i64> %dst.sroa.0.0.copyload.i442, <2 x i64> %dst.sroa.0.0.copyload.i439, <4 x i32> <i32 0, i32 1, i32 2, i32 3>
  %68 = bitcast <4 x i64> %dst2.i444 to <32 x i8>
  %_3.i445 = shufflevector <32 x i8> %68, <32 x i8> poison, <32 x i32> <i32 7, i32 6, i32 5, i32 4, i32 3, i32 2, i32 1, i32 0, i32 15, i32 14, i32 13, i32 12, i32 11, i32 10, i32 9, i32 8, i32 23, i32 22, i32 21, i32 20, i32 19, i32 18, i32 17, i32 16, i32 31, i32 30, i32 29, i32 28, i32 27, i32 26, i32 25, i32 24>
  %69 = bitcast <32 x i8> %_3.i445 to <4 x i64>
  %_3.i447 = add <4 x i64> %69, <i64 -2880145864133508542, i64 1334009975649890238, i64 -2880145864133508542, i64 1334009975649890238>
  %dst.i448 = shufflevector <4 x i64> %_3.i447, <4 x i64> poison, <2 x i32> <i32 0, i32 1>
  store <2 x i64> %dst.i448, ptr %52, align 16, !alias.scope !148, !noalias !160
  %dst.i449 = shufflevector <4 x i64> %_3.i447, <4 x i64> poison, <2 x i32> <i32 2, i32 3>
  store <2 x i64> %dst.i449, ptr %53, align 16, !alias.scope !151, !noalias !161
  %_106.i = getelementptr inbounds nuw i8, ptr %_0.i, i64 208
  %dst.sroa.0.0.copyload.i450 = load <2 x i64>, ptr %_106.i, align 1, !noalias !186
  %_110.i = getelementptr inbounds nuw i8, ptr %_0.i, i64 80
  %dst.sroa.0.0.copyload.i453 = load <2 x i64>, ptr %_110.i, align 1, !noalias !189
  %dst2.i455 = shufflevector <2 x i64> %dst.sroa.0.0.copyload.i453, <2 x i64> %dst.sroa.0.0.copyload.i450, <4 x i32> <i32 0, i32 1, i32 2, i32 3>
  %70 = bitcast <4 x i64> %dst2.i455 to <32 x i8>
  %_3.i456 = shufflevector <32 x i8> %70, <32 x i8> poison, <32 x i32> <i32 7, i32 6, i32 5, i32 4, i32 3, i32 2, i32 1, i32 0, i32 15, i32 14, i32 13, i32 12, i32 11, i32 10, i32 9, i32 8, i32 23, i32 22, i32 21, i32 20, i32 19, i32 18, i32 17, i32 16, i32 31, i32 30, i32 29, i32 28, i32 27, i32 26, i32 25, i32 24>
  %71 = bitcast <32 x i8> %_3.i456 to <4 x i64>
  %_3.i458 = add <4 x i64> %71, <i64 2608012711638119052, i64 6128411473006802146, i64 2608012711638119052, i64 6128411473006802146>
  %dst.i459 = shufflevector <4 x i64> %_3.i458, <4 x i64> poison, <2 x i32> <i32 0, i32 1>
  store <2 x i64> %dst.i459, ptr %54, align 16, !alias.scope !148, !noalias !160
  %dst.i460 = shufflevector <4 x i64> %_3.i458, <4 x i64> poison, <2 x i32> <i32 2, i32 3>
  store <2 x i64> %dst.i460, ptr %55, align 16, !alias.scope !151, !noalias !161
  %_126.i = getelementptr inbounds nuw i8, ptr %_0.i, i64 224
  %dst.sroa.0.0.copyload.i461 = load <2 x i64>, ptr %_126.i, align 1, !noalias !192
  %_130.i = getelementptr inbounds nuw i8, ptr %_0.i, i64 96
  %dst.sroa.0.0.copyload.i464 = load <2 x i64>, ptr %_130.i, align 1, !noalias !195
  %dst2.i466 = shufflevector <2 x i64> %dst.sroa.0.0.copyload.i464, <2 x i64> %dst.sroa.0.0.copyload.i461, <4 x i32> <i32 0, i32 1, i32 2, i32 3>
  %72 = bitcast <4 x i64> %dst2.i466 to <32 x i8>
  %_3.i467 = shufflevector <32 x i8> %72, <32 x i8> poison, <32 x i32> <i32 7, i32 6, i32 5, i32 4, i32 3, i32 2, i32 1, i32 0, i32 15, i32 14, i32 13, i32 12, i32 11, i32 10, i32 9, i32 8, i32 23, i32 22, i32 21, i32 20, i32 19, i32 18, i32 17, i32 16, i32 31, i32 30, i32 29, i32 28, i32 27, i32 26, i32 25, i32 24>
  %73 = bitcast <32 x i8> %_3.i467 to <4 x i64>
  %_3.i469 = add <4 x i64> %73, <i64 8268148722764581231, i64 -9160688886553864527, i64 8268148722764581231, i64 -9160688886553864527>
  %dst.i470 = shufflevector <4 x i64> %_3.i469, <4 x i64> poison, <2 x i32> <i32 0, i32 1>
  store <2 x i64> %dst.i470, ptr %56, align 16, !alias.scope !148, !noalias !160
  %dst.i471 = shufflevector <4 x i64> %_3.i469, <4 x i64> poison, <2 x i32> <i32 2, i32 3>
  store <2 x i64> %dst.i471, ptr %57, align 16, !alias.scope !151, !noalias !161
  %_146.i = getelementptr inbounds nuw i8, ptr %_0.i, i64 240
  %dst.sroa.0.0.copyload.i472 = load <2 x i64>, ptr %_146.i, align 1, !noalias !198
  %_150.i = getelementptr inbounds nuw i8, ptr %_0.i, i64 112
  %dst.sroa.0.0.copyload.i475 = load <2 x i64>, ptr %_150.i, align 1, !noalias !201
  %dst2.i477 = shufflevector <2 x i64> %dst.sroa.0.0.copyload.i475, <2 x i64> %dst.sroa.0.0.copyload.i472, <4 x i32> <i32 0, i32 1, i32 2, i32 3>
  %74 = bitcast <4 x i64> %dst2.i477 to <32 x i8>
  %_3.i478 = shufflevector <32 x i8> %74, <32 x i8> poison, <32 x i32> <i32 7, i32 6, i32 5, i32 4, i32 3, i32 2, i32 1, i32 0, i32 15, i32 14, i32 13, i32 12, i32 11, i32 10, i32 9, i32 8, i32 23, i32 22, i32 21, i32 20, i32 19, i32 18, i32 17, i32 16, i32 31, i32 30, i32 29, i32 28, i32 27, i32 26, i32 25, i32 24>
  %75 = bitcast <32 x i8> %_3.i478 to <4 x i64>
  %_3.i480 = add <4 x i64> %75, <i64 -7215885187991268811, i64 -4495734319001033068, i64 -7215885187991268811, i64 -4495734319001033068>
  %dst.i481 = shufflevector <4 x i64> %_3.i480, <4 x i64> poison, <2 x i32> <i32 0, i32 1>
  store <2 x i64> %dst.i481, ptr %58, align 16, !alias.scope !148, !noalias !160
  %dst.i482 = shufflevector <4 x i64> %_3.i480, <4 x i64> poison, <2 x i32> <i32 2, i32 3>
  store <2 x i64> %dst.i482, ptr %59, align 16, !alias.scope !151, !noalias !161
  tail call void @llvm.experimental.noalias.scope.decl(metadata !204)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !207)
  br label %bb14.i

bb1.i28.loopexit:                                 ; preds = %bb16.i
  %76 = add nuw nsw i64 %iter.sroa.0.0.i291149, 1
  %exitcond1210.not = icmp eq i64 %76, 5
  br i1 %exitcond1210.not, label %bb2.i, label %bb14.i

bb14.i:                                           ; preds = %bb14, %bb1.i28.loopexit
  %k64x4_idx.sroa.0.0.i1150 = phi i64 [ 16, %bb14 ], [ %86, %bb1.i28.loopexit ]
  %iter.sroa.0.0.i291149 = phi i64 [ 1, %bb14 ], [ %76, %bb1.i28.loopexit ]
  %_3.i4881054.lcssa11021148 = phi <4 x i64> [ %63, %bb14 ], [ %_39.i50910631093, %bb1.i28.loopexit ]
  %_3.i48810541055.lcssa11041147 = phi <4 x i64> [ %61, %bb14 ], [ %_3.i48810541098, %bb1.i28.loopexit ]
  %_5.i4901057.lcssa11061146 = phi <4 x i64> [ %71, %bb14 ], [ %_43.i51310671091, %bb1.i28.loopexit ]
  %_6.i4911059.lcssa11081145 = phi <4 x i64> [ %69, %bb14 ], [ %_5.i49010571096, %bb1.i28.loopexit ]
  %_20.i5001061.lcssa11101144 = phi <4 x i64> [ %75, %bb14 ], [ %_3.i542, %bb1.i28.loopexit ]
  %_39.i5091063.lcssa11121143 = phi <4 x i64> [ %65, %bb14 ], [ %_40.i51010651092, %bb1.i28.loopexit ]
  %_40.i5101065.lcssa11141142 = phi <4 x i64> [ %67, %bb14 ], [ %_6.i49110591095, %bb1.i28.loopexit ]
  %_43.i5131067.lcssa11161141 = phi <4 x i64> [ %73, %bb14 ], [ %_20.i50010611094, %bb1.i28.loopexit ]
  %_22.i2201069.lcssa11181140 = phi i64 [ %_5.i.71261, %bb14 ], [ %_43.i26210751087, %bb1.i28.loopexit ]
  %_43.i2221071.lcssa11201139 = phi i64 [ %_5.i.41258, %bb14 ], [ %_43.i222, %bb1.i28.loopexit ]
  %_43.i22210711073.lcssa11221138 = phi i64 [ %_5.i.61260, %bb14 ], [ %_43.i22210711089, %bb1.i28.loopexit ]
  %_43.i2621075.lcssa11241137 = phi i64 [ %_5.i.51259, %bb14 ], [ %_43.i262, %bb1.i28.loopexit ]
  %_22.i2601076.lcssa11261136 = phi i64 [ %current_state.sroa.0.0.copyload1254, %bb14 ], [ %_22.i220, %bb1.i28.loopexit ]
  %_22.i2601078.lcssa11281135 = phi i64 [ %_5.i.11255, %bb14 ], [ %_22.i260, %bb1.i28.loopexit ]
  %_22.i26010761080.lcssa11301134 = phi i64 [ %_5.i.21256, %bb14 ], [ %_22.i26010761086, %bb1.i28.loopexit ]
  %_43.i2221082.lcssa11321133 = phi i64 [ %_5.i.31257, %bb14 ], [ %_22.i26010781085, %bb1.i28.loopexit ]
  %.idx.i = shl nuw nsw i64 %iter.sroa.0.0.i291149, 7
  %77 = getelementptr inbounds nuw i8, ptr %t2, i64 %.idx.i
  br label %bb16.i

bb16.i:                                           ; preds = %bb14.i, %bb16.i
  %k64x4_idx.sroa.0.1.i1100 = phi i64 [ %k64x4_idx.sroa.0.0.i1150, %bb14.i ], [ %86, %bb16.i ]
  %iter1.sroa.0.0.i1099 = phi i64 [ 0, %bb14.i ], [ %78, %bb16.i ]
  %_3.i48810541098 = phi <4 x i64> [ %_3.i4881054.lcssa11021148, %bb14.i ], [ %_39.i50910631093, %bb16.i ]
  %_3.i488105410551097 = phi <4 x i64> [ %_3.i48810541055.lcssa11041147, %bb14.i ], [ %_3.i48810541098, %bb16.i ]
  %_5.i49010571096 = phi <4 x i64> [ %_5.i4901057.lcssa11061146, %bb14.i ], [ %_43.i51310671091, %bb16.i ]
  %_6.i49110591095 = phi <4 x i64> [ %_6.i4911059.lcssa11081145, %bb14.i ], [ %_5.i49010571096, %bb16.i ]
  %_20.i50010611094 = phi <4 x i64> [ %_20.i5001061.lcssa11101144, %bb14.i ], [ %_3.i542, %bb16.i ]
  %_39.i50910631093 = phi <4 x i64> [ %_39.i5091063.lcssa11121143, %bb14.i ], [ %_40.i51010651092, %bb16.i ]
  %_40.i51010651092 = phi <4 x i64> [ %_40.i5101065.lcssa11141142, %bb14.i ], [ %_6.i49110591095, %bb16.i ]
  %_43.i51310671091 = phi <4 x i64> [ %_43.i5131067.lcssa11161141, %bb14.i ], [ %_20.i50010611094, %bb16.i ]
  %_22.i22010691090 = phi i64 [ %_22.i2201069.lcssa11181140, %bb14.i ], [ %_43.i26210751087, %bb16.i ]
  %_43.i22210711089 = phi i64 [ %_43.i2221071.lcssa11201139, %bb14.i ], [ %_43.i222, %bb16.i ]
  %_43.i222107110731088 = phi i64 [ %_43.i22210711073.lcssa11221138, %bb14.i ], [ %_43.i22210711089, %bb16.i ]
  %_43.i26210751087 = phi i64 [ %_43.i2621075.lcssa11241137, %bb14.i ], [ %_43.i262, %bb16.i ]
  %_22.i26010761086 = phi i64 [ %_22.i2601076.lcssa11261136, %bb14.i ], [ %_22.i220, %bb16.i ]
  %_22.i26010781085 = phi i64 [ %_22.i2601078.lcssa11281135, %bb14.i ], [ %_22.i260, %bb16.i ]
  %_22.i260107610801084 = phi i64 [ %_22.i26010761080.lcssa11301134, %bb14.i ], [ %_22.i26010761086, %bb16.i ]
  %_43.i22210821083 = phi i64 [ %_43.i2221082.lcssa11321133, %bb14.i ], [ %_22.i26010781085, %bb16.i ]
  %78 = add nuw nsw i64 %iter1.sroa.0.0.i1099, 1
  %_12.i31 = getelementptr inbounds nuw i64, ptr @alloc_448aca044373cb4cde6849f95106f1ce, i64 %k64x4_idx.sroa.0.1.i1100
  %dst.sroa.0.0.copyload.i4839301263 = load <2 x i64>, ptr %_12.i31, align 8, !noalias !209
  %79 = shufflevector <2 x i64> %dst.sroa.0.0.copyload.i4839301263, <2 x i64> poison, <4 x i32> <i32 0, i32 1, i32 0, i32 1>
  %80 = shufflevector <4 x i64> %_3.i488105410551097, <4 x i64> %_3.i48810541098, <4 x i32> <i32 1, i32 4, i32 3, i32 6>
  %81 = shufflevector <4 x i64> %_6.i49110591095, <4 x i64> %_5.i49010571096, <4 x i32> <i32 1, i32 4, i32 3, i32 6>
  %_3.i562 = lshr <4 x i64> %80, splat (i64 1)
  %_3.i561 = add <4 x i64> %_3.i488105410551097, %81
  %_3.i560 = lshr <4 x i64> %80, splat (i64 7)
  %_3.i559 = shl <4 x i64> %80, splat (i64 56)
  %_3.i558 = xor <4 x i64> %_3.i562, %_3.i560
  %_3.i557 = lshr <4 x i64> %80, splat (i64 8)
  %_3.i556 = xor <4 x i64> %_3.i558, %_3.i559
  %_3.i555 = shl <4 x i64> %80, splat (i64 63)
  %_3.i554 = xor <4 x i64> %_3.i556, %_3.i557
  %_3.i553 = xor <4 x i64> %_3.i554, %_3.i555
  %_3.i552 = lshr <4 x i64> %_20.i50010611094, splat (i64 6)
  %_3.i551 = shl <4 x i64> %_20.i50010611094, splat (i64 3)
  %_3.i550 = add <4 x i64> %_3.i561, %_3.i553
  %_3.i549 = lshr <4 x i64> %_20.i50010611094, splat (i64 19)
  %_3.i548 = xor <4 x i64> %_3.i551, %_3.i552
  %_3.i547 = shl <4 x i64> %_20.i50010611094, splat (i64 45)
  %_3.i546 = xor <4 x i64> %_3.i548, %_3.i549
  %_3.i545 = lshr <4 x i64> %_20.i50010611094, splat (i64 61)
  %_3.i544 = xor <4 x i64> %_3.i546, %_3.i547
  %_3.i543 = xor <4 x i64> %_3.i544, %_3.i545
  %_3.i542 = add <4 x i64> %_3.i550, %_3.i543
  %_3.i541 = add <4 x i64> %_3.i542, %79
  %.idx931 = shl nuw nsw i64 %iter1.sroa.0.0.i1099, 4
  %82 = getelementptr inbounds nuw i8, ptr %ms, i64 %.idx931
  %_20.i35 = load i64, ptr %82, align 16, !alias.scope !204, !noalias !212, !noundef !137
  %_5.i231 = add i64 %_22.i22010691090, %_20.i35
  %_0.i514 = tail call i64 @llvm.fshl.i64(i64 %_43.i22210711089, i64 %_43.i22210711089, i64 50)
  %_0.i515 = tail call i64 @llvm.fshl.i64(i64 %_43.i22210711089, i64 %_43.i22210711089, i64 46)
  %_8.i235 = xor i64 %_0.i514, %_0.i515
  %_0.i516 = tail call i64 @llvm.fshl.i64(i64 %_43.i22210711089, i64 %_43.i22210711089, i64 23)
  %_7.i237 = xor i64 %_8.i235, %_0.i516
  %_4.i238 = add i64 %_5.i231, %_7.i237
  %_19.i242 = xor i64 %_43.i26210751087, %_43.i222107110731088
  %_17.i243 = and i64 %_19.i242, %_43.i22210711089
  %_15.i244 = xor i64 %_17.i243, %_43.i222107110731088
  %t.i245 = add i64 %_4.i238, %_15.i244
  %_0.i517 = tail call i64 @llvm.fshl.i64(i64 %_22.i26010761086, i64 %_22.i26010761086, i64 36)
  %_0.i518 = tail call i64 @llvm.fshl.i64(i64 %_22.i26010761086, i64 %_22.i26010761086, i64 30)
  %_25.i249 = xor i64 %_0.i517, %_0.i518
  %_0.i519 = tail call i64 @llvm.fshl.i64(i64 %_22.i26010761086, i64 %_22.i26010761086, i64 25)
  %_24.i251 = xor i64 %_25.i249, %_0.i519
  %_23.i252 = add i64 %t.i245, %_24.i251
  %_371.i256 = xor i64 %_22.i260107610801084, %_22.i26010781085
  %_33.i257 = and i64 %_371.i256, %_22.i26010761086
  %_40.i258 = and i64 %_22.i260107610801084, %_22.i26010781085
  %_32.i259 = xor i64 %_33.i257, %_40.i258
  %_22.i260 = add i64 %_23.i252, %_32.i259
  %_43.i262 = add i64 %_43.i22210821083, %t.i245
  %83 = getelementptr inbounds nuw i8, ptr %82, i64 8
  %_24.i36 = load i64, ptr %83, align 8, !alias.scope !204, !noalias !212, !noundef !137
  %_0.i520 = tail call i64 @llvm.fshl.i64(i64 %_43.i262, i64 %_43.i262, i64 50)
  %_0.i521 = tail call i64 @llvm.fshl.i64(i64 %_43.i262, i64 %_43.i262, i64 46)
  %_8.i195 = xor i64 %_0.i520, %_0.i521
  %_0.i522 = tail call i64 @llvm.fshl.i64(i64 %_43.i262, i64 %_43.i262, i64 23)
  %_7.i197 = xor i64 %_8.i195, %_0.i522
  %_19.i202 = xor i64 %_43.i26210751087, %_43.i22210711089
  %_17.i203 = and i64 %_43.i262, %_19.i202
  %_15.i204 = xor i64 %_17.i203, %_43.i26210751087
  %_5.i191 = add i64 %_15.i204, %_43.i222107110731088
  %_4.i198 = add i64 %_5.i191, %_7.i197
  %t.i205 = add i64 %_4.i198, %_24.i36
  %_0.i523 = tail call i64 @llvm.fshl.i64(i64 %_22.i260, i64 %_22.i260, i64 36)
  %_0.i524 = tail call i64 @llvm.fshl.i64(i64 %_22.i260, i64 %_22.i260, i64 30)
  %_25.i209 = xor i64 %_0.i523, %_0.i524
  %_0.i525 = tail call i64 @llvm.fshl.i64(i64 %_22.i260, i64 %_22.i260, i64 25)
  %_24.i211 = xor i64 %_25.i209, %_0.i525
  %_371.i216 = xor i64 %_22.i26010781085, %_22.i26010761086
  %_33.i217 = and i64 %_22.i260, %_371.i216
  %_40.i218 = and i64 %_22.i26010781085, %_22.i26010761086
  %_32.i219 = xor i64 %_33.i217, %_40.i218
  %_23.i212 = add i64 %_24.i211, %_32.i219
  %_22.i220 = add i64 %_23.i212, %t.i205
  %_43.i222 = add i64 %t.i205, %_22.i260107610801084
  %dst.i526 = shufflevector <4 x i64> %_3.i541, <4 x i64> poison, <2 x i32> <i32 0, i32 1>
  %84 = getelementptr inbounds nuw <2 x i64>, ptr %ms, i64 %iter1.sroa.0.0.i1099
  store <2 x i64> %dst.i526, ptr %84, align 16, !alias.scope !204, !noalias !212
  %dst.i527 = shufflevector <4 x i64> %_3.i541, <4 x i64> poison, <2 x i32> <i32 2, i32 3>
  %85 = getelementptr inbounds nuw <2 x i64>, ptr %77, i64 %iter1.sroa.0.0.i1099
  store <2 x i64> %dst.i527, ptr %85, align 16, !alias.scope !207, !noalias !215
  %86 = add i64 %k64x4_idx.sroa.0.1.i1100, 2
  %exitcond1209.not = icmp eq i64 %78, 8
  br i1 %exitcond1209.not, label %bb1.i28.loopexit, label %bb16.i

bb2.i:                                            ; preds = %bb1.i28.loopexit, %bb2.i
  %iter.sroa.0.0.i1174 = phi i64 [ %87, %bb2.i ], [ 64, %bb1.i28.loopexit ]
  %_16.i27911521173 = phi i64 [ %_20.i28111561171, %bb2.i ], [ %_43.i26210751087, %bb1.i28.loopexit ]
  %_43.i30211541172 = phi i64 [ %_43.i302, %bb2.i ], [ %_43.i222, %bb1.i28.loopexit ]
  %_20.i28111561171 = phi i64 [ %_43.i302115411581170, %bb2.i ], [ %_43.i22210711089, %bb1.i28.loopexit ]
  %_43.i302115411581170 = phi i64 [ %_43.i30211541172, %bb2.i ], [ %_43.i262, %bb1.i28.loopexit ]
  %_22.i30011591169 = phi i64 [ %_22.i300, %bb2.i ], [ %_22.i220, %bb1.i28.loopexit ]
  %_22.i300115911611168 = phi i64 [ %_22.i30011591169, %bb2.i ], [ %_22.i260, %bb1.i28.loopexit ]
  %_22.i3001159116111631167 = phi i64 [ %_22.i300115911611168, %bb2.i ], [ %_22.i26010761086, %bb1.i28.loopexit ]
  %_22.i30011591161116311651166 = phi i64 [ %_22.i3001159116111631167, %bb2.i ], [ %_22.i26010781085, %bb1.i28.loopexit ]
  %_7.i = and i64 %iter.sroa.0.0.i1174, 15
  %87 = add nuw nsw i64 %iter.sroa.0.0.i1174, 1
  %88 = getelementptr inbounds nuw i64, ptr %ms, i64 %_7.i
  %_6.i = load i64, ptr %88, align 8, !alias.scope !216, !noalias !219, !noundef !137
  %_5.i271 = add i64 %_16.i27911521173, %_6.i
  %_0.i528 = tail call i64 @llvm.fshl.i64(i64 %_43.i30211541172, i64 %_43.i30211541172, i64 50)
  %_0.i529 = tail call i64 @llvm.fshl.i64(i64 %_43.i30211541172, i64 %_43.i30211541172, i64 46)
  %_8.i275 = xor i64 %_0.i528, %_0.i529
  %_0.i530 = tail call i64 @llvm.fshl.i64(i64 %_43.i30211541172, i64 %_43.i30211541172, i64 23)
  %_7.i277 = xor i64 %_8.i275, %_0.i530
  %_4.i278 = add i64 %_5.i271, %_7.i277
  %_19.i282 = xor i64 %_43.i302115411581170, %_20.i28111561171
  %_17.i283 = and i64 %_19.i282, %_43.i30211541172
  %_15.i284 = xor i64 %_17.i283, %_20.i28111561171
  %t.i285 = add i64 %_4.i278, %_15.i284
  %_0.i531 = tail call i64 @llvm.fshl.i64(i64 %_22.i30011591169, i64 %_22.i30011591169, i64 36)
  %_0.i532 = tail call i64 @llvm.fshl.i64(i64 %_22.i30011591169, i64 %_22.i30011591169, i64 30)
  %_25.i289 = xor i64 %_0.i531, %_0.i532
  %_0.i533 = tail call i64 @llvm.fshl.i64(i64 %_22.i30011591169, i64 %_22.i30011591169, i64 25)
  %_24.i291 = xor i64 %_25.i289, %_0.i533
  %_23.i292 = add i64 %t.i285, %_24.i291
  %_371.i296 = xor i64 %_22.i3001159116111631167, %_22.i300115911611168
  %_33.i297 = and i64 %_371.i296, %_22.i30011591169
  %_40.i298 = and i64 %_22.i3001159116111631167, %_22.i300115911611168
  %_32.i299 = xor i64 %_33.i297, %_40.i298
  %_22.i300 = add i64 %_23.i292, %_32.i299
  %_43.i302 = add i64 %_22.i30011591161116311651166, %t.i285
  %exitcond1211.not = icmp eq i64 %87, 80
  br i1 %exitcond1211.not, label %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx212rounds_64_79.exit, label %bb2.i

_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx212rounds_64_79.exit: ; preds = %bb2.i
  %_5.i26 = add i64 %_22.i300, %current_state.sroa.0.0.copyload1254
  %_5.i26.1 = add i64 %_22.i30011591169, %_5.i.11255
  %_5.i26.2 = add i64 %_22.i300115911611168, %_5.i.21256
  %_5.i26.3 = add i64 %_22.i3001159116111631167, %_5.i.31257
  %_5.i26.4 = add i64 %_43.i302, %_5.i.41258
  %_5.i26.5 = add i64 %_43.i30211541172, %_5.i.51259
  %_5.i26.6 = add i64 %_43.i302115411581170, %_5.i.61260
  %_5.i26.7 = add i64 %_20.i28111561171, %_5.i.71261
  br label %bb4.i

bb4.i:                                            ; preds = %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx212rounds_64_79.exit, %bb4.i
  %iter.sroa.0.0.idx.i1200 = phi i64 [ 0, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx212rounds_64_79.exit ], [ %iter.sroa.0.0.add.i, %bb4.i ]
  %_16.i15911771199 = phi i64 [ %_5.i26.7, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx212rounds_64_79.exit ], [ %_20.i16111811197, %bb4.i ]
  %_43.i18211791198 = phi i64 [ %_5.i26.4, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx212rounds_64_79.exit ], [ %_43.i182, %bb4.i ]
  %_20.i16111811197 = phi i64 [ %_5.i26.6, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx212rounds_64_79.exit ], [ %_43.i182117911831196, %bb4.i ]
  %_43.i182117911831196 = phi i64 [ %_5.i26.5, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx212rounds_64_79.exit ], [ %_43.i18211791198, %bb4.i ]
  %_22.i18011851195 = phi i64 [ %_5.i26, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx212rounds_64_79.exit ], [ %_22.i180, %bb4.i ]
  %_22.i180118511871194 = phi i64 [ %_5.i26.1, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx212rounds_64_79.exit ], [ %_22.i18011851195, %bb4.i ]
  %_22.i1801185118711891193 = phi i64 [ %_5.i26.2, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx212rounds_64_79.exit ], [ %_22.i180118511871194, %bb4.i ]
  %_22.i18011851187118911911192 = phi i64 [ %_5.i26.3, %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx212rounds_64_79.exit ], [ %_22.i1801185118711891193, %bb4.i ]
  %iter.sroa.0.0.ptr.i = getelementptr inbounds nuw i8, ptr %t2, i64 %iter.sroa.0.0.idx.i1200
  %iter.sroa.0.0.add.i = add nuw nsw i64 %iter.sroa.0.0.idx.i1200, 8
  %_9.i41 = load i64, ptr %iter.sroa.0.0.ptr.i, align 8, !alias.scope !221, !noalias !224, !noundef !137
  %_5.i151 = add i64 %_16.i15911771199, %_9.i41
  %_0.i534 = tail call i64 @llvm.fshl.i64(i64 %_43.i18211791198, i64 %_43.i18211791198, i64 50)
  %_0.i535 = tail call i64 @llvm.fshl.i64(i64 %_43.i18211791198, i64 %_43.i18211791198, i64 46)
  %_8.i155 = xor i64 %_0.i534, %_0.i535
  %_0.i536 = tail call i64 @llvm.fshl.i64(i64 %_43.i18211791198, i64 %_43.i18211791198, i64 23)
  %_7.i157 = xor i64 %_8.i155, %_0.i536
  %_4.i158 = add i64 %_5.i151, %_7.i157
  %_19.i162 = xor i64 %_43.i182117911831196, %_20.i16111811197
  %_17.i163 = and i64 %_19.i162, %_43.i18211791198
  %_15.i164 = xor i64 %_17.i163, %_20.i16111811197
  %t.i165 = add i64 %_4.i158, %_15.i164
  %_0.i537 = tail call i64 @llvm.fshl.i64(i64 %_22.i18011851195, i64 %_22.i18011851195, i64 36)
  %_0.i538 = tail call i64 @llvm.fshl.i64(i64 %_22.i18011851195, i64 %_22.i18011851195, i64 30)
  %_25.i169 = xor i64 %_0.i537, %_0.i538
  %_0.i539 = tail call i64 @llvm.fshl.i64(i64 %_22.i18011851195, i64 %_22.i18011851195, i64 25)
  %_24.i171 = xor i64 %_25.i169, %_0.i539
  %_23.i172 = add i64 %t.i165, %_24.i171
  %_371.i176 = xor i64 %_22.i1801185118711891193, %_22.i180118511871194
  %_33.i177 = and i64 %_371.i176, %_22.i18011851195
  %_40.i178 = and i64 %_22.i1801185118711891193, %_22.i180118511871194
  %_32.i179 = xor i64 %_33.i177, %_40.i178
  %_22.i180 = add i64 %_23.i172, %_32.i179
  %_43.i182 = add i64 %_22.i18011851187118911911192, %t.i165
  %_23.i40 = icmp eq i64 %iter.sroa.0.0.add.i, 640
  br i1 %_23.i40, label %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx220process_second_block.exit, label %bb4.i

_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx220process_second_block.exit: ; preds = %bb4.i
  %_5.i = add i64 %_22.i180, %_5.i26
  %_5.i.1 = add i64 %_22.i18011851195, %_5.i26.1
  %_5.i.2 = add i64 %_22.i180118511871194, %_5.i26.2
  %_5.i.3 = add i64 %_22.i1801185118711891193, %_5.i26.3
  %_5.i.4 = add i64 %_43.i182, %_5.i26.4
  %_5.i.5 = add i64 %_43.i18211791198, %_5.i26.5
  %_5.i.6 = add i64 %_43.i182117911831196, %_5.i26.6
  %_5.i.7 = add i64 %_20.i16111811197, %_5.i26.7
  %_8.i.i396 = add i64 %iter.sroa.0.01204, 2
  %89 = add i64 %iter.sroa.5.01203, -1
  %_6.not.i.i = icmp eq i64 %89, 0
  br i1 %_6.not.i.i, label %bb15.loopexit, label %bb14

bb15.loopexit:                                    ; preds = %_RNvNtNtCs7dqAOVfn11v_4sha26sha5128x86_avx220process_second_block.exit
  store i64 %_5.i, ptr %state, align 8
  store i64 %_5.i.1, ptr %current_state.sroa.12.0.state.sroa_idx, align 8
  store i64 %_5.i.2, ptr %current_state.sroa.20.0.state.sroa_idx, align 8
  store i64 %_5.i.3, ptr %current_state.sroa.28.0.state.sroa_idx, align 8
  store i64 %_5.i.4, ptr %current_state.sroa.36.0.state.sroa_idx, align 8
  store i64 %_5.i.5, ptr %current_state.sroa.44.0.state.sroa_idx, align 8
  store i64 %_5.i.6, ptr %current_state.sroa.52.0.state.sroa_idx, align 8
  store i64 %_5.i.7, ptr %current_state.sroa.60.0.state.sroa_idx, align 8
  br label %bb15

bb15:                                             ; preds = %bb15.loopexit, %bb5
  call void @llvm.lifetime.end.p0(ptr nonnull %t2)
  call void @llvm.lifetime.end.p0(ptr nonnull %ms)
  ret void
}
