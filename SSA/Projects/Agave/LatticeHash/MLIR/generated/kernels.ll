; ModuleID = 'agave_lthash_extract.f366d146f8fe3407-cgu.0'
source_filename = "agave_lthash_extract.f366d146f8fe3407-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_141662a74a282820cac3ca1f940ed0c5 = private unnamed_addr constant [56 x i8] c"/tmp/agave-lthash-mlir-tools/generated/batch/../arch.rs\00", align 1
@alloc_61fb4a9344bbdaf2573accd6331d7e32 = private unnamed_addr constant [896 x i8] c"\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00\0C\00\00\00\00\00\00\00\0D\00\00\00\00\00\00\00\0E\00\00\00\00\00\00\00\0F\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\0D\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00\0C\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\0E\00\00\00\00\00\00\00\0F\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\0C\00\00\00\00\00\00\00\0D\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00\0E\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00\0F\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00\0C\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\0E\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\0D\00\00\00\00\00\00\00\0F\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00\0C\00\00\00\00\00\00\00\0D\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00\0F\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\0E\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\0E\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\0C\00\00\00\00\00\00\00\0F\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\0D\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00\0F\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00\0E\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\0C\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00\0D\00\00\00\00\00\00\00", align 8
@alloc_83bddfce772813ac48c9037cf7b0770f = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_141662a74a282820cac3ca1f940ed0c5, [16 x i8] c"7\00\00\00\00\00\00\00\D3\00\00\007\00\00\00" }>, align 8

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
define void @agave_add_u16_16(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([64 x i8]) align 64 captures(none) dereferenceable(64) initializes((0, 64)) %_0, ptr dead_on_return noalias nofree noundef readonly align 64 captures(none) dereferenceable(64) %a, ptr dead_on_return noalias nofree noundef readonly align 64 captures(none) dereferenceable(64) %b) unnamed_addr #0 {
start:
  %0 = load <32 x i16>, ptr %a, align 64
  %1 = load <32 x i16>, ptr %b, align 64
  %_3.i = add <32 x i16> %1, %0
  store <32 x i16> %_3.i, ptr %_0, align 64, !alias.scope !4, !noalias !7
  ret void
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
define void @agave_add_u16_8(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([32 x i8]) align 32 captures(none) dereferenceable(32) initializes((0, 32)) %_0, ptr dead_on_return noalias nofree noundef readonly align 32 captures(none) dereferenceable(32) %a, ptr dead_on_return noalias nofree noundef readonly align 32 captures(none) dereferenceable(32) %b) unnamed_addr #1 {
start:
  %0 = load <16 x i16>, ptr %a, align 32
  %1 = load <16 x i16>, ptr %b, align 32
  %_3.i = add <16 x i16> %1, %0
  store <16 x i16> %_3.i, ptr %_0, align 32, !alias.scope !13
  ret void
}

; Function Attrs: nounwind nonlazybind uwtable
define void @agave_batch_16(ptr noalias nofree noundef readonly align 4 captures(none) dereferenceable(16384) %lanes, ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(128) %lengths, ptr noalias nofree noundef align 2 captures(none) dereferenceable(2048) %acc) unnamed_addr #2 personality ptr @rust_eh_personality {
start:
  %m.i = alloca [1024 x i8], align 64
  %root_m.i = alloca [1024 x i8], align 64
  %_32.1.i = getelementptr inbounds nuw i8, ptr %lanes, i64 1024
  %_32.2.i = getelementptr inbounds nuw i8, ptr %lanes, i64 2048
  %_32.3.i = getelementptr inbounds nuw i8, ptr %lanes, i64 3072
  %_32.4.i = getelementptr inbounds nuw i8, ptr %lanes, i64 4096
  %_32.5.i = getelementptr inbounds nuw i8, ptr %lanes, i64 5120
  %_32.6.i = getelementptr inbounds nuw i8, ptr %lanes, i64 6144
  %_32.7.i = getelementptr inbounds nuw i8, ptr %lanes, i64 7168
  %_32.8.i = getelementptr inbounds nuw i8, ptr %lanes, i64 8192
  %_32.9.i = getelementptr inbounds nuw i8, ptr %lanes, i64 9216
  %_32.10.i = getelementptr inbounds nuw i8, ptr %lanes, i64 10240
  %_32.11.i = getelementptr inbounds nuw i8, ptr %lanes, i64 11264
  %_32.12.i = getelementptr inbounds nuw i8, ptr %lanes, i64 12288
  %_32.13.i = getelementptr inbounds nuw i8, ptr %lanes, i64 13312
  %_32.14.i = getelementptr inbounds nuw i8, ptr %lanes, i64 14336
  %_32.15.i = getelementptr inbounds nuw i8, ptr %lanes, i64 15360
  %m.i254.sroa.22.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 64
  %m.i254.sroa.40.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 128
  %m.i254.sroa.57.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 192
  %m.i254.sroa.73.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 256
  %m.i254.sroa.88.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 320
  %m.i254.sroa.102.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 384
  %m.i254.sroa.115.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 448
  %m.i254.sroa.127.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 512
  %m.i254.sroa.138.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 576
  %m.i254.sroa.148.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 640
  %m.i254.sroa.157.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 704
  %m.i254.sroa.165.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 768
  %m.i254.sroa.172.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 832
  %m.i254.sroa.178.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 896
  %m.i254.sroa.183.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 960
  %wide.load = load <8 x i64>, ptr %lengths, align 8, !noalias !16
  %0 = getelementptr inbounds nuw i8, ptr %lengths, i64 64
  %wide.load.1 = load <8 x i64>, ptr %0, align 8, !noalias !16
  br label %bb3.i

bb3.i:                                            ; preds = %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i, %start
  %off.i.sroa.20.0 = phi <8 x i64> [ zeroinitializer, %start ], [ %off.i.sroa.20.8, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %off.i.sroa.0.0 = phi <8 x i64> [ zeroinitializer, %start ], [ %off.i.sroa.0.8, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %1 = phi i64 [ 0, %start ], [ %171, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %2 = phi i64 [ 0, %start ], [ %169, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %3 = phi i64 [ 0, %start ], [ %167, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %4 = phi i64 [ 0, %start ], [ %165, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %5 = phi i64 [ 0, %start ], [ %163, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %6 = phi i64 [ 0, %start ], [ %161, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %7 = phi i64 [ 0, %start ], [ %159, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %8 = phi i64 [ 0, %start ], [ %157, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %9 = phi i64 [ 0, %start ], [ %155, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %10 = phi i64 [ 0, %start ], [ %153, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %11 = phi i64 [ 0, %start ], [ %151, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %12 = phi i64 [ 0, %start ], [ %149, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %13 = phi i64 [ 0, %start ], [ %147, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %14 = phi i64 [ 0, %start ], [ %145, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %15 = phi i64 [ 0, %start ], [ %143, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %16 = phi i64 [ 0, %start ], [ %140, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %17 = phi <16 x i32> [ splat (i32 1541459225), %start ], [ %_4.i575.7, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %18 = phi <16 x i32> [ splat (i32 528734635), %start ], [ %_4.i575.6, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %19 = phi <16 x i32> [ splat (i32 -1694144372), %start ], [ %_4.i575.5, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %20 = phi <16 x i32> [ splat (i32 1359893119), %start ], [ %_4.i575.4, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %21 = phi <16 x i32> [ splat (i32 -1521486534), %start ], [ %_4.i575.3, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %22 = phi <16 x i32> [ splat (i32 1013904242), %start ], [ %_4.i575.2, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %23 = phi <16 x i32> [ splat (i32 -1150833019), %start ], [ %_4.i575.1, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %24 = phi <16 x i32> [ splat (i32 1779033703), %start ], [ %_4.i575, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i ]
  %25 = add <8 x i64> %off.i.sroa.0.0, splat (i64 64)
  %26 = icmp ugt <8 x i64> %wide.load, %25
  %27 = icmp eq <8 x i64> %off.i.sroa.0.0, zeroinitializer
  %28 = select <8 x i1> %26, <8 x i32> zeroinitializer, <8 x i32> splat (i32 10)
  %29 = zext <8 x i1> %27 to <8 x i32>
  %30 = or disjoint <8 x i32> %28, %29
  %31 = bitcast <8 x i32> %30 to <4 x i64>
  %block_flags.i.sroa.0.0.vec.expand = shufflevector <4 x i64> %31, <4 x i64> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 poison, i32 poison, i32 poison, i32 poison>
  %32 = sub <8 x i64> %wide.load, %off.i.sroa.0.0
  %33 = tail call <8 x i64> @llvm.umin.v8i64(<8 x i64> %32, <8 x i64> splat (i64 64))
  %34 = trunc nuw nsw <8 x i64> %33 to <8 x i32>
  %35 = bitcast <8 x i32> %34 to <4 x i64>
  %block_sz.i.sroa.0.0.vec.expand = shufflevector <4 x i64> %35, <4 x i64> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 poison, i32 poison, i32 poison, i32 poison>
  %36 = zext <8 x i1> %26 to <8 x i8>
  %active.i.sroa.0.0.vec.expand = shufflevector <8 x i8> %36, <8 x i8> poison, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>
  %37 = add <8 x i64> %off.i.sroa.20.0, splat (i64 64)
  %38 = icmp ugt <8 x i64> %wide.load.1, %37
  %39 = icmp eq <8 x i64> %off.i.sroa.20.0, zeroinitializer
  %40 = select <8 x i1> %38, <8 x i32> zeroinitializer, <8 x i32> splat (i32 10)
  %41 = zext <8 x i1> %39 to <8 x i32>
  %42 = or disjoint <8 x i32> %40, %41
  %43 = bitcast <8 x i32> %42 to <4 x i64>
  %block_flags.i.sroa.0.32.vec.expand = shufflevector <4 x i64> %43, <4 x i64> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 0, i32 1, i32 2, i32 3>
  %block_flags.i.sroa.0.32.vecblend = shufflevector <8 x i64> %block_flags.i.sroa.0.0.vec.expand, <8 x i64> %block_flags.i.sroa.0.32.vec.expand, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %44 = sub <8 x i64> %wide.load.1, %off.i.sroa.20.0
  %45 = tail call <8 x i64> @llvm.umin.v8i64(<8 x i64> %44, <8 x i64> splat (i64 64))
  %46 = trunc nuw nsw <8 x i64> %45 to <8 x i32>
  %47 = bitcast <8 x i32> %46 to <4 x i64>
  %block_sz.i.sroa.0.32.vec.expand = shufflevector <4 x i64> %47, <4 x i64> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 0, i32 1, i32 2, i32 3>
  %block_sz.i.sroa.0.32.vecblend = shufflevector <8 x i64> %block_sz.i.sroa.0.0.vec.expand, <8 x i64> %block_sz.i.sroa.0.32.vec.expand, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %48 = zext <8 x i1> %38 to <8 x i8>
  %active.i.sroa.0.8.vec.expand = shufflevector <8 x i8> %48, <8 x i8> poison, <16 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %active.i.sroa.0.8.vecblend = shufflevector <16 x i8> %active.i.sroa.0.0.vec.expand, <16 x i8> %active.i.sroa.0.8.vec.expand, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 24, i32 25, i32 26, i32 27, i32 28, i32 29, i32 30, i32 31>
  %.fr = freeze <16 x i8> %active.i.sroa.0.8.vecblend
  call void @llvm.lifetime.start.p0(ptr nonnull %m.i), !noalias !16
  %_257.i = lshr i64 %16, 2
  %_257.1.i = lshr i64 %15, 2
  %_257.2.i = lshr i64 %14, 2
  %_257.3.i = lshr i64 %13, 2
  %_257.4.i = lshr i64 %12, 2
  %_257.5.i = lshr i64 %11, 2
  %_257.6.i = lshr i64 %10, 2
  %_257.7.i = lshr i64 %9, 2
  %_257.8.i = lshr i64 %8, 2
  %_257.9.i = lshr i64 %7, 2
  %_257.10.i = lshr i64 %6, 2
  %_257.11.i = lshr i64 %5, 2
  %_257.12.i = lshr i64 %4, 2
  %_257.13.i = lshr i64 %3, 2
  %_257.14.i = lshr i64 %2, 2
  %_257.15.i = lshr i64 %1, 2
  %_65.i265 = icmp ugt i64 %16, 1027
  %_71.i266 = getelementptr inbounds nuw i32, ptr %lanes, i64 %_257.i
  %_71.1.i = getelementptr inbounds nuw i32, ptr %_32.1.i, i64 %_257.1.i
  %_71.2.i = getelementptr inbounds nuw i32, ptr %_32.2.i, i64 %_257.2.i
  %_71.3.i = getelementptr inbounds nuw i32, ptr %_32.3.i, i64 %_257.3.i
  %_71.4.i = getelementptr inbounds nuw i32, ptr %_32.4.i, i64 %_257.4.i
  %_71.5.i = getelementptr inbounds nuw i32, ptr %_32.5.i, i64 %_257.5.i
  %_71.6.i = getelementptr inbounds nuw i32, ptr %_32.6.i, i64 %_257.6.i
  %_71.7.i = getelementptr inbounds nuw i32, ptr %_32.7.i, i64 %_257.7.i
  %_71.8.i = getelementptr inbounds nuw i32, ptr %_32.8.i, i64 %_257.8.i
  %_71.9.i = getelementptr inbounds nuw i32, ptr %_32.9.i, i64 %_257.9.i
  %_71.10.i = getelementptr inbounds nuw i32, ptr %_32.10.i, i64 %_257.10.i
  %_71.11.i = getelementptr inbounds nuw i32, ptr %_32.11.i, i64 %_257.11.i
  %_71.12.i = getelementptr inbounds nuw i32, ptr %_32.12.i, i64 %_257.12.i
  %_71.13.i = getelementptr inbounds nuw i32, ptr %_32.13.i, i64 %_257.13.i
  %_71.14.i = getelementptr inbounds nuw i32, ptr %_32.14.i, i64 %_257.14.i
  %_71.15.i = getelementptr inbounds nuw i32, ptr %_32.15.i, i64 %_257.15.i
  br i1 %_65.i265, label %bb20.i, label %bb11.lr.ph.i.split, !prof !20

bb11.lr.ph.i.split:                               ; preds = %bb3.i
  %_65.15.i = icmp ugt i64 %1, 1027
  %_65.14.i = icmp ugt i64 %2, 1027
  %_65.13.i = icmp ugt i64 %3, 1027
  %_65.12.i = icmp ugt i64 %4, 1027
  %_65.11.i = icmp ugt i64 %5, 1027
  %_65.10.i = icmp ugt i64 %6, 1027
  %_65.9.i = icmp ugt i64 %7, 1027
  %_65.8.i = icmp ugt i64 %8, 1027
  %_65.7.i = icmp ugt i64 %9, 1027
  %_65.6.i = icmp ugt i64 %10, 1027
  %_65.5.i = icmp ugt i64 %11, 1027
  %_65.4.i = icmp ugt i64 %12, 1027
  %_65.3.i = icmp ugt i64 %13, 1027
  %_65.2.i = icmp ugt i64 %14, 1027
  %_65.1.i = icmp ugt i64 %15, 1027
  %49 = or i1 %_65.14.i, %_65.15.i
  %50 = or i1 %49, %_65.13.i
  %51 = or i1 %50, %_65.12.i
  %52 = or i1 %51, %_65.11.i
  %53 = or i1 %52, %_65.10.i
  %54 = or i1 %53, %_65.9.i
  %55 = or i1 %54, %_65.8.i
  %56 = or i1 %55, %_65.7.i
  %57 = or i1 %56, %_65.6.i
  %58 = or i1 %57, %_65.5.i
  %59 = or i1 %58, %_65.4.i
  %60 = or i1 %59, %_65.3.i
  %61 = or i1 %60, %_65.2.i
  %brmerge5576 = or i1 %61, %_65.1.i
  br i1 %brmerge5576, label %bb20.i.split.loop.exit, label %bb8.i, !prof !21

bb8.i:                                            ; preds = %bb11.lr.ph.i.split
  %.sroa.02332.0.copyload23625519 = load <16 x i32>, ptr %_71.i266, align 4, !noalias !22
  %.sroa.02332.0.copyload23615520 = load <16 x i32>, ptr %_71.1.i, align 4, !noalias !22
  %.sroa.02332.0.copyload23605521 = load <16 x i32>, ptr %_71.2.i, align 4, !noalias !22
  %.sroa.02332.0.copyload23595522 = load <16 x i32>, ptr %_71.3.i, align 4, !noalias !22
  %.sroa.02332.0.copyload23585523 = load <16 x i32>, ptr %_71.4.i, align 4, !noalias !22
  %.sroa.02332.0.copyload23575524 = load <16 x i32>, ptr %_71.5.i, align 4, !noalias !22
  %.sroa.02332.0.copyload23565525 = load <16 x i32>, ptr %_71.6.i, align 4, !noalias !22
  %.sroa.02332.0.copyload23555526 = load <16 x i32>, ptr %_71.7.i, align 4, !noalias !22
  %.sroa.02332.0.copyload23545527 = load <16 x i32>, ptr %_71.8.i, align 4, !noalias !22
  %.sroa.02332.0.copyload23535528 = load <16 x i32>, ptr %_71.9.i, align 4, !noalias !22
  %.sroa.02332.0.copyload23525529 = load <16 x i32>, ptr %_71.10.i, align 4, !noalias !22
  %.sroa.02332.0.copyload23515530 = load <16 x i32>, ptr %_71.11.i, align 4, !noalias !22
  %.sroa.02332.0.copyload23505531 = load <16 x i32>, ptr %_71.12.i, align 4, !noalias !22
  %.sroa.02332.0.copyload23495532 = load <16 x i32>, ptr %_71.13.i, align 4, !noalias !22
  %.sroa.02332.0.copyload23485533 = load <16 x i32>, ptr %_71.14.i, align 4, !noalias !22
  %.sroa.02332.0.copyload5534 = load <16 x i32>, ptr %_71.15.i, align 4, !noalias !22
  %r.i639 = shufflevector <16 x i32> %.sroa.02332.0.copyload23625519, <16 x i32> %.sroa.02332.0.copyload23585523, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i638 = shufflevector <16 x i32> %.sroa.02332.0.copyload23615520, <16 x i32> %.sroa.02332.0.copyload23575524, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i637 = shufflevector <16 x i32> %.sroa.02332.0.copyload23605521, <16 x i32> %.sroa.02332.0.copyload23565525, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i636 = shufflevector <16 x i32> %.sroa.02332.0.copyload23595522, <16 x i32> %.sroa.02332.0.copyload23555526, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i635 = shufflevector <16 x i32> %.sroa.02332.0.copyload23625519, <16 x i32> %.sroa.02332.0.copyload23585523, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i634 = shufflevector <16 x i32> %.sroa.02332.0.copyload23615520, <16 x i32> %.sroa.02332.0.copyload23575524, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i633 = shufflevector <16 x i32> %.sroa.02332.0.copyload23605521, <16 x i32> %.sroa.02332.0.copyload23565525, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i632 = shufflevector <16 x i32> %.sroa.02332.0.copyload23595522, <16 x i32> %.sroa.02332.0.copyload23555526, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i631 = shufflevector <16 x i32> %.sroa.02332.0.copyload23545527, <16 x i32> %.sroa.02332.0.copyload23505531, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i630 = shufflevector <16 x i32> %.sroa.02332.0.copyload23535528, <16 x i32> %.sroa.02332.0.copyload23495532, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i629 = shufflevector <16 x i32> %.sroa.02332.0.copyload23525529, <16 x i32> %.sroa.02332.0.copyload23485533, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i628 = shufflevector <16 x i32> %.sroa.02332.0.copyload23515530, <16 x i32> %.sroa.02332.0.copyload5534, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i627 = shufflevector <16 x i32> %.sroa.02332.0.copyload23545527, <16 x i32> %.sroa.02332.0.copyload23505531, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i626 = shufflevector <16 x i32> %.sroa.02332.0.copyload23535528, <16 x i32> %.sroa.02332.0.copyload23495532, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i625 = shufflevector <16 x i32> %.sroa.02332.0.copyload23525529, <16 x i32> %.sroa.02332.0.copyload23485533, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i624 = shufflevector <16 x i32> %.sroa.02332.0.copyload23515530, <16 x i32> %.sroa.02332.0.copyload5534, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i623 = shufflevector <16 x i32> %r.i639, <16 x i32> %r.i631, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i622 = shufflevector <16 x i32> %r.i638, <16 x i32> %r.i630, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i621 = shufflevector <16 x i32> %r.i637, <16 x i32> %r.i629, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i620 = shufflevector <16 x i32> %r.i636, <16 x i32> %r.i628, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i619 = shufflevector <16 x i32> %r.i635, <16 x i32> %r.i627, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i618 = shufflevector <16 x i32> %r.i634, <16 x i32> %r.i626, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i617 = shufflevector <16 x i32> %r.i633, <16 x i32> %r.i625, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i616 = shufflevector <16 x i32> %r.i632, <16 x i32> %r.i624, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i615 = shufflevector <16 x i32> %r.i639, <16 x i32> %r.i631, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i614 = shufflevector <16 x i32> %r.i638, <16 x i32> %r.i630, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i613 = shufflevector <16 x i32> %r.i637, <16 x i32> %r.i629, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i612 = shufflevector <16 x i32> %r.i636, <16 x i32> %r.i628, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i611 = shufflevector <16 x i32> %r.i635, <16 x i32> %r.i627, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i610 = shufflevector <16 x i32> %r.i634, <16 x i32> %r.i626, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i609 = shufflevector <16 x i32> %r.i633, <16 x i32> %r.i625, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i608 = shufflevector <16 x i32> %r.i632, <16 x i32> %r.i624, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i607 = shufflevector <16 x i32> %r.i623, <16 x i32> %r.i621, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i606 = shufflevector <16 x i32> %r.i622, <16 x i32> %r.i620, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i605 = shufflevector <16 x i32> %r.i623, <16 x i32> %r.i621, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i604 = shufflevector <16 x i32> %r.i622, <16 x i32> %r.i620, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i603 = shufflevector <16 x i32> %r.i619, <16 x i32> %r.i617, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i602 = shufflevector <16 x i32> %r.i618, <16 x i32> %r.i616, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i601 = shufflevector <16 x i32> %r.i619, <16 x i32> %r.i617, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i600 = shufflevector <16 x i32> %r.i618, <16 x i32> %r.i616, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i599 = shufflevector <16 x i32> %r.i615, <16 x i32> %r.i613, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i598 = shufflevector <16 x i32> %r.i614, <16 x i32> %r.i612, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i597 = shufflevector <16 x i32> %r.i615, <16 x i32> %r.i613, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i596 = shufflevector <16 x i32> %r.i614, <16 x i32> %r.i612, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i595 = shufflevector <16 x i32> %r.i611, <16 x i32> %r.i609, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i594 = shufflevector <16 x i32> %r.i610, <16 x i32> %r.i608, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i593 = shufflevector <16 x i32> %r.i611, <16 x i32> %r.i609, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i592 = shufflevector <16 x i32> %r.i610, <16 x i32> %r.i608, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i591 = shufflevector <16 x i32> %r.i607, <16 x i32> %r.i606, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i590 = shufflevector <16 x i32> %r.i607, <16 x i32> %r.i606, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i589 = shufflevector <16 x i32> %r.i605, <16 x i32> %r.i604, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i588 = shufflevector <16 x i32> %r.i605, <16 x i32> %r.i604, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i587 = shufflevector <16 x i32> %r.i603, <16 x i32> %r.i602, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i586 = shufflevector <16 x i32> %r.i603, <16 x i32> %r.i602, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i585 = shufflevector <16 x i32> %r.i601, <16 x i32> %r.i600, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i584 = shufflevector <16 x i32> %r.i601, <16 x i32> %r.i600, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i583 = shufflevector <16 x i32> %r.i599, <16 x i32> %r.i598, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i582 = shufflevector <16 x i32> %r.i599, <16 x i32> %r.i598, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i581 = shufflevector <16 x i32> %r.i597, <16 x i32> %r.i596, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i580 = shufflevector <16 x i32> %r.i597, <16 x i32> %r.i596, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i579 = shufflevector <16 x i32> %r.i595, <16 x i32> %r.i594, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i578 = shufflevector <16 x i32> %r.i595, <16 x i32> %r.i594, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i577 = shufflevector <16 x i32> %r.i593, <16 x i32> %r.i592, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i576 = shufflevector <16 x i32> %r.i593, <16 x i32> %r.i592, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  store <16 x i32> %r.i591, ptr %m.i, align 64, !noalias !27
  store <16 x i32> %r.i590, ptr %m.i254.sroa.22.0.m.i.sroa_idx, align 64, !noalias !27
  store <16 x i32> %r.i589, ptr %m.i254.sroa.40.0.m.i.sroa_idx, align 64, !noalias !27
  store <16 x i32> %r.i588, ptr %m.i254.sroa.57.0.m.i.sroa_idx, align 64, !noalias !27
  store <16 x i32> %r.i587, ptr %m.i254.sroa.73.0.m.i.sroa_idx, align 64, !noalias !27
  store <16 x i32> %r.i586, ptr %m.i254.sroa.88.0.m.i.sroa_idx, align 64, !noalias !27
  store <16 x i32> %r.i585, ptr %m.i254.sroa.102.0.m.i.sroa_idx, align 64, !noalias !27
  store <16 x i32> %r.i584, ptr %m.i254.sroa.115.0.m.i.sroa_idx, align 64, !noalias !27
  store <16 x i32> %r.i583, ptr %m.i254.sroa.127.0.m.i.sroa_idx, align 64, !noalias !27
  store <16 x i32> %r.i582, ptr %m.i254.sroa.138.0.m.i.sroa_idx, align 64, !noalias !27
  store <16 x i32> %r.i581, ptr %m.i254.sroa.148.0.m.i.sroa_idx, align 64, !noalias !27
  store <16 x i32> %r.i580, ptr %m.i254.sroa.157.0.m.i.sroa_idx, align 64, !noalias !27
  store <16 x i32> %r.i579, ptr %m.i254.sroa.165.0.m.i.sroa_idx, align 64, !noalias !27
  store <16 x i32> %r.i578, ptr %m.i254.sroa.172.0.m.i.sroa_idx, align 64, !noalias !27
  store <16 x i32> %r.i577, ptr %m.i254.sroa.178.0.m.i.sroa_idx, align 64, !noalias !27
  store <16 x i32> %r.i576, ptr %m.i254.sroa.183.0.m.i.sroa_idx, align 64, !noalias !27
  %62 = trunc <16 x i8> %.fr to <16 x i1>
  %63 = bitcast <16 x i1> %62 to i16
  %.not = icmp eq i16 %63, 0
  br i1 %.not, label %bb24.i, label %bb23.i

bb20.i.split.loop.exit:                           ; preds = %bb11.lr.ph.i.split
  %_257.1.i.mux.le = select i1 %_65.14.i, i64 %_257.14.i, i64 %_257.15.i
  %_257.1.i.mux.mux.le = select i1 %_65.13.i, i64 %_257.13.i, i64 %_257.1.i.mux.le
  %_257.1.i.mux.mux.mux.le = select i1 %_65.12.i, i64 %_257.12.i, i64 %_257.1.i.mux.mux.le
  %_257.1.i.mux.mux.mux.mux.le = select i1 %_65.11.i, i64 %_257.11.i, i64 %_257.1.i.mux.mux.mux.le
  %_257.1.i.mux.mux.mux.mux.mux.le = select i1 %_65.10.i, i64 %_257.10.i, i64 %_257.1.i.mux.mux.mux.mux.le
  %_257.1.i.mux.mux.mux.mux.mux.mux.le = select i1 %_65.9.i, i64 %_257.9.i, i64 %_257.1.i.mux.mux.mux.mux.mux.le
  %_257.1.i.mux.mux.mux.mux.mux.mux.mux.le = select i1 %_65.8.i, i64 %_257.8.i, i64 %_257.1.i.mux.mux.mux.mux.mux.mux.le
  %_257.1.i.mux.mux.mux.mux.mux.mux.mux.mux.le = select i1 %_65.7.i, i64 %_257.7.i, i64 %_257.1.i.mux.mux.mux.mux.mux.mux.mux.le
  %_257.1.i.mux.mux.mux.mux.mux.mux.mux.mux.mux.le = select i1 %_65.6.i, i64 %_257.6.i, i64 %_257.1.i.mux.mux.mux.mux.mux.mux.mux.mux.le
  %_257.1.i.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.le = select i1 %_65.5.i, i64 %_257.5.i, i64 %_257.1.i.mux.mux.mux.mux.mux.mux.mux.mux.mux.le
  %_257.1.i.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.le = select i1 %_65.4.i, i64 %_257.4.i, i64 %_257.1.i.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.le
  %_257.1.i.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.le = select i1 %_65.3.i, i64 %_257.3.i, i64 %_257.1.i.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.le
  %_257.1.i.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.le = select i1 %_65.2.i, i64 %_257.2.i, i64 %_257.1.i.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.le
  %_257.1.i.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.le = select i1 %_65.1.i, i64 %_257.1.i, i64 %_257.1.i.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.le
  br label %bb20.i

bb20.i:                                           ; preds = %bb3.i, %bb20.i.split.loop.exit
  %.us-phi2745 = phi i64 [ %_257.1.i.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.mux.le, %bb20.i.split.loop.exit ], [ %_257.i, %bb3.i ]
; call core::slice::index::slice_index_fail
  tail call void @_RNvNtNtCsgxBkk5gSRhY_4core5slice5index16slice_index_fail(i64 noundef %.us-phi2745, i64 noundef 256, i64 noundef 256, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_83bddfce772813ac48c9037cf7b0770f) #12, !noalias !22
  unreachable

bb24.i:                                           ; preds = %bb8.i
  call void @llvm.lifetime.start.p0(ptr nonnull %root_m.i), !noalias !16
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 64 dereferenceable(1024) %root_m.i, ptr noundef nonnull align 64 dereferenceable(1024) %m.i, i64 1024, i1 false), !noalias !16
  call void @llvm.lifetime.end.p0(ptr nonnull %m.i), !noalias !16
  %64 = bitcast <8 x i64> %block_sz.i.sroa.0.32.vecblend to <16 x i32>
  %65 = bitcast <8 x i64> %block_flags.i.sroa.0.32.vecblend to <16 x i32>
  br label %bb70.i

bb23.i:                                           ; preds = %bb8.i
  %66 = bitcast <8 x i64> %block_sz.i.sroa.0.32.vecblend to <16 x i32>
  %67 = bitcast <8 x i64> %block_flags.i.sroa.0.32.vecblend to <16 x i32>
  br label %bb3.i.i

bb3.i.i:                                          ; preds = %bb23.i, %bb3.i.i
  %iter.sroa.0.0.i.i4875 = phi i64 [ 0, %bb23.i ], [ %82, %bb3.i.i ]
  %68 = phi <16 x i32> [ %24, %bb23.i ], [ %_3.i344, %bb3.i.i ]
  %69 = phi <16 x i32> [ %23, %bb23.i ], [ %_3.i358, %bb3.i.i ]
  %70 = phi <16 x i32> [ %22, %bb23.i ], [ %_3.i372, %bb3.i.i ]
  %71 = phi <16 x i32> [ %21, %bb23.i ], [ %_3.i386, %bb3.i.i ]
  %72 = phi <16 x i32> [ %20, %bb23.i ], [ %_3.i.i391, %bb3.i.i ]
  %73 = phi <16 x i32> [ %19, %bb23.i ], [ %_3.i.i349, %bb3.i.i ]
  %74 = phi <16 x i32> [ %18, %bb23.i ], [ %_3.i.i363, %bb3.i.i ]
  %75 = phi <16 x i32> [ %17, %bb23.i ], [ %_3.i.i377, %bb3.i.i ]
  %76 = phi <16 x i32> [ splat (i32 1779033703), %bb23.i ], [ %_3.i375, %bb3.i.i ]
  %77 = phi <16 x i32> [ splat (i32 -1150833019), %bb23.i ], [ %_3.i389, %bb3.i.i ]
  %78 = phi <16 x i32> [ splat (i32 1013904242), %bb23.i ], [ %_3.i347, %bb3.i.i ]
  %79 = phi <16 x i32> [ splat (i32 -1521486534), %bb23.i ], [ %_3.i361, %bb3.i.i ]
  %80 = phi <16 x i32> [ zeroinitializer, %bb23.i ], [ %_3.i.i360, %bb3.i.i ]
  %81 = phi <16 x i32> [ zeroinitializer, %bb23.i ], [ %_3.i.i374, %bb3.i.i ]
  %v.i.i.sroa.137.04874 = phi <16 x i32> [ %66, %bb23.i ], [ %_3.i.i388, %bb3.i.i ]
  %v.i.i.sroa.146.04873 = phi <16 x i32> [ %67, %bb23.i ], [ %_3.i.i346, %bb3.i.i ]
  %82 = add nuw nsw i64 %iter.sroa.0.0.i.i4875, 1
  tail call void @llvm.experimental.noalias.scope.decl(metadata !28)
  %s.i1 = getelementptr inbounds nuw [16 x i64], ptr @alloc_61fb4a9344bbdaf2573accd6331d7e32, i64 %iter.sroa.0.0.i.i4875
  %83 = getelementptr inbounds nuw i8, ptr %s.i1, i64 8
  %_11.i = load i64, ptr %83, align 8, !noalias !31, !noundef !41
  %_8.i = load i64, ptr %s.i1, align 8, !noalias !31, !noundef !41
  %84 = getelementptr inbounds nuw <8 x i64>, ptr %m.i, i64 %_8.i
  %_7.i2692 = load <16 x i32>, ptr %84, align 64, !alias.scope !28, !noalias !42
  %85 = getelementptr inbounds nuw <8 x i64>, ptr %m.i, i64 %_11.i
  %_10.i2693 = load <16 x i32>, ptr %85, align 64, !alias.scope !28, !noalias !42
  %_3.i = add <16 x i32> %68, %72
  %_3.i282 = add <16 x i32> %_3.i, %_7.i2692
  %_3.i283 = xor <16 x i32> %_3.i282, %80
  %_3.i.i = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i283, <16 x i32> %_3.i283, <16 x i32> splat (i32 16))
  %_3.i284 = add <16 x i32> %_3.i.i, %76
  %_3.i285 = xor <16 x i32> %_3.i284, %72
  %_3.i.i286 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i285, <16 x i32> %_3.i285, <16 x i32> splat (i32 20))
  %_3.i287 = add <16 x i32> %_10.i2693, %_3.i282
  %_3.i288 = add <16 x i32> %_3.i287, %_3.i.i286
  %_3.i289 = xor <16 x i32> %_3.i288, %_3.i.i
  %_3.i.i290 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i289, <16 x i32> %_3.i289, <16 x i32> splat (i32 24))
  %_3.i291 = add <16 x i32> %_3.i.i290, %_3.i284
  %_3.i292 = xor <16 x i32> %_3.i291, %_3.i.i286
  %_3.i.i293 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i292, <16 x i32> %_3.i292, <16 x i32> splat (i32 25))
  %86 = getelementptr inbounds nuw i8, ptr %s.i1, i64 24
  %_18.i = load i64, ptr %86, align 8, !noalias !31, !noundef !41
  %87 = getelementptr inbounds nuw i8, ptr %s.i1, i64 16
  %_15.i = load i64, ptr %87, align 8, !noalias !31, !noundef !41
  %88 = getelementptr inbounds nuw <8 x i64>, ptr %m.i, i64 %_15.i
  %_14.i2696 = load <16 x i32>, ptr %88, align 64, !alias.scope !28, !noalias !42
  %89 = getelementptr inbounds nuw <8 x i64>, ptr %m.i, i64 %_18.i
  %_17.i2697 = load <16 x i32>, ptr %89, align 64, !alias.scope !28, !noalias !42
  %_3.i294 = add <16 x i32> %69, %73
  %_3.i295 = add <16 x i32> %_3.i294, %_14.i2696
  %_3.i296 = xor <16 x i32> %_3.i295, %81
  %_3.i.i297 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i296, <16 x i32> %_3.i296, <16 x i32> splat (i32 16))
  %_3.i298 = add <16 x i32> %_3.i.i297, %77
  %_3.i299 = xor <16 x i32> %_3.i298, %73
  %_3.i.i300 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i299, <16 x i32> %_3.i299, <16 x i32> splat (i32 20))
  %_3.i301 = add <16 x i32> %_17.i2697, %_3.i295
  %_3.i302 = add <16 x i32> %_3.i301, %_3.i.i300
  %_3.i303 = xor <16 x i32> %_3.i302, %_3.i.i297
  %_3.i.i304 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i303, <16 x i32> %_3.i303, <16 x i32> splat (i32 24))
  %_3.i305 = add <16 x i32> %_3.i.i304, %_3.i298
  %_3.i306 = xor <16 x i32> %_3.i305, %_3.i.i300
  %_3.i.i307 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i306, <16 x i32> %_3.i306, <16 x i32> splat (i32 25))
  %90 = getelementptr inbounds nuw i8, ptr %s.i1, i64 40
  %_25.i = load i64, ptr %90, align 8, !noalias !31, !noundef !41
  %91 = getelementptr inbounds nuw i8, ptr %s.i1, i64 32
  %_22.i = load i64, ptr %91, align 8, !noalias !31, !noundef !41
  %92 = getelementptr inbounds nuw <8 x i64>, ptr %m.i, i64 %_22.i
  %_21.i2700 = load <16 x i32>, ptr %92, align 64, !alias.scope !28, !noalias !42
  %93 = getelementptr inbounds nuw <8 x i64>, ptr %m.i, i64 %_25.i
  %_24.i22701 = load <16 x i32>, ptr %93, align 64, !alias.scope !28, !noalias !42
  %_3.i308 = add <16 x i32> %70, %74
  %_3.i309 = add <16 x i32> %_3.i308, %_21.i2700
  %_3.i310 = xor <16 x i32> %_3.i309, %v.i.i.sroa.137.04874
  %_3.i.i311 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i310, <16 x i32> %_3.i310, <16 x i32> splat (i32 16))
  %_3.i312 = add <16 x i32> %_3.i.i311, %78
  %_3.i313 = xor <16 x i32> %_3.i312, %74
  %_3.i.i314 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i313, <16 x i32> %_3.i313, <16 x i32> splat (i32 20))
  %_3.i315 = add <16 x i32> %_24.i22701, %_3.i309
  %_3.i316 = add <16 x i32> %_3.i315, %_3.i.i314
  %_3.i317 = xor <16 x i32> %_3.i316, %_3.i.i311
  %_3.i.i318 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i317, <16 x i32> %_3.i317, <16 x i32> splat (i32 24))
  %_3.i319 = add <16 x i32> %_3.i.i318, %_3.i312
  %_3.i320 = xor <16 x i32> %_3.i319, %_3.i.i314
  %_3.i.i321 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i320, <16 x i32> %_3.i320, <16 x i32> splat (i32 25))
  %94 = getelementptr inbounds nuw i8, ptr %s.i1, i64 56
  %_32.i = load i64, ptr %94, align 8, !noalias !31, !noundef !41
  %95 = getelementptr inbounds nuw i8, ptr %s.i1, i64 48
  %_29.i = load i64, ptr %95, align 8, !noalias !31, !noundef !41
  %96 = getelementptr inbounds nuw <8 x i64>, ptr %m.i, i64 %_29.i
  %_28.i32704 = load <16 x i32>, ptr %96, align 64, !alias.scope !28, !noalias !42
  %97 = getelementptr inbounds nuw <8 x i64>, ptr %m.i, i64 %_32.i
  %_31.i2705 = load <16 x i32>, ptr %97, align 64, !alias.scope !28, !noalias !42
  %_3.i322 = add <16 x i32> %71, %75
  %_3.i323 = add <16 x i32> %_3.i322, %_28.i32704
  %_3.i324 = xor <16 x i32> %_3.i323, %v.i.i.sroa.146.04873
  %_3.i.i325 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i324, <16 x i32> %_3.i324, <16 x i32> splat (i32 16))
  %_3.i326 = add <16 x i32> %_3.i.i325, %79
  %_3.i327 = xor <16 x i32> %_3.i326, %75
  %_3.i.i328 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i327, <16 x i32> %_3.i327, <16 x i32> splat (i32 20))
  %_3.i329 = add <16 x i32> %_31.i2705, %_3.i323
  %_3.i330 = add <16 x i32> %_3.i329, %_3.i.i328
  %_3.i331 = xor <16 x i32> %_3.i330, %_3.i.i325
  %_3.i.i332 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i331, <16 x i32> %_3.i331, <16 x i32> splat (i32 24))
  %_3.i333 = add <16 x i32> %_3.i.i332, %_3.i326
  %_3.i334 = xor <16 x i32> %_3.i333, %_3.i.i328
  %_3.i.i335 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i334, <16 x i32> %_3.i334, <16 x i32> splat (i32 25))
  %98 = getelementptr inbounds nuw i8, ptr %s.i1, i64 72
  %_39.i = load i64, ptr %98, align 8, !noalias !31, !noundef !41
  %99 = getelementptr inbounds nuw i8, ptr %s.i1, i64 64
  %_36.i = load i64, ptr %99, align 8, !noalias !31, !noundef !41
  %100 = getelementptr inbounds nuw <8 x i64>, ptr %m.i, i64 %_36.i
  %_35.i42708 = load <16 x i32>, ptr %100, align 64, !alias.scope !28, !noalias !42
  %101 = getelementptr inbounds nuw <8 x i64>, ptr %m.i, i64 %_39.i
  %_38.i2709 = load <16 x i32>, ptr %101, align 64, !alias.scope !28, !noalias !42
  %_3.i336 = add <16 x i32> %_35.i42708, %_3.i288
  %_3.i337 = add <16 x i32> %_3.i336, %_3.i.i307
  %_3.i338 = xor <16 x i32> %_3.i.i332, %_3.i337
  %_3.i.i339 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i338, <16 x i32> %_3.i338, <16 x i32> splat (i32 16))
  %_3.i340 = add <16 x i32> %_3.i.i339, %_3.i319
  %_3.i341 = xor <16 x i32> %_3.i340, %_3.i.i307
  %_3.i.i342 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i341, <16 x i32> %_3.i341, <16 x i32> splat (i32 20))
  %_3.i343 = add <16 x i32> %_3.i337, %_38.i2709
  %_3.i344 = add <16 x i32> %_3.i343, %_3.i.i342
  %_3.i345 = xor <16 x i32> %_3.i344, %_3.i.i339
  %_3.i.i346 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i345, <16 x i32> %_3.i345, <16 x i32> splat (i32 24))
  %_3.i347 = add <16 x i32> %_3.i.i346, %_3.i340
  %_3.i348 = xor <16 x i32> %_3.i347, %_3.i.i342
  %_3.i.i349 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i348, <16 x i32> %_3.i348, <16 x i32> splat (i32 25))
  %102 = getelementptr inbounds nuw i8, ptr %s.i1, i64 88
  %_46.i = load i64, ptr %102, align 8, !noalias !31, !noundef !41
  %103 = getelementptr inbounds nuw i8, ptr %s.i1, i64 80
  %_43.i = load i64, ptr %103, align 8, !noalias !31, !noundef !41
  %104 = getelementptr inbounds nuw <8 x i64>, ptr %m.i, i64 %_43.i
  %_42.i2710 = load <16 x i32>, ptr %104, align 64, !alias.scope !28, !noalias !42
  %105 = getelementptr inbounds nuw <8 x i64>, ptr %m.i, i64 %_46.i
  %_45.i2711 = load <16 x i32>, ptr %105, align 64, !alias.scope !28, !noalias !42
  %_3.i350 = add <16 x i32> %_42.i2710, %_3.i302
  %_3.i351 = add <16 x i32> %_3.i350, %_3.i.i321
  %_3.i352 = xor <16 x i32> %_3.i351, %_3.i.i290
  %_3.i.i353 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i352, <16 x i32> %_3.i352, <16 x i32> splat (i32 16))
  %_3.i354 = add <16 x i32> %_3.i.i353, %_3.i333
  %_3.i355 = xor <16 x i32> %_3.i354, %_3.i.i321
  %_3.i.i356 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i355, <16 x i32> %_3.i355, <16 x i32> splat (i32 20))
  %_3.i357 = add <16 x i32> %_3.i351, %_45.i2711
  %_3.i358 = add <16 x i32> %_3.i357, %_3.i.i356
  %_3.i359 = xor <16 x i32> %_3.i358, %_3.i.i353
  %_3.i.i360 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i359, <16 x i32> %_3.i359, <16 x i32> splat (i32 24))
  %_3.i361 = add <16 x i32> %_3.i.i360, %_3.i354
  %_3.i362 = xor <16 x i32> %_3.i361, %_3.i.i356
  %_3.i.i363 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i362, <16 x i32> %_3.i362, <16 x i32> splat (i32 25))
  %106 = getelementptr inbounds nuw i8, ptr %s.i1, i64 104
  %_53.i = load i64, ptr %106, align 8, !noalias !31, !noundef !41
  %107 = getelementptr inbounds nuw i8, ptr %s.i1, i64 96
  %_50.i6 = load i64, ptr %107, align 8, !noalias !31, !noundef !41
  %108 = getelementptr inbounds nuw <8 x i64>, ptr %m.i, i64 %_50.i6
  %_49.i2712 = load <16 x i32>, ptr %108, align 64, !alias.scope !28, !noalias !42
  %109 = getelementptr inbounds nuw <8 x i64>, ptr %m.i, i64 %_53.i
  %_52.i72713 = load <16 x i32>, ptr %109, align 64, !alias.scope !28, !noalias !42
  %_3.i364 = add <16 x i32> %_49.i2712, %_3.i316
  %_3.i365 = add <16 x i32> %_3.i364, %_3.i.i335
  %_3.i366 = xor <16 x i32> %_3.i365, %_3.i.i304
  %_3.i.i367 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i366, <16 x i32> %_3.i366, <16 x i32> splat (i32 16))
  %_3.i368 = add <16 x i32> %_3.i.i367, %_3.i291
  %_3.i369 = xor <16 x i32> %_3.i368, %_3.i.i335
  %_3.i.i370 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i369, <16 x i32> %_3.i369, <16 x i32> splat (i32 20))
  %_3.i371 = add <16 x i32> %_3.i365, %_52.i72713
  %_3.i372 = add <16 x i32> %_3.i371, %_3.i.i370
  %_3.i373 = xor <16 x i32> %_3.i372, %_3.i.i367
  %_3.i.i374 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i373, <16 x i32> %_3.i373, <16 x i32> splat (i32 24))
  %_3.i375 = add <16 x i32> %_3.i.i374, %_3.i368
  %_3.i376 = xor <16 x i32> %_3.i375, %_3.i.i370
  %_3.i.i377 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i376, <16 x i32> %_3.i376, <16 x i32> splat (i32 25))
  %110 = getelementptr inbounds nuw i8, ptr %s.i1, i64 120
  %_60.i = load i64, ptr %110, align 8, !noalias !31, !noundef !41
  %111 = getelementptr inbounds nuw i8, ptr %s.i1, i64 112
  %_57.i8 = load i64, ptr %111, align 8, !noalias !31, !noundef !41
  %112 = getelementptr inbounds nuw <8 x i64>, ptr %m.i, i64 %_57.i8
  %_56.i2714 = load <16 x i32>, ptr %112, align 64, !alias.scope !28, !noalias !42
  %113 = getelementptr inbounds nuw <8 x i64>, ptr %m.i, i64 %_60.i
  %_59.i2715 = load <16 x i32>, ptr %113, align 64, !alias.scope !28, !noalias !42
  %_3.i378 = add <16 x i32> %_3.i330, %_3.i.i293
  %_3.i379 = add <16 x i32> %_3.i378, %_56.i2714
  %_3.i380 = xor <16 x i32> %_3.i379, %_3.i.i318
  %_3.i.i381 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i380, <16 x i32> %_3.i380, <16 x i32> splat (i32 16))
  %_3.i382 = add <16 x i32> %_3.i.i381, %_3.i305
  %_3.i383 = xor <16 x i32> %_3.i382, %_3.i.i293
  %_3.i.i384 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i383, <16 x i32> %_3.i383, <16 x i32> splat (i32 20))
  %_3.i385 = add <16 x i32> %_59.i2715, %_3.i379
  %_3.i386 = add <16 x i32> %_3.i385, %_3.i.i384
  %_3.i387 = xor <16 x i32> %_3.i386, %_3.i.i381
  %_3.i.i388 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i387, <16 x i32> %_3.i387, <16 x i32> splat (i32 24))
  %_3.i389 = add <16 x i32> %_3.i.i388, %_3.i382
  %_3.i390 = xor <16 x i32> %_3.i389, %_3.i.i384
  %_3.i.i391 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i390, <16 x i32> %_3.i390, <16 x i32> splat (i32 25))
  %exitcond5449.not = icmp eq i64 %82, 7
  br i1 %exitcond5449.not, label %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i, label %bb3.i.i

_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit.i: ; preds = %bb3.i.i
  %active.i.sroa.0.0.vec.extract = extractelement <16 x i8> %.fr, i64 0
  %active.i.sroa.0.1.vec.extract = extractelement <16 x i8> %.fr, i64 1
  %114 = shl nuw nsw i8 %active.i.sroa.0.1.vec.extract, 1
  %115 = or disjoint i8 %114, %active.i.sroa.0.0.vec.extract
  %active.i.sroa.0.2.vec.extract = extractelement <16 x i8> %.fr, i64 2
  %116 = shl nuw nsw i8 %active.i.sroa.0.2.vec.extract, 2
  %117 = or disjoint i8 %116, %115
  %active.i.sroa.0.3.vec.extract = extractelement <16 x i8> %.fr, i64 3
  %118 = shl nuw nsw i8 %active.i.sroa.0.3.vec.extract, 3
  %119 = or disjoint i8 %118, %117
  %active.i.sroa.0.4.vec.extract = extractelement <16 x i8> %.fr, i64 4
  %120 = shl nuw nsw i8 %active.i.sroa.0.4.vec.extract, 4
  %121 = or disjoint i8 %120, %119
  %active.i.sroa.0.5.vec.extract = extractelement <16 x i8> %.fr, i64 5
  %122 = shl nuw nsw i8 %active.i.sroa.0.5.vec.extract, 5
  %123 = or i8 %122, %121
  %active.i.sroa.0.6.vec.extract = extractelement <16 x i8> %.fr, i64 6
  %124 = shl nuw nsw i8 %active.i.sroa.0.6.vec.extract, 6
  %125 = or i8 %124, %123
  %active.i.sroa.0.7.vec.extract = extractelement <16 x i8> %.fr, i64 7
  %126 = shl nuw i8 %active.i.sroa.0.7.vec.extract, 7
  %127 = or i8 %126, %125
  %128 = zext i8 %127 to i16
  %active.i.sroa.0.8.vec.extract = extractelement <16 x i8> %.fr, i64 8
  %a.i.8 = zext nneg i8 %active.i.sroa.0.8.vec.extract to i16
  %_10.i237.8 = shl nuw nsw i16 %a.i.8, 8
  %129 = or disjoint i16 %_10.i237.8, %128
  %active.i.sroa.0.9.vec.extract = extractelement <16 x i8> %.fr, i64 9
  %a.i.9 = zext nneg i8 %active.i.sroa.0.9.vec.extract to i16
  %_10.i237.9 = shl nuw nsw i16 %a.i.9, 9
  %130 = or disjoint i16 %_10.i237.9, %129
  %active.i.sroa.0.10.vec.extract = extractelement <16 x i8> %.fr, i64 10
  %a.i.10 = zext nneg i8 %active.i.sroa.0.10.vec.extract to i16
  %_10.i237.10 = shl nuw nsw i16 %a.i.10, 10
  %131 = or disjoint i16 %_10.i237.10, %130
  %active.i.sroa.0.11.vec.extract = extractelement <16 x i8> %.fr, i64 11
  %a.i.11 = zext nneg i8 %active.i.sroa.0.11.vec.extract to i16
  %_10.i237.11 = shl nuw nsw i16 %a.i.11, 11
  %132 = or i16 %_10.i237.11, %131
  %active.i.sroa.0.12.vec.extract = extractelement <16 x i8> %.fr, i64 12
  %a.i.12 = zext nneg i8 %active.i.sroa.0.12.vec.extract to i16
  %_10.i237.12 = shl nuw nsw i16 %a.i.12, 12
  %133 = or i16 %_10.i237.12, %132
  %active.i.sroa.0.13.vec.extract = extractelement <16 x i8> %.fr, i64 13
  %a.i.13 = zext nneg i8 %active.i.sroa.0.13.vec.extract to i16
  %_10.i237.13 = shl nuw nsw i16 %a.i.13, 13
  %134 = or i16 %_10.i237.13, %133
  %active.i.sroa.0.14.vec.extract = extractelement <16 x i8> %.fr, i64 14
  %a.i.14 = zext nneg i8 %active.i.sroa.0.14.vec.extract to i16
  %_10.i237.14 = shl nuw nsw i16 %a.i.14, 14
  %135 = or i16 %_10.i237.14, %134
  %active.i.sroa.0.15.vec.extract = extractelement <16 x i8> %.fr, i64 15
  %a.i.15 = zext nneg i8 %active.i.sroa.0.15.vec.extract to i16
  %_10.i237.15 = shl nuw i16 %a.i.15, 15
  %136 = or i16 %_10.i237.15, %135
  %137 = bitcast i16 %136 to <16 x i1>
  %_3.i574 = xor <16 x i32> %_3.i375, %_3.i344
  %_4.i575 = select <16 x i1> %137, <16 x i32> %_3.i574, <16 x i32> %24
  %_3.i574.1 = xor <16 x i32> %_3.i389, %_3.i358
  %_4.i575.1 = select <16 x i1> %137, <16 x i32> %_3.i574.1, <16 x i32> %23
  %_3.i574.2 = xor <16 x i32> %_3.i347, %_3.i372
  %_4.i575.2 = select <16 x i1> %137, <16 x i32> %_3.i574.2, <16 x i32> %22
  %_3.i574.3 = xor <16 x i32> %_3.i361, %_3.i386
  %_4.i575.3 = select <16 x i1> %137, <16 x i32> %_3.i574.3, <16 x i32> %21
  %_3.i574.4 = xor <16 x i32> %_3.i.i360, %_3.i.i391
  %_4.i575.4 = select <16 x i1> %137, <16 x i32> %_3.i574.4, <16 x i32> %20
  %_3.i574.5 = xor <16 x i32> %_3.i.i374, %_3.i.i349
  %_4.i575.5 = select <16 x i1> %137, <16 x i32> %_3.i574.5, <16 x i32> %19
  %_3.i574.6 = xor <16 x i32> %_3.i.i388, %_3.i.i363
  %_4.i575.6 = select <16 x i1> %137, <16 x i32> %_3.i574.6, <16 x i32> %18
  %_3.i574.7 = xor <16 x i32> %_3.i.i346, %_3.i.i377
  %_4.i575.7 = select <16 x i1> %137, <16 x i32> %_3.i574.7, <16 x i32> %17
  %138 = bitcast <16 x i8> %.fr to <128 x i1>
  %_75.i = extractelement <128 x i1> %138, i64 0
  %139 = add nuw nsw i64 %16, 64
  %off.i.sroa.0.0.vec.insert = insertelement <8 x i64> %off.i.sroa.0.0, i64 %139, i64 0
  %off.i.sroa.0.1 = select i1 %_75.i, <8 x i64> %off.i.sroa.0.0.vec.insert, <8 x i64> %off.i.sroa.0.0
  %140 = select i1 %_75.i, i64 %139, i64 %16
  %141 = bitcast <16 x i8> %.fr to <128 x i1>
  %_75.i.1 = extractelement <128 x i1> %141, i64 8
  %142 = add nuw nsw i64 %15, 64
  %off.i.sroa.0.8.vec.insert = insertelement <8 x i64> %off.i.sroa.0.1, i64 %142, i64 1
  %off.i.sroa.0.2 = select i1 %_75.i.1, <8 x i64> %off.i.sroa.0.8.vec.insert, <8 x i64> %off.i.sroa.0.1
  %143 = select i1 %_75.i.1, i64 %142, i64 %15
  %_75.i.2 = trunc nuw i8 %active.i.sroa.0.2.vec.extract to i1
  %144 = add nuw nsw i64 %14, 64
  %off.i.sroa.0.16.vec.insert = insertelement <8 x i64> %off.i.sroa.0.2, i64 %144, i64 2
  %off.i.sroa.0.3 = select i1 %_75.i.2, <8 x i64> %off.i.sroa.0.16.vec.insert, <8 x i64> %off.i.sroa.0.2
  %145 = select i1 %_75.i.2, i64 %144, i64 %14
  %_75.i.3 = trunc nuw i8 %active.i.sroa.0.3.vec.extract to i1
  %146 = add nuw nsw i64 %13, 64
  %off.i.sroa.0.24.vec.insert = insertelement <8 x i64> %off.i.sroa.0.3, i64 %146, i64 3
  %off.i.sroa.0.4 = select i1 %_75.i.3, <8 x i64> %off.i.sroa.0.24.vec.insert, <8 x i64> %off.i.sroa.0.3
  %147 = select i1 %_75.i.3, i64 %146, i64 %13
  %_75.i.4 = trunc nuw i8 %active.i.sroa.0.4.vec.extract to i1
  %148 = add nuw nsw i64 %12, 64
  %off.i.sroa.0.32.vec.insert = insertelement <8 x i64> %off.i.sroa.0.4, i64 %148, i64 4
  %off.i.sroa.0.5 = select i1 %_75.i.4, <8 x i64> %off.i.sroa.0.32.vec.insert, <8 x i64> %off.i.sroa.0.4
  %149 = select i1 %_75.i.4, i64 %148, i64 %12
  %_75.i.5 = trunc nuw i8 %active.i.sroa.0.5.vec.extract to i1
  %150 = add nuw nsw i64 %11, 64
  %off.i.sroa.0.40.vec.insert = insertelement <8 x i64> %off.i.sroa.0.5, i64 %150, i64 5
  %off.i.sroa.0.6 = select i1 %_75.i.5, <8 x i64> %off.i.sroa.0.40.vec.insert, <8 x i64> %off.i.sroa.0.5
  %151 = select i1 %_75.i.5, i64 %150, i64 %11
  %_75.i.6 = trunc nuw i8 %active.i.sroa.0.6.vec.extract to i1
  %152 = add nuw nsw i64 %10, 64
  %off.i.sroa.0.48.vec.insert = insertelement <8 x i64> %off.i.sroa.0.6, i64 %152, i64 6
  %off.i.sroa.0.7 = select i1 %_75.i.6, <8 x i64> %off.i.sroa.0.48.vec.insert, <8 x i64> %off.i.sroa.0.6
  %153 = select i1 %_75.i.6, i64 %152, i64 %10
  %_75.i.7 = trunc nuw i8 %active.i.sroa.0.7.vec.extract to i1
  %154 = add i64 %9, 64
  %off.i.sroa.0.56.vec.insert = insertelement <8 x i64> %off.i.sroa.0.7, i64 %154, i64 7
  %off.i.sroa.0.8 = select i1 %_75.i.7, <8 x i64> %off.i.sroa.0.56.vec.insert, <8 x i64> %off.i.sroa.0.7
  %155 = select i1 %_75.i.7, i64 %154, i64 %9
  %_75.i.8 = trunc nuw i8 %active.i.sroa.0.8.vec.extract to i1
  %156 = add i64 %8, 64
  %off.i.sroa.20.64.vec.insert = insertelement <8 x i64> %off.i.sroa.20.0, i64 %156, i64 0
  %off.i.sroa.20.1 = select i1 %_75.i.8, <8 x i64> %off.i.sroa.20.64.vec.insert, <8 x i64> %off.i.sroa.20.0
  %157 = select i1 %_75.i.8, i64 %156, i64 %8
  %_75.i.9 = trunc nuw i8 %active.i.sroa.0.9.vec.extract to i1
  %158 = add i64 %7, 64
  %off.i.sroa.20.72.vec.insert = insertelement <8 x i64> %off.i.sroa.20.1, i64 %158, i64 1
  %off.i.sroa.20.2 = select i1 %_75.i.9, <8 x i64> %off.i.sroa.20.72.vec.insert, <8 x i64> %off.i.sroa.20.1
  %159 = select i1 %_75.i.9, i64 %158, i64 %7
  %_75.i.10 = trunc nuw i8 %active.i.sroa.0.10.vec.extract to i1
  %160 = add i64 %6, 64
  %off.i.sroa.20.80.vec.insert = insertelement <8 x i64> %off.i.sroa.20.2, i64 %160, i64 2
  %off.i.sroa.20.3 = select i1 %_75.i.10, <8 x i64> %off.i.sroa.20.80.vec.insert, <8 x i64> %off.i.sroa.20.2
  %161 = select i1 %_75.i.10, i64 %160, i64 %6
  %_75.i.11 = trunc nuw i8 %active.i.sroa.0.11.vec.extract to i1
  %162 = add i64 %5, 64
  %off.i.sroa.20.88.vec.insert = insertelement <8 x i64> %off.i.sroa.20.3, i64 %162, i64 3
  %off.i.sroa.20.4 = select i1 %_75.i.11, <8 x i64> %off.i.sroa.20.88.vec.insert, <8 x i64> %off.i.sroa.20.3
  %163 = select i1 %_75.i.11, i64 %162, i64 %5
  %_75.i.12 = trunc nuw i8 %active.i.sroa.0.12.vec.extract to i1
  %164 = add i64 %4, 64
  %off.i.sroa.20.96.vec.insert = insertelement <8 x i64> %off.i.sroa.20.4, i64 %164, i64 4
  %off.i.sroa.20.5 = select i1 %_75.i.12, <8 x i64> %off.i.sroa.20.96.vec.insert, <8 x i64> %off.i.sroa.20.4
  %165 = select i1 %_75.i.12, i64 %164, i64 %4
  %_75.i.13 = trunc nuw i8 %active.i.sroa.0.13.vec.extract to i1
  %166 = add i64 %3, 64
  %off.i.sroa.20.104.vec.insert = insertelement <8 x i64> %off.i.sroa.20.5, i64 %166, i64 5
  %off.i.sroa.20.6 = select i1 %_75.i.13, <8 x i64> %off.i.sroa.20.104.vec.insert, <8 x i64> %off.i.sroa.20.5
  %167 = select i1 %_75.i.13, i64 %166, i64 %3
  %_75.i.14 = trunc nuw i8 %active.i.sroa.0.14.vec.extract to i1
  %168 = add i64 %2, 64
  %off.i.sroa.20.112.vec.insert = insertelement <8 x i64> %off.i.sroa.20.6, i64 %168, i64 6
  %off.i.sroa.20.7 = select i1 %_75.i.14, <8 x i64> %off.i.sroa.20.112.vec.insert, <8 x i64> %off.i.sroa.20.6
  %169 = select i1 %_75.i.14, i64 %168, i64 %2
  %_75.i.15 = trunc nuw i8 %active.i.sroa.0.15.vec.extract to i1
  %170 = add i64 %1, 64
  %off.i.sroa.20.120.vec.insert = insertelement <8 x i64> %off.i.sroa.20.7, i64 %170, i64 7
  %off.i.sroa.20.8 = select i1 %_75.i.15, <8 x i64> %off.i.sroa.20.120.vec.insert, <8 x i64> %off.i.sroa.20.7
  %171 = select i1 %_75.i.15, i64 %170, i64 %1
  call void @llvm.lifetime.end.p0(ptr nonnull %m.i), !noalias !16
  br label %bb3.i

bb70.i:                                           ; preds = %bb24.i, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit58.i
  %iter4.sroa.0.0.i4920 = phi i64 [ 0, %bb24.i ], [ %235, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit58.i ]
  %_87.i = trunc nuw nsw i64 %iter4.sroa.0.0.i4920 to i32
  %172 = insertelement <16 x i32> poison, i32 %_87.i, i64 0
  %173 = shufflevector <16 x i32> %172, <16 x i32> poison, <16 x i32> zeroinitializer
  br label %bb3.i57.i

bb3.i57.i:                                        ; preds = %bb70.i, %bb3.i57.i
  %iter.sroa.0.0.i55.i4884 = phi i64 [ 0, %bb70.i ], [ %187, %bb3.i57.i ]
  %174 = phi <16 x i32> [ %24, %bb70.i ], [ %_3.i459, %bb3.i57.i ]
  %175 = phi <16 x i32> [ %23, %bb70.i ], [ %_3.i473, %bb3.i57.i ]
  %176 = phi <16 x i32> [ %22, %bb70.i ], [ %_3.i487, %bb3.i57.i ]
  %177 = phi <16 x i32> [ %21, %bb70.i ], [ %_3.i501, %bb3.i57.i ]
  %178 = phi <16 x i32> [ %20, %bb70.i ], [ %_3.i.i506, %bb3.i57.i ]
  %179 = phi <16 x i32> [ %19, %bb70.i ], [ %_3.i.i464, %bb3.i57.i ]
  %180 = phi <16 x i32> [ %18, %bb70.i ], [ %_3.i.i478, %bb3.i57.i ]
  %181 = phi <16 x i32> [ %17, %bb70.i ], [ %_3.i.i492, %bb3.i57.i ]
  %182 = phi <16 x i32> [ splat (i32 1779033703), %bb70.i ], [ %_3.i490, %bb3.i57.i ]
  %183 = phi <16 x i32> [ splat (i32 -1150833019), %bb70.i ], [ %_3.i504, %bb3.i57.i ]
  %184 = phi <16 x i32> [ splat (i32 1013904242), %bb70.i ], [ %_3.i462, %bb3.i57.i ]
  %185 = phi <16 x i32> [ splat (i32 -1521486534), %bb70.i ], [ %_3.i476, %bb3.i57.i ]
  %v.i41.i.sroa.119.0.in4883 = phi <16 x i32> [ %173, %bb70.i ], [ %_3.i.i475, %bb3.i57.i ]
  %186 = phi <16 x i32> [ zeroinitializer, %bb70.i ], [ %_3.i.i489, %bb3.i57.i ]
  %v.i41.i.sroa.137.04882 = phi <16 x i32> [ %64, %bb70.i ], [ %_3.i.i503, %bb3.i57.i ]
  %v.i41.i.sroa.146.04881 = phi <16 x i32> [ %65, %bb70.i ], [ %_3.i.i461, %bb3.i57.i ]
  %187 = add nuw nsw i64 %iter.sroa.0.0.i55.i4884, 1
  tail call void @llvm.experimental.noalias.scope.decl(metadata !43)
  %s.i18 = getelementptr inbounds nuw [16 x i64], ptr @alloc_61fb4a9344bbdaf2573accd6331d7e32, i64 %iter.sroa.0.0.i55.i4884
  %188 = getelementptr inbounds nuw i8, ptr %s.i18, i64 8
  %_11.i19 = load i64, ptr %188, align 8, !noalias !46, !noundef !41
  %_8.i20 = load i64, ptr %s.i18, align 8, !noalias !46, !noundef !41
  %189 = getelementptr inbounds nuw <8 x i64>, ptr %root_m.i, i64 %_8.i20
  %_7.i212665 = load <16 x i32>, ptr %189, align 64, !alias.scope !43, !noalias !56
  %190 = getelementptr inbounds nuw <8 x i64>, ptr %root_m.i, i64 %_11.i19
  %_10.i222666 = load <16 x i32>, ptr %190, align 64, !alias.scope !43, !noalias !56
  %_3.i395 = add <16 x i32> %174, %178
  %_3.i396 = add <16 x i32> %_3.i395, %_7.i212665
  %_3.i397 = xor <16 x i32> %_3.i396, %v.i41.i.sroa.119.0.in4883
  %_3.i.i398 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i397, <16 x i32> %_3.i397, <16 x i32> splat (i32 16))
  %_3.i399 = add <16 x i32> %_3.i.i398, %182
  %_3.i400 = xor <16 x i32> %_3.i399, %178
  %_3.i.i401 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i400, <16 x i32> %_3.i400, <16 x i32> splat (i32 20))
  %_3.i402 = add <16 x i32> %_10.i222666, %_3.i396
  %_3.i403 = add <16 x i32> %_3.i402, %_3.i.i401
  %_3.i404 = xor <16 x i32> %_3.i403, %_3.i.i398
  %_3.i.i405 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i404, <16 x i32> %_3.i404, <16 x i32> splat (i32 24))
  %_3.i406 = add <16 x i32> %_3.i.i405, %_3.i399
  %_3.i407 = xor <16 x i32> %_3.i406, %_3.i.i401
  %_3.i.i408 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i407, <16 x i32> %_3.i407, <16 x i32> splat (i32 25))
  %191 = getelementptr inbounds nuw i8, ptr %s.i18, i64 24
  %_18.i46 = load i64, ptr %191, align 8, !noalias !46, !noundef !41
  %192 = getelementptr inbounds nuw i8, ptr %s.i18, i64 16
  %_15.i47 = load i64, ptr %192, align 8, !noalias !46, !noundef !41
  %193 = getelementptr inbounds nuw <8 x i64>, ptr %root_m.i, i64 %_15.i47
  %_14.i482669 = load <16 x i32>, ptr %193, align 64, !alias.scope !43, !noalias !56
  %194 = getelementptr inbounds nuw <8 x i64>, ptr %root_m.i, i64 %_18.i46
  %_17.i492670 = load <16 x i32>, ptr %194, align 64, !alias.scope !43, !noalias !56
  %_3.i409 = add <16 x i32> %175, %179
  %_3.i410 = add <16 x i32> %_3.i409, %_14.i482669
  %_3.i411 = xor <16 x i32> %_3.i410, %186
  %_3.i.i412 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i411, <16 x i32> %_3.i411, <16 x i32> splat (i32 16))
  %_3.i413 = add <16 x i32> %_3.i.i412, %183
  %_3.i414 = xor <16 x i32> %_3.i413, %179
  %_3.i.i415 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i414, <16 x i32> %_3.i414, <16 x i32> splat (i32 20))
  %_3.i416 = add <16 x i32> %_17.i492670, %_3.i410
  %_3.i417 = add <16 x i32> %_3.i416, %_3.i.i415
  %_3.i418 = xor <16 x i32> %_3.i417, %_3.i.i412
  %_3.i.i419 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i418, <16 x i32> %_3.i418, <16 x i32> splat (i32 24))
  %_3.i420 = add <16 x i32> %_3.i.i419, %_3.i413
  %_3.i421 = xor <16 x i32> %_3.i420, %_3.i.i415
  %_3.i.i422 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i421, <16 x i32> %_3.i421, <16 x i32> splat (i32 25))
  %195 = getelementptr inbounds nuw i8, ptr %s.i18, i64 40
  %_25.i73 = load i64, ptr %195, align 8, !noalias !46, !noundef !41
  %196 = getelementptr inbounds nuw i8, ptr %s.i18, i64 32
  %_22.i74 = load i64, ptr %196, align 8, !noalias !46, !noundef !41
  %197 = getelementptr inbounds nuw <8 x i64>, ptr %root_m.i, i64 %_22.i74
  %_21.i752673 = load <16 x i32>, ptr %197, align 64, !alias.scope !43, !noalias !56
  %198 = getelementptr inbounds nuw <8 x i64>, ptr %root_m.i, i64 %_25.i73
  %_24.i762674 = load <16 x i32>, ptr %198, align 64, !alias.scope !43, !noalias !56
  %_3.i423 = add <16 x i32> %176, %180
  %_3.i424 = add <16 x i32> %_3.i423, %_21.i752673
  %_3.i425 = xor <16 x i32> %_3.i424, %v.i41.i.sroa.137.04882
  %_3.i.i426 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i425, <16 x i32> %_3.i425, <16 x i32> splat (i32 16))
  %_3.i427 = add <16 x i32> %_3.i.i426, %184
  %_3.i428 = xor <16 x i32> %_3.i427, %180
  %_3.i.i429 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i428, <16 x i32> %_3.i428, <16 x i32> splat (i32 20))
  %_3.i430 = add <16 x i32> %_24.i762674, %_3.i424
  %_3.i431 = add <16 x i32> %_3.i430, %_3.i.i429
  %_3.i432 = xor <16 x i32> %_3.i431, %_3.i.i426
  %_3.i.i433 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i432, <16 x i32> %_3.i432, <16 x i32> splat (i32 24))
  %_3.i434 = add <16 x i32> %_3.i.i433, %_3.i427
  %_3.i435 = xor <16 x i32> %_3.i434, %_3.i.i429
  %_3.i.i436 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i435, <16 x i32> %_3.i435, <16 x i32> splat (i32 25))
  %199 = getelementptr inbounds nuw i8, ptr %s.i18, i64 56
  %_32.i100 = load i64, ptr %199, align 8, !noalias !46, !noundef !41
  %200 = getelementptr inbounds nuw i8, ptr %s.i18, i64 48
  %_29.i101 = load i64, ptr %200, align 8, !noalias !46, !noundef !41
  %201 = getelementptr inbounds nuw <8 x i64>, ptr %root_m.i, i64 %_29.i101
  %_28.i1022677 = load <16 x i32>, ptr %201, align 64, !alias.scope !43, !noalias !56
  %202 = getelementptr inbounds nuw <8 x i64>, ptr %root_m.i, i64 %_32.i100
  %_31.i1032678 = load <16 x i32>, ptr %202, align 64, !alias.scope !43, !noalias !56
  %_3.i437 = add <16 x i32> %177, %181
  %_3.i438 = add <16 x i32> %_3.i437, %_28.i1022677
  %_3.i439 = xor <16 x i32> %_3.i438, %v.i41.i.sroa.146.04881
  %_3.i.i440 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i439, <16 x i32> %_3.i439, <16 x i32> splat (i32 16))
  %_3.i441 = add <16 x i32> %_3.i.i440, %185
  %_3.i442 = xor <16 x i32> %_3.i441, %181
  %_3.i.i443 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i442, <16 x i32> %_3.i442, <16 x i32> splat (i32 20))
  %_3.i444 = add <16 x i32> %_31.i1032678, %_3.i438
  %_3.i445 = add <16 x i32> %_3.i444, %_3.i.i443
  %_3.i446 = xor <16 x i32> %_3.i445, %_3.i.i440
  %_3.i.i447 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i446, <16 x i32> %_3.i446, <16 x i32> splat (i32 24))
  %_3.i448 = add <16 x i32> %_3.i.i447, %_3.i441
  %_3.i449 = xor <16 x i32> %_3.i448, %_3.i.i443
  %_3.i.i450 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i449, <16 x i32> %_3.i449, <16 x i32> splat (i32 25))
  %203 = getelementptr inbounds nuw i8, ptr %s.i18, i64 72
  %_39.i127 = load i64, ptr %203, align 8, !noalias !46, !noundef !41
  %204 = getelementptr inbounds nuw i8, ptr %s.i18, i64 64
  %_36.i128 = load i64, ptr %204, align 8, !noalias !46, !noundef !41
  %205 = getelementptr inbounds nuw <8 x i64>, ptr %root_m.i, i64 %_36.i128
  %_35.i1292681 = load <16 x i32>, ptr %205, align 64, !alias.scope !43, !noalias !56
  %206 = getelementptr inbounds nuw <8 x i64>, ptr %root_m.i, i64 %_39.i127
  %_38.i1302682 = load <16 x i32>, ptr %206, align 64, !alias.scope !43, !noalias !56
  %_3.i451 = add <16 x i32> %_35.i1292681, %_3.i403
  %_3.i452 = add <16 x i32> %_3.i451, %_3.i.i422
  %_3.i453 = xor <16 x i32> %_3.i.i447, %_3.i452
  %_3.i.i454 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i453, <16 x i32> %_3.i453, <16 x i32> splat (i32 16))
  %_3.i455 = add <16 x i32> %_3.i.i454, %_3.i434
  %_3.i456 = xor <16 x i32> %_3.i455, %_3.i.i422
  %_3.i.i457 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i456, <16 x i32> %_3.i456, <16 x i32> splat (i32 20))
  %_3.i458 = add <16 x i32> %_3.i452, %_38.i1302682
  %_3.i459 = add <16 x i32> %_3.i458, %_3.i.i457
  %_3.i460 = xor <16 x i32> %_3.i459, %_3.i.i454
  %_3.i.i461 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i460, <16 x i32> %_3.i460, <16 x i32> splat (i32 24))
  %_3.i462 = add <16 x i32> %_3.i.i461, %_3.i455
  %_3.i463 = xor <16 x i32> %_3.i462, %_3.i.i457
  %_3.i.i464 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i463, <16 x i32> %_3.i463, <16 x i32> splat (i32 25))
  %207 = getelementptr inbounds nuw i8, ptr %s.i18, i64 88
  %_46.i154 = load i64, ptr %207, align 8, !noalias !46, !noundef !41
  %208 = getelementptr inbounds nuw i8, ptr %s.i18, i64 80
  %_43.i155 = load i64, ptr %208, align 8, !noalias !46, !noundef !41
  %209 = getelementptr inbounds nuw <8 x i64>, ptr %root_m.i, i64 %_43.i155
  %_42.i1562683 = load <16 x i32>, ptr %209, align 64, !alias.scope !43, !noalias !56
  %210 = getelementptr inbounds nuw <8 x i64>, ptr %root_m.i, i64 %_46.i154
  %_45.i1572684 = load <16 x i32>, ptr %210, align 64, !alias.scope !43, !noalias !56
  %_3.i465 = add <16 x i32> %_42.i1562683, %_3.i417
  %_3.i466 = add <16 x i32> %_3.i465, %_3.i.i436
  %_3.i467 = xor <16 x i32> %_3.i466, %_3.i.i405
  %_3.i.i468 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i467, <16 x i32> %_3.i467, <16 x i32> splat (i32 16))
  %_3.i469 = add <16 x i32> %_3.i.i468, %_3.i448
  %_3.i470 = xor <16 x i32> %_3.i469, %_3.i.i436
  %_3.i.i471 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i470, <16 x i32> %_3.i470, <16 x i32> splat (i32 20))
  %_3.i472 = add <16 x i32> %_3.i466, %_45.i1572684
  %_3.i473 = add <16 x i32> %_3.i472, %_3.i.i471
  %_3.i474 = xor <16 x i32> %_3.i473, %_3.i.i468
  %_3.i.i475 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i474, <16 x i32> %_3.i474, <16 x i32> splat (i32 24))
  %_3.i476 = add <16 x i32> %_3.i.i475, %_3.i469
  %_3.i477 = xor <16 x i32> %_3.i476, %_3.i.i471
  %_3.i.i478 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i477, <16 x i32> %_3.i477, <16 x i32> splat (i32 25))
  %211 = getelementptr inbounds nuw i8, ptr %s.i18, i64 104
  %_53.i181 = load i64, ptr %211, align 8, !noalias !46, !noundef !41
  %212 = getelementptr inbounds nuw i8, ptr %s.i18, i64 96
  %_50.i182 = load i64, ptr %212, align 8, !noalias !46, !noundef !41
  %213 = getelementptr inbounds nuw <8 x i64>, ptr %root_m.i, i64 %_50.i182
  %_49.i1832685 = load <16 x i32>, ptr %213, align 64, !alias.scope !43, !noalias !56
  %214 = getelementptr inbounds nuw <8 x i64>, ptr %root_m.i, i64 %_53.i181
  %_52.i1842686 = load <16 x i32>, ptr %214, align 64, !alias.scope !43, !noalias !56
  %_3.i479 = add <16 x i32> %_49.i1832685, %_3.i431
  %_3.i480 = add <16 x i32> %_3.i479, %_3.i.i450
  %_3.i481 = xor <16 x i32> %_3.i480, %_3.i.i419
  %_3.i.i482 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i481, <16 x i32> %_3.i481, <16 x i32> splat (i32 16))
  %_3.i483 = add <16 x i32> %_3.i.i482, %_3.i406
  %_3.i484 = xor <16 x i32> %_3.i483, %_3.i.i450
  %_3.i.i485 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i484, <16 x i32> %_3.i484, <16 x i32> splat (i32 20))
  %_3.i486 = add <16 x i32> %_3.i480, %_52.i1842686
  %_3.i487 = add <16 x i32> %_3.i486, %_3.i.i485
  %_3.i488 = xor <16 x i32> %_3.i487, %_3.i.i482
  %_3.i.i489 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i488, <16 x i32> %_3.i488, <16 x i32> splat (i32 24))
  %_3.i490 = add <16 x i32> %_3.i.i489, %_3.i483
  %_3.i491 = xor <16 x i32> %_3.i490, %_3.i.i485
  %_3.i.i492 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i491, <16 x i32> %_3.i491, <16 x i32> splat (i32 25))
  %215 = getelementptr inbounds nuw i8, ptr %s.i18, i64 120
  %_60.i208 = load i64, ptr %215, align 8, !noalias !46, !noundef !41
  %216 = getelementptr inbounds nuw i8, ptr %s.i18, i64 112
  %_57.i209 = load i64, ptr %216, align 8, !noalias !46, !noundef !41
  %217 = getelementptr inbounds nuw <8 x i64>, ptr %root_m.i, i64 %_57.i209
  %_56.i2102687 = load <16 x i32>, ptr %217, align 64, !alias.scope !43, !noalias !56
  %218 = getelementptr inbounds nuw <8 x i64>, ptr %root_m.i, i64 %_60.i208
  %_59.i2112688 = load <16 x i32>, ptr %218, align 64, !alias.scope !43, !noalias !56
  %_3.i493 = add <16 x i32> %_3.i445, %_3.i.i408
  %_3.i494 = add <16 x i32> %_3.i493, %_56.i2102687
  %_3.i495 = xor <16 x i32> %_3.i494, %_3.i.i433
  %_3.i.i496 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i495, <16 x i32> %_3.i495, <16 x i32> splat (i32 16))
  %_3.i497 = add <16 x i32> %_3.i.i496, %_3.i420
  %_3.i498 = xor <16 x i32> %_3.i497, %_3.i.i408
  %_3.i.i499 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i498, <16 x i32> %_3.i498, <16 x i32> splat (i32 20))
  %_3.i500 = add <16 x i32> %_59.i2112688, %_3.i494
  %_3.i501 = add <16 x i32> %_3.i500, %_3.i.i499
  %_3.i502 = xor <16 x i32> %_3.i501, %_3.i.i496
  %_3.i.i503 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i502, <16 x i32> %_3.i502, <16 x i32> splat (i32 24))
  %_3.i504 = add <16 x i32> %_3.i.i503, %_3.i497
  %_3.i505 = xor <16 x i32> %_3.i504, %_3.i.i499
  %_3.i.i506 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i505, <16 x i32> %_3.i505, <16 x i32> splat (i32 25))
  %exitcond5453.not = icmp eq i64 %187, 7
  br i1 %exitcond5453.not, label %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit58.i, label %bb3.i57.i

_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit58.i: ; preds = %bb3.i57.i
  %_3.i507 = xor <16 x i32> %_3.i490, %_3.i459
  %_3.i508 = xor <16 x i32> %24, %_3.i490
  %_3.i507.1 = xor <16 x i32> %_3.i504, %_3.i473
  %_3.i508.1 = xor <16 x i32> %23, %_3.i504
  %_3.i507.2 = xor <16 x i32> %_3.i462, %_3.i487
  %_3.i508.2 = xor <16 x i32> %22, %_3.i462
  %_3.i507.3 = xor <16 x i32> %_3.i476, %_3.i501
  %_3.i508.3 = xor <16 x i32> %21, %_3.i476
  %_3.i507.4 = xor <16 x i32> %_3.i.i475, %_3.i.i506
  %_3.i508.4 = xor <16 x i32> %20, %_3.i.i475
  %_3.i507.5 = xor <16 x i32> %_3.i.i489, %_3.i.i464
  %_3.i508.5 = xor <16 x i32> %19, %_3.i.i489
  %_3.i507.6 = xor <16 x i32> %_3.i.i503, %_3.i.i478
  %_3.i508.6 = xor <16 x i32> %18, %_3.i.i503
  %_3.i507.7 = xor <16 x i32> %_3.i.i461, %_3.i.i492
  %_3.i508.7 = xor <16 x i32> %17, %_3.i.i461
  %_218.i.idx = shl nuw nsw i64 %iter4.sroa.0.0.i4920, 6
  %_218.i = getelementptr inbounds nuw i8, ptr %acc, i64 %_218.i.idx
  %_218.i.promoted = load <32 x i16>, ptr %_218.i, align 2, !noalias !57
  %r.i = shufflevector <16 x i32> %_3.i507, <16 x i32> %_3.i507.4, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i509 = shufflevector <16 x i32> %_3.i507.1, <16 x i32> %_3.i507.5, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i510 = shufflevector <16 x i32> %_3.i507.2, <16 x i32> %_3.i507.6, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i511 = shufflevector <16 x i32> %_3.i507.3, <16 x i32> %_3.i507.7, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i512 = shufflevector <16 x i32> %_3.i507, <16 x i32> %_3.i507.4, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i513 = shufflevector <16 x i32> %_3.i507.1, <16 x i32> %_3.i507.5, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i514 = shufflevector <16 x i32> %_3.i507.2, <16 x i32> %_3.i507.6, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i515 = shufflevector <16 x i32> %_3.i507.3, <16 x i32> %_3.i507.7, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i516 = shufflevector <16 x i32> %_3.i508, <16 x i32> %_3.i508.4, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i517 = shufflevector <16 x i32> %_3.i508.1, <16 x i32> %_3.i508.5, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i518 = shufflevector <16 x i32> %_3.i508.2, <16 x i32> %_3.i508.6, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i519 = shufflevector <16 x i32> %_3.i508.3, <16 x i32> %_3.i508.7, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i520 = shufflevector <16 x i32> %_3.i508, <16 x i32> %_3.i508.4, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i521 = shufflevector <16 x i32> %_3.i508.1, <16 x i32> %_3.i508.5, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i522 = shufflevector <16 x i32> %_3.i508.2, <16 x i32> %_3.i508.6, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i523 = shufflevector <16 x i32> %_3.i508.3, <16 x i32> %_3.i508.7, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i524 = shufflevector <16 x i32> %r.i, <16 x i32> %r.i516, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i525 = shufflevector <16 x i32> %r.i509, <16 x i32> %r.i517, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i526 = shufflevector <16 x i32> %r.i510, <16 x i32> %r.i518, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i527 = shufflevector <16 x i32> %r.i511, <16 x i32> %r.i519, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i528 = shufflevector <16 x i32> %r.i512, <16 x i32> %r.i520, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i529 = shufflevector <16 x i32> %r.i513, <16 x i32> %r.i521, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i530 = shufflevector <16 x i32> %r.i514, <16 x i32> %r.i522, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i531 = shufflevector <16 x i32> %r.i515, <16 x i32> %r.i523, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i532 = shufflevector <16 x i32> %r.i, <16 x i32> %r.i516, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i533 = shufflevector <16 x i32> %r.i509, <16 x i32> %r.i517, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i534 = shufflevector <16 x i32> %r.i510, <16 x i32> %r.i518, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i535 = shufflevector <16 x i32> %r.i511, <16 x i32> %r.i519, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i536 = shufflevector <16 x i32> %r.i512, <16 x i32> %r.i520, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i537 = shufflevector <16 x i32> %r.i513, <16 x i32> %r.i521, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i538 = shufflevector <16 x i32> %r.i514, <16 x i32> %r.i522, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i539 = shufflevector <16 x i32> %r.i515, <16 x i32> %r.i523, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i540 = shufflevector <16 x i32> %r.i524, <16 x i32> %r.i526, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i541 = shufflevector <16 x i32> %r.i525, <16 x i32> %r.i527, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i542 = shufflevector <16 x i32> %r.i524, <16 x i32> %r.i526, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i543 = shufflevector <16 x i32> %r.i525, <16 x i32> %r.i527, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i544 = shufflevector <16 x i32> %r.i528, <16 x i32> %r.i530, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i545 = shufflevector <16 x i32> %r.i529, <16 x i32> %r.i531, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i546 = shufflevector <16 x i32> %r.i528, <16 x i32> %r.i530, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i547 = shufflevector <16 x i32> %r.i529, <16 x i32> %r.i531, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i548 = shufflevector <16 x i32> %r.i532, <16 x i32> %r.i534, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i549 = shufflevector <16 x i32> %r.i533, <16 x i32> %r.i535, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i550 = shufflevector <16 x i32> %r.i532, <16 x i32> %r.i534, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i551 = shufflevector <16 x i32> %r.i533, <16 x i32> %r.i535, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i552 = shufflevector <16 x i32> %r.i536, <16 x i32> %r.i538, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i553 = shufflevector <16 x i32> %r.i537, <16 x i32> %r.i539, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i554 = shufflevector <16 x i32> %r.i536, <16 x i32> %r.i538, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i555 = shufflevector <16 x i32> %r.i537, <16 x i32> %r.i539, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i556 = shufflevector <16 x i32> %r.i540, <16 x i32> %r.i541, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i557 = shufflevector <16 x i32> %r.i540, <16 x i32> %r.i541, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i558 = shufflevector <16 x i32> %r.i542, <16 x i32> %r.i543, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i559 = shufflevector <16 x i32> %r.i542, <16 x i32> %r.i543, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i560 = shufflevector <16 x i32> %r.i544, <16 x i32> %r.i545, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i561 = shufflevector <16 x i32> %r.i544, <16 x i32> %r.i545, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i562 = shufflevector <16 x i32> %r.i546, <16 x i32> %r.i547, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i563 = shufflevector <16 x i32> %r.i546, <16 x i32> %r.i547, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i564 = shufflevector <16 x i32> %r.i548, <16 x i32> %r.i549, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i565 = shufflevector <16 x i32> %r.i548, <16 x i32> %r.i549, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i566 = shufflevector <16 x i32> %r.i550, <16 x i32> %r.i551, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i567 = shufflevector <16 x i32> %r.i550, <16 x i32> %r.i551, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i568 = shufflevector <16 x i32> %r.i552, <16 x i32> %r.i553, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i569 = shufflevector <16 x i32> %r.i552, <16 x i32> %r.i553, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i570 = shufflevector <16 x i32> %r.i554, <16 x i32> %r.i555, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i571 = shufflevector <16 x i32> %r.i554, <16 x i32> %r.i555, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %219 = bitcast <16 x i32> %r.i556 to <32 x i16>
  %220 = bitcast <16 x i32> %r.i557 to <32 x i16>
  %_3.i572 = add <32 x i16> %220, %219
  %221 = bitcast <16 x i32> %r.i558 to <32 x i16>
  %_3.i572.1 = add <32 x i16> %_3.i572, %221
  %222 = bitcast <16 x i32> %r.i559 to <32 x i16>
  %_3.i572.2 = add <32 x i16> %_3.i572.1, %222
  %223 = bitcast <16 x i32> %r.i560 to <32 x i16>
  %_3.i572.3 = add <32 x i16> %_3.i572.2, %223
  %224 = bitcast <16 x i32> %r.i561 to <32 x i16>
  %_3.i572.4 = add <32 x i16> %_3.i572.3, %224
  %225 = bitcast <16 x i32> %r.i562 to <32 x i16>
  %_3.i572.5 = add <32 x i16> %_3.i572.4, %225
  %226 = bitcast <16 x i32> %r.i563 to <32 x i16>
  %_3.i572.6 = add <32 x i16> %_3.i572.5, %226
  %227 = bitcast <16 x i32> %r.i564 to <32 x i16>
  %_3.i572.7 = add <32 x i16> %_3.i572.6, %227
  %228 = bitcast <16 x i32> %r.i565 to <32 x i16>
  %_3.i572.8 = add <32 x i16> %_3.i572.7, %228
  %229 = bitcast <16 x i32> %r.i566 to <32 x i16>
  %_3.i572.9 = add <32 x i16> %_3.i572.8, %229
  %230 = bitcast <16 x i32> %r.i567 to <32 x i16>
  %_3.i572.10 = add <32 x i16> %_3.i572.9, %230
  %231 = bitcast <16 x i32> %r.i568 to <32 x i16>
  %_3.i572.11 = add <32 x i16> %_3.i572.10, %231
  %232 = bitcast <16 x i32> %r.i569 to <32 x i16>
  %_3.i572.12 = add <32 x i16> %_3.i572.11, %232
  %233 = bitcast <16 x i32> %r.i570 to <32 x i16>
  %_3.i572.13 = add <32 x i16> %_3.i572.12, %233
  %234 = bitcast <16 x i32> %r.i571 to <32 x i16>
  %_3.i572.14 = add <32 x i16> %_3.i572.13, %234
  %235 = add nuw nsw i64 %iter4.sroa.0.0.i4920, 1
  %_3.i573 = add <32 x i16> %_218.i.promoted, %_3.i572.14
  store <32 x i16> %_3.i573, ptr %_218.i, align 2, !noalias !57
  %exitcond5455.not = icmp eq i64 %235, 32
  br i1 %exitcond5455.not, label %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit, label %bb70.i

_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit: ; preds = %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit58.i
  call void @llvm.lifetime.end.p0(ptr nonnull %root_m.i), !noalias !16
  ret void
}

; Function Attrs: nounwind nonlazybind uwtable
define void @agave_batch_8(ptr noalias nofree noundef readonly align 4 captures(none) dereferenceable(8192) %lanes, ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(64) %lengths, ptr noalias nofree noundef align 2 captures(none) dereferenceable(2048) %acc) unnamed_addr #3 personality ptr @rust_eh_personality {
start:
  %m.i = alloca [512 x i8], align 32
  %root_m.i = alloca [512 x i8], align 32
  %_32.1.i = getelementptr inbounds nuw i8, ptr %lanes, i64 1024
  %_32.2.i = getelementptr inbounds nuw i8, ptr %lanes, i64 2048
  %_32.3.i = getelementptr inbounds nuw i8, ptr %lanes, i64 3072
  %_32.4.i = getelementptr inbounds nuw i8, ptr %lanes, i64 4096
  %_32.5.i = getelementptr inbounds nuw i8, ptr %lanes, i64 5120
  %_32.6.i = getelementptr inbounds nuw i8, ptr %lanes, i64 6144
  %_32.7.i = getelementptr inbounds nuw i8, ptr %lanes, i64 7168
  %0 = load <8 x i64>, ptr %lengths, align 8, !noalias !58
  %m.i956.sroa.7.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 32
  %m.i956.sroa.11.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 64
  %m.i956.sroa.15.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 96
  %m.i956.sroa.19.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 128
  %m.i956.sroa.23.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 160
  %m.i956.sroa.27.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 192
  %m.i956.sroa.31.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 224
  %m.i956.sroa.35.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 256
  %m.i956.sroa.39.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 288
  %m.i956.sroa.43.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 320
  %m.i956.sroa.47.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 352
  %m.i956.sroa.51.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 384
  %m.i956.sroa.55.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 416
  %m.i956.sroa.59.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 448
  %m.i956.sroa.63.0.m.i.sroa_idx = getelementptr inbounds nuw i8, ptr %m.i, i64 480
  br label %bb3.i

bb3.i:                                            ; preds = %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit.i, %start
  %h.i.sroa.44.0 = phi <4 x i64> [ splat (i64 6620516961033964825), %start ], [ %158, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit.i ]
  %h.i.sroa.38.0 = phi <4 x i64> [ splat (i64 2270897966116231595), %start ], [ %155, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit.i ]
  %h.i.sroa.32.0 = phi <4 x i64> [ splat (i64 -7276294669841635188), %start ], [ %152, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit.i ]
  %h.i.sroa.26.0 = phi <4 x i64> [ splat (i64 5840696473520329343), %start ], [ %149, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit.i ]
  %h.i.sroa.20.0 = phi <4 x i64> [ splat (i64 -6534734902060911302), %start ], [ %146, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit.i ]
  %h.i.sroa.14.0 = phi <4 x i64> [ splat (i64 4354685561679573874), %start ], [ %143, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit.i ]
  %h.i.sroa.8.0 = phi <4 x i64> [ splat (i64 -4942790176617812347), %start ], [ %140, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit.i ]
  %h.i.sroa.0.0 = phi <4 x i64> [ splat (i64 7640891574645810791), %start ], [ %137, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit.i ]
  %1 = phi <8 x i64> [ zeroinitializer, %start ], [ %159, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit.i ]
  %2 = add <8 x i64> %1, splat (i64 64)
  %3 = icmp ugt <8 x i64> %0, %2
  %4 = freeze <8 x i1> %3
  %5 = icmp eq <8 x i64> %1, zeroinitializer
  %6 = select <8 x i1> %4, <8 x i32> zeroinitializer, <8 x i32> splat (i32 10)
  %7 = zext <8 x i1> %5 to <8 x i32>
  %8 = or disjoint <8 x i32> %6, %7
  %9 = sub <8 x i64> %0, %1
  %10 = tail call <8 x i64> @llvm.umin.v8i64(<8 x i64> %9, <8 x i64> splat (i64 64))
  %11 = trunc nuw nsw <8 x i64> %10 to <8 x i32>
  call void @llvm.lifetime.start.p0(ptr nonnull %m.i), !noalias !58
  %12 = extractelement <8 x i64> %1, i64 0
  %_257.i = lshr i64 %12, 2
  %13 = extractelement <8 x i64> %1, i64 1
  %_257.1.i = lshr i64 %13, 2
  %14 = extractelement <8 x i64> %1, i64 2
  %_257.2.i = lshr i64 %14, 2
  %15 = extractelement <8 x i64> %1, i64 3
  %_257.3.i = lshr i64 %15, 2
  %16 = extractelement <8 x i64> %1, i64 4
  %_257.4.i = lshr i64 %16, 2
  %17 = extractelement <8 x i64> %1, i64 5
  %_257.5.i = lshr i64 %17, 2
  %18 = extractelement <8 x i64> %1, i64 6
  %_257.6.i = lshr i64 %18, 2
  %19 = extractelement <8 x i64> %1, i64 7
  %_257.7.i = lshr i64 %19, 2
  %_65.i969 = icmp ugt i64 %12, 1027
  br i1 %_65.i969, label %bb20.i, label %bb8.1.i, !prof !20

bb8.i.1:                                          ; preds = %bb8.7.i
  %_71.6.i = getelementptr inbounds nuw i32, ptr %_32.6.i, i64 %_257.6.i
  %dst.sroa.0.0.copyload.i13793769 = load <8 x i32>, ptr %_71.6.i, align 4, !noalias !62
  %_71.7.i = getelementptr inbounds nuw i32, ptr %_32.7.i, i64 %_257.7.i
  %dst.sroa.0.0.copyload.i13783770 = load <8 x i32>, ptr %_71.7.i, align 4, !noalias !69
  %r.i1409 = shufflevector <8 x i32> %dst.sroa.0.0.copyload.i13853763, <8 x i32> %dst.sroa.0.0.copyload.i13843764, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1408 = shufflevector <8 x i32> %dst.sroa.0.0.copyload.i13853763, <8 x i32> %dst.sroa.0.0.copyload.i13843764, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %r.i1407 = shufflevector <8 x i32> %dst.sroa.0.0.copyload.i13833765, <8 x i32> %dst.sroa.0.0.copyload.i13823766, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1406 = shufflevector <8 x i32> %dst.sroa.0.0.copyload.i13833765, <8 x i32> %dst.sroa.0.0.copyload.i13823766, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %r.i1405 = shufflevector <8 x i32> %dst.sroa.0.0.copyload.i13813767, <8 x i32> %dst.sroa.0.0.copyload.i13803768, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1404 = shufflevector <8 x i32> %dst.sroa.0.0.copyload.i13813767, <8 x i32> %dst.sroa.0.0.copyload.i13803768, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %r.i1403 = shufflevector <8 x i32> %dst.sroa.0.0.copyload.i13793769, <8 x i32> %dst.sroa.0.0.copyload.i13783770, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1402 = shufflevector <8 x i32> %dst.sroa.0.0.copyload.i13793769, <8 x i32> %dst.sroa.0.0.copyload.i13783770, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %20 = shufflevector <8 x i32> %r.i1409, <8 x i32> %r.i1407, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %21 = shufflevector <8 x i32> %r.i1409, <8 x i32> %r.i1407, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %22 = shufflevector <8 x i32> %r.i1408, <8 x i32> %r.i1406, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %23 = shufflevector <8 x i32> %r.i1408, <8 x i32> %r.i1406, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %24 = shufflevector <8 x i32> %r.i1405, <8 x i32> %r.i1403, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %25 = shufflevector <8 x i32> %r.i1405, <8 x i32> %r.i1403, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %26 = shufflevector <8 x i32> %r.i1404, <8 x i32> %r.i1402, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %27 = shufflevector <8 x i32> %r.i1404, <8 x i32> %r.i1402, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %28 = shufflevector <8 x i32> %20, <8 x i32> %24, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  %29 = shufflevector <8 x i32> %21, <8 x i32> %25, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  %30 = shufflevector <8 x i32> %22, <8 x i32> %26, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  %31 = shufflevector <8 x i32> %23, <8 x i32> %27, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  %32 = shufflevector <8 x i32> %20, <8 x i32> %24, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  %33 = shufflevector <8 x i32> %21, <8 x i32> %25, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  %34 = shufflevector <8 x i32> %22, <8 x i32> %26, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  %35 = shufflevector <8 x i32> %23, <8 x i32> %27, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  %base.i968.1 = add nuw nsw i64 %_257.i, 8
  %_65.i969.1 = icmp samesign ugt i64 %12, 995
  br i1 %_65.i969.1, label %bb20.i, label %bb8.1.i.1, !prof !20

bb8.1.i.1:                                        ; preds = %bb8.i.1
  %_71.i970.1 = getelementptr inbounds nuw i32, ptr %lanes, i64 %base.i968.1
  %dst.sroa.0.0.copyload.i1385.13771 = load <8 x i32>, ptr %_71.i970.1, align 4, !noalias !72
  %base.1.i.1 = add nuw nsw i64 %_257.1.i, 8
  %_65.1.i.1 = icmp ugt i64 %13, 995
  br i1 %_65.1.i.1, label %bb20.i, label %bb8.2.i.1, !prof !20

bb8.2.i.1:                                        ; preds = %bb8.1.i.1
  %_71.1.i.1 = getelementptr inbounds nuw i32, ptr %_32.1.i, i64 %base.1.i.1
  %dst.sroa.0.0.copyload.i1384.13772 = load <8 x i32>, ptr %_71.1.i.1, align 4, !noalias !75
  %base.2.i.1 = add nuw nsw i64 %_257.2.i, 8
  %_65.2.i.1 = icmp ugt i64 %14, 995
  br i1 %_65.2.i.1, label %bb20.i, label %bb8.3.i.1, !prof !20

bb8.3.i.1:                                        ; preds = %bb8.2.i.1
  %_71.2.i.1 = getelementptr inbounds nuw i32, ptr %_32.2.i, i64 %base.2.i.1
  %dst.sroa.0.0.copyload.i1383.13773 = load <8 x i32>, ptr %_71.2.i.1, align 4, !noalias !78
  %base.3.i.1 = add nuw nsw i64 %_257.3.i, 8
  %_65.3.i.1 = icmp ugt i64 %15, 995
  br i1 %_65.3.i.1, label %bb20.i, label %bb8.4.i.1, !prof !20

bb8.4.i.1:                                        ; preds = %bb8.3.i.1
  %_71.3.i.1 = getelementptr inbounds nuw i32, ptr %_32.3.i, i64 %base.3.i.1
  %dst.sroa.0.0.copyload.i1382.13774 = load <8 x i32>, ptr %_71.3.i.1, align 4, !noalias !81
  %base.4.i.1 = add nuw nsw i64 %_257.4.i, 8
  %_65.4.i.1 = icmp ugt i64 %16, 995
  br i1 %_65.4.i.1, label %bb20.i, label %bb8.5.i.1, !prof !20

bb8.5.i.1:                                        ; preds = %bb8.4.i.1
  %_71.4.i.1 = getelementptr inbounds nuw i32, ptr %_32.4.i, i64 %base.4.i.1
  %dst.sroa.0.0.copyload.i1381.13775 = load <8 x i32>, ptr %_71.4.i.1, align 4, !noalias !84
  %base.5.i.1 = add nuw nsw i64 %_257.5.i, 8
  %_65.5.i.1 = icmp ugt i64 %17, 995
  br i1 %_65.5.i.1, label %bb20.i, label %bb8.6.i.1, !prof !20

bb8.6.i.1:                                        ; preds = %bb8.5.i.1
  %_71.5.i.1 = getelementptr inbounds nuw i32, ptr %_32.5.i, i64 %base.5.i.1
  %dst.sroa.0.0.copyload.i1380.13776 = load <8 x i32>, ptr %_71.5.i.1, align 4, !noalias !87
  %base.6.i.1 = add nuw nsw i64 %_257.6.i, 8
  %_65.6.i.1 = icmp ugt i64 %18, 995
  br i1 %_65.6.i.1, label %bb20.i, label %bb8.7.i.1, !prof !20

bb8.7.i.1:                                        ; preds = %bb8.6.i.1
  %base.7.i.1 = add nuw nsw i64 %_257.7.i, 8
  %_65.7.i.1 = icmp ugt i64 %19, 995
  br i1 %_65.7.i.1, label %bb20.i, label %_RNvXNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4archNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iNtB2_5Lanes9transpose.exit.i.1, !prof !20

_RNvXNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4archNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iNtB2_5Lanes9transpose.exit.i.1: ; preds = %bb8.7.i.1
  %_71.6.i.1 = getelementptr inbounds nuw i32, ptr %_32.6.i, i64 %base.6.i.1
  %dst.sroa.0.0.copyload.i1379.13777 = load <8 x i32>, ptr %_71.6.i.1, align 4, !noalias !62
  %_71.7.i.1 = getelementptr inbounds nuw i32, ptr %_32.7.i, i64 %base.7.i.1
  %dst.sroa.0.0.copyload.i1378.13778 = load <8 x i32>, ptr %_71.7.i.1, align 4, !noalias !69
  %r.i1409.1 = shufflevector <8 x i32> %dst.sroa.0.0.copyload.i1385.13771, <8 x i32> %dst.sroa.0.0.copyload.i1384.13772, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1408.1 = shufflevector <8 x i32> %dst.sroa.0.0.copyload.i1385.13771, <8 x i32> %dst.sroa.0.0.copyload.i1384.13772, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %r.i1407.1 = shufflevector <8 x i32> %dst.sroa.0.0.copyload.i1383.13773, <8 x i32> %dst.sroa.0.0.copyload.i1382.13774, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1406.1 = shufflevector <8 x i32> %dst.sroa.0.0.copyload.i1383.13773, <8 x i32> %dst.sroa.0.0.copyload.i1382.13774, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %r.i1405.1 = shufflevector <8 x i32> %dst.sroa.0.0.copyload.i1381.13775, <8 x i32> %dst.sroa.0.0.copyload.i1380.13776, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1404.1 = shufflevector <8 x i32> %dst.sroa.0.0.copyload.i1381.13775, <8 x i32> %dst.sroa.0.0.copyload.i1380.13776, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %r.i1403.1 = shufflevector <8 x i32> %dst.sroa.0.0.copyload.i1379.13777, <8 x i32> %dst.sroa.0.0.copyload.i1378.13778, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1402.1 = shufflevector <8 x i32> %dst.sroa.0.0.copyload.i1379.13777, <8 x i32> %dst.sroa.0.0.copyload.i1378.13778, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %36 = shufflevector <8 x i32> %r.i1409.1, <8 x i32> %r.i1407.1, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %37 = shufflevector <8 x i32> %r.i1409.1, <8 x i32> %r.i1407.1, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %38 = shufflevector <8 x i32> %r.i1408.1, <8 x i32> %r.i1406.1, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %39 = shufflevector <8 x i32> %r.i1408.1, <8 x i32> %r.i1406.1, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %40 = shufflevector <8 x i32> %r.i1405.1, <8 x i32> %r.i1403.1, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %41 = shufflevector <8 x i32> %r.i1405.1, <8 x i32> %r.i1403.1, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %42 = shufflevector <8 x i32> %r.i1404.1, <8 x i32> %r.i1402.1, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %43 = shufflevector <8 x i32> %r.i1404.1, <8 x i32> %r.i1402.1, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %44 = shufflevector <8 x i32> %36, <8 x i32> %40, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  %45 = shufflevector <8 x i32> %37, <8 x i32> %41, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  %46 = shufflevector <8 x i32> %38, <8 x i32> %42, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  %47 = shufflevector <8 x i32> %39, <8 x i32> %43, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  %48 = shufflevector <8 x i32> %36, <8 x i32> %40, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  %49 = shufflevector <8 x i32> %37, <8 x i32> %41, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  %50 = shufflevector <8 x i32> %38, <8 x i32> %42, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  %51 = shufflevector <8 x i32> %39, <8 x i32> %43, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  store <8 x i32> %28, ptr %m.i, align 32, !noalias !90
  store <8 x i32> %29, ptr %m.i956.sroa.7.0.m.i.sroa_idx, align 32, !noalias !90
  store <8 x i32> %30, ptr %m.i956.sroa.11.0.m.i.sroa_idx, align 32, !noalias !90
  store <8 x i32> %31, ptr %m.i956.sroa.15.0.m.i.sroa_idx, align 32, !noalias !90
  store <8 x i32> %32, ptr %m.i956.sroa.19.0.m.i.sroa_idx, align 32, !noalias !90
  store <8 x i32> %33, ptr %m.i956.sroa.23.0.m.i.sroa_idx, align 32, !noalias !90
  store <8 x i32> %34, ptr %m.i956.sroa.27.0.m.i.sroa_idx, align 32, !noalias !90
  store <8 x i32> %35, ptr %m.i956.sroa.31.0.m.i.sroa_idx, align 32, !noalias !90
  store <8 x i32> %44, ptr %m.i956.sroa.35.0.m.i.sroa_idx, align 32, !noalias !90
  store <8 x i32> %45, ptr %m.i956.sroa.39.0.m.i.sroa_idx, align 32, !noalias !90
  store <8 x i32> %46, ptr %m.i956.sroa.43.0.m.i.sroa_idx, align 32, !noalias !90
  store <8 x i32> %47, ptr %m.i956.sroa.47.0.m.i.sroa_idx, align 32, !noalias !90
  store <8 x i32> %48, ptr %m.i956.sroa.51.0.m.i.sroa_idx, align 32, !noalias !90
  store <8 x i32> %49, ptr %m.i956.sroa.55.0.m.i.sroa_idx, align 32, !noalias !90
  store <8 x i32> %50, ptr %m.i956.sroa.59.0.m.i.sroa_idx, align 32, !noalias !90
  store <8 x i32> %51, ptr %m.i956.sroa.63.0.m.i.sroa_idx, align 32, !noalias !90
  %52 = bitcast <8 x i1> %4 to i8
  %.not = icmp eq i8 %52, 0
  br i1 %.not, label %bb24.i, label %bb23.i

bb8.1.i:                                          ; preds = %bb3.i
  %_71.i970 = getelementptr inbounds nuw i32, ptr %lanes, i64 %_257.i
  %dst.sroa.0.0.copyload.i13853763 = load <8 x i32>, ptr %_71.i970, align 4, !noalias !72
  %_65.1.i = icmp samesign ugt i64 %13, 1027
  br i1 %_65.1.i, label %bb20.i, label %bb8.2.i, !prof !20

bb8.2.i:                                          ; preds = %bb8.1.i
  %_71.1.i = getelementptr inbounds nuw i32, ptr %_32.1.i, i64 %_257.1.i
  %dst.sroa.0.0.copyload.i13843764 = load <8 x i32>, ptr %_71.1.i, align 4, !noalias !75
  %_65.2.i = icmp samesign ugt i64 %14, 1027
  br i1 %_65.2.i, label %bb20.i, label %bb8.3.i, !prof !20

bb8.3.i:                                          ; preds = %bb8.2.i
  %_71.2.i = getelementptr inbounds nuw i32, ptr %_32.2.i, i64 %_257.2.i
  %dst.sroa.0.0.copyload.i13833765 = load <8 x i32>, ptr %_71.2.i, align 4, !noalias !78
  %_65.3.i = icmp samesign ugt i64 %15, 1027
  br i1 %_65.3.i, label %bb20.i, label %bb8.4.i, !prof !20

bb8.4.i:                                          ; preds = %bb8.3.i
  %_71.3.i = getelementptr inbounds nuw i32, ptr %_32.3.i, i64 %_257.3.i
  %dst.sroa.0.0.copyload.i13823766 = load <8 x i32>, ptr %_71.3.i, align 4, !noalias !81
  %_65.4.i = icmp samesign ugt i64 %16, 1027
  br i1 %_65.4.i, label %bb20.i, label %bb8.5.i, !prof !20

bb8.5.i:                                          ; preds = %bb8.4.i
  %_71.4.i = getelementptr inbounds nuw i32, ptr %_32.4.i, i64 %_257.4.i
  %dst.sroa.0.0.copyload.i13813767 = load <8 x i32>, ptr %_71.4.i, align 4, !noalias !84
  %_65.5.i = icmp samesign ugt i64 %17, 1027
  br i1 %_65.5.i, label %bb20.i, label %bb8.6.i, !prof !20

bb8.6.i:                                          ; preds = %bb8.5.i
  %_71.5.i = getelementptr inbounds nuw i32, ptr %_32.5.i, i64 %_257.5.i
  %dst.sroa.0.0.copyload.i13803768 = load <8 x i32>, ptr %_71.5.i, align 4, !noalias !87
  %_65.6.i = icmp samesign ugt i64 %18, 1027
  br i1 %_65.6.i, label %bb20.i, label %bb8.7.i, !prof !20

bb8.7.i:                                          ; preds = %bb8.6.i
  %_65.7.i = icmp samesign ugt i64 %19, 1027
  br i1 %_65.7.i, label %bb20.i, label %bb8.i.1, !prof !20

bb20.i:                                           ; preds = %bb8.7.i.1, %bb8.6.i.1, %bb8.5.i.1, %bb8.4.i.1, %bb8.3.i.1, %bb8.2.i.1, %bb8.1.i.1, %bb8.i.1, %bb8.7.i, %bb8.6.i, %bb8.5.i, %bb8.4.i, %bb8.3.i, %bb8.2.i, %bb8.1.i, %bb3.i
  %base.lcssa49.ph.i = phi i64 [ %_257.7.i, %bb8.7.i ], [ %_257.6.i, %bb8.6.i ], [ %_257.5.i, %bb8.5.i ], [ %_257.4.i, %bb8.4.i ], [ %_257.3.i, %bb8.3.i ], [ %_257.2.i, %bb8.2.i ], [ %_257.1.i, %bb8.1.i ], [ %_257.i, %bb3.i ], [ %base.i968.1, %bb8.i.1 ], [ %base.1.i.1, %bb8.1.i.1 ], [ %base.2.i.1, %bb8.2.i.1 ], [ %base.3.i.1, %bb8.3.i.1 ], [ %base.4.i.1, %bb8.4.i.1 ], [ %base.5.i.1, %bb8.5.i.1 ], [ %base.6.i.1, %bb8.6.i.1 ], [ %base.7.i.1, %bb8.7.i.1 ]
; call core::slice::index::slice_index_fail
  tail call void @_RNvNtNtCsgxBkk5gSRhY_4core5slice5index16slice_index_fail(i64 noundef %base.lcssa49.ph.i, i64 noundef 256, i64 noundef 256, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_83bddfce772813ac48c9037cf7b0770f) #12, !noalias !91
  unreachable

bb24.i:                                           ; preds = %_RNvXNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4archNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iNtB2_5Lanes9transpose.exit.i.1
  call void @llvm.lifetime.start.p0(ptr nonnull %root_m.i), !noalias !58
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 32 dereferenceable(512) %root_m.i, ptr noundef nonnull align 32 dereferenceable(512) %m.i, i64 512, i1 false), !noalias !58
  call void @llvm.lifetime.end.p0(ptr nonnull %m.i), !noalias !58
  %53 = bitcast <4 x i64> %h.i.sroa.0.0 to <8 x i32>
  %54 = bitcast <4 x i64> %h.i.sroa.8.0 to <8 x i32>
  %55 = bitcast <4 x i64> %h.i.sroa.14.0 to <8 x i32>
  %56 = bitcast <4 x i64> %h.i.sroa.20.0 to <8 x i32>
  %57 = bitcast <4 x i64> %h.i.sroa.26.0 to <8 x i32>
  %58 = bitcast <4 x i64> %h.i.sroa.32.0 to <8 x i32>
  %59 = bitcast <4 x i64> %h.i.sroa.38.0 to <8 x i32>
  %60 = bitcast <4 x i64> %h.i.sroa.44.0 to <8 x i32>
  %61 = bitcast <4 x i64> %h.i.sroa.0.0 to <8 x i32>
  %62 = bitcast <4 x i64> %h.i.sroa.8.0 to <8 x i32>
  %63 = bitcast <4 x i64> %h.i.sroa.14.0 to <8 x i32>
  %64 = bitcast <4 x i64> %h.i.sroa.20.0 to <8 x i32>
  %65 = bitcast <4 x i64> %h.i.sroa.26.0 to <8 x i32>
  %66 = bitcast <4 x i64> %h.i.sroa.32.0 to <8 x i32>
  %67 = bitcast <4 x i64> %h.i.sroa.38.0 to <8 x i32>
  %68 = bitcast <4 x i64> %h.i.sroa.44.0 to <8 x i32>
  %69 = getelementptr inbounds nuw i8, ptr %acc, i64 32
  br label %bb70.i

bb23.i:                                           ; preds = %_RNvXNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4archNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iNtB2_5Lanes9transpose.exit.i.1
  %70 = bitcast <4 x i64> %h.i.sroa.0.0 to <8 x i32>
  %71 = bitcast <4 x i64> %h.i.sroa.8.0 to <8 x i32>
  %72 = bitcast <4 x i64> %h.i.sroa.14.0 to <8 x i32>
  %73 = bitcast <4 x i64> %h.i.sroa.20.0 to <8 x i32>
  %74 = bitcast <4 x i64> %h.i.sroa.26.0 to <8 x i32>
  %75 = bitcast <4 x i64> %h.i.sroa.32.0 to <8 x i32>
  %76 = bitcast <4 x i64> %h.i.sroa.38.0 to <8 x i32>
  %77 = bitcast <4 x i64> %h.i.sroa.44.0 to <8 x i32>
  br label %bb3.i.i

bb3.i.i:                                          ; preds = %bb23.i, %bb3.i.i
  %iter.sroa.0.0.i.i3608 = phi i64 [ 0, %bb23.i ], [ %92, %bb3.i.i ]
  %78 = phi <8 x i32> [ %70, %bb23.i ], [ %_3.i1081, %bb3.i.i ]
  %79 = phi <8 x i32> [ %71, %bb23.i ], [ %_3.i1103, %bb3.i.i ]
  %80 = phi <8 x i32> [ %72, %bb23.i ], [ %_3.i1125, %bb3.i.i ]
  %81 = phi <8 x i32> [ %73, %bb23.i ], [ %_3.i1147, %bb3.i.i ]
  %82 = phi <8 x i32> [ %74, %bb23.i ], [ %_34.i11563581, %bb3.i.i ]
  %83 = phi <8 x i32> [ %75, %bb23.i ], [ %_34.i10903551, %bb3.i.i ]
  %84 = phi <8 x i32> [ %76, %bb23.i ], [ %_34.i11123561, %bb3.i.i ]
  %85 = phi <8 x i32> [ %77, %bb23.i ], [ %_34.i11343571, %bb3.i.i ]
  %86 = phi <8 x i32> [ splat (i32 1779033703), %bb23.i ], [ %_3.i1130, %bb3.i.i ]
  %87 = phi <8 x i32> [ splat (i32 -1150833019), %bb23.i ], [ %_3.i1152, %bb3.i.i ]
  %88 = phi <8 x i32> [ splat (i32 1013904242), %bb23.i ], [ %_3.i1086, %bb3.i.i ]
  %89 = phi <8 x i32> [ splat (i32 -1521486534), %bb23.i ], [ %_3.i1108, %bb3.i.i ]
  %90 = phi <8 x i32> [ zeroinitializer, %bb23.i ], [ %_34.i11073559, %bb3.i.i ]
  %91 = phi <8 x i32> [ zeroinitializer, %bb23.i ], [ %_34.i11293569, %bb3.i.i ]
  %v.i.i.sroa.137.03601 = phi <8 x i32> [ %11, %bb23.i ], [ %_34.i11513579, %bb3.i.i ]
  %v.i.i.sroa.146.03600 = phi <8 x i32> [ %8, %bb23.i ], [ %_34.i10853549, %bb3.i.i ]
  %92 = add nuw nsw i64 %iter.sroa.0.0.i.i3608, 1
  tail call void @llvm.experimental.noalias.scope.decl(metadata !92)
  %s.i1 = getelementptr inbounds nuw [16 x i64], ptr @alloc_61fb4a9344bbdaf2573accd6331d7e32, i64 %iter.sroa.0.0.i.i3608
  %93 = getelementptr inbounds nuw i8, ptr %s.i1, i64 8
  %_11.i = load i64, ptr %93, align 8, !noalias !95, !noundef !41
  %_8.i = load i64, ptr %s.i1, align 8, !noalias !95, !noundef !41
  %94 = getelementptr inbounds nuw <4 x i64>, ptr %m.i, i64 %_8.i
  %_7.i3506 = load <8 x i32>, ptr %94, align 32, !alias.scope !92, !noalias !105
  %95 = getelementptr inbounds nuw <4 x i64>, ptr %m.i, i64 %_11.i
  %_10.i3507 = load <8 x i32>, ptr %95, align 32, !alias.scope !92, !noalias !105
  %_3.i981 = add <8 x i32> %78, %82
  %_3.i982 = add <8 x i32> %_3.i981, %_7.i3506
  %96 = xor <8 x i32> %_3.i982, %90
  %_34.i9863509 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %96, <8 x i32> %96, <8 x i32> splat (i32 16))
  %_3.i987 = add <8 x i32> %_34.i9863509, %86
  %97 = xor <8 x i32> %_3.i987, %82
  %_34.i9913510 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %97, <8 x i32> %97, <8 x i32> splat (i32 20))
  %_3.i992 = add <8 x i32> %_10.i3507, %_3.i982
  %_3.i993 = add <8 x i32> %_3.i992, %_34.i9913510
  %_3.i9943511 = xor <8 x i32> %_3.i993, %_34.i9863509
  %_34.i9973512 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i9943511, <8 x i32> %_3.i9943511, <8 x i32> splat (i32 24))
  %_3.i998 = add <8 x i32> %_34.i9973512, %_3.i987
  %_3.i9993513 = xor <8 x i32> %_3.i998, %_34.i9913510
  %_34.i10023514 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i9993513, <8 x i32> %_3.i9993513, <8 x i32> splat (i32 25))
  %98 = getelementptr inbounds nuw i8, ptr %s.i1, i64 24
  %_18.i = load i64, ptr %98, align 8, !noalias !95, !noundef !41
  %99 = getelementptr inbounds nuw i8, ptr %s.i1, i64 16
  %_15.i = load i64, ptr %99, align 8, !noalias !95, !noundef !41
  %100 = getelementptr inbounds nuw <4 x i64>, ptr %m.i, i64 %_15.i
  %_14.i3515 = load <8 x i32>, ptr %100, align 32, !alias.scope !92, !noalias !105
  %101 = getelementptr inbounds nuw <4 x i64>, ptr %m.i, i64 %_18.i
  %_17.i3516 = load <8 x i32>, ptr %101, align 32, !alias.scope !92, !noalias !105
  %_3.i1003 = add <8 x i32> %79, %83
  %_3.i1004 = add <8 x i32> %_3.i1003, %_14.i3515
  %102 = xor <8 x i32> %_3.i1004, %91
  %_34.i10083518 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %102, <8 x i32> %102, <8 x i32> splat (i32 16))
  %_3.i1009 = add <8 x i32> %_34.i10083518, %87
  %103 = xor <8 x i32> %_3.i1009, %83
  %_34.i10133519 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %103, <8 x i32> %103, <8 x i32> splat (i32 20))
  %_3.i1014 = add <8 x i32> %_17.i3516, %_3.i1004
  %_3.i1015 = add <8 x i32> %_3.i1014, %_34.i10133519
  %_3.i10163520 = xor <8 x i32> %_3.i1015, %_34.i10083518
  %_34.i10193521 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i10163520, <8 x i32> %_3.i10163520, <8 x i32> splat (i32 24))
  %_3.i1020 = add <8 x i32> %_34.i10193521, %_3.i1009
  %_3.i10213522 = xor <8 x i32> %_3.i1020, %_34.i10133519
  %_34.i10243523 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i10213522, <8 x i32> %_3.i10213522, <8 x i32> splat (i32 25))
  %104 = getelementptr inbounds nuw i8, ptr %s.i1, i64 40
  %_25.i = load i64, ptr %104, align 8, !noalias !95, !noundef !41
  %105 = getelementptr inbounds nuw i8, ptr %s.i1, i64 32
  %_22.i = load i64, ptr %105, align 8, !noalias !95, !noundef !41
  %106 = getelementptr inbounds nuw <4 x i64>, ptr %m.i, i64 %_22.i
  %_21.i3524 = load <8 x i32>, ptr %106, align 32, !alias.scope !92, !noalias !105
  %107 = getelementptr inbounds nuw <4 x i64>, ptr %m.i, i64 %_25.i
  %_24.i23525 = load <8 x i32>, ptr %107, align 32, !alias.scope !92, !noalias !105
  %_3.i1025 = add <8 x i32> %80, %84
  %_3.i1026 = add <8 x i32> %_3.i1025, %_21.i3524
  %108 = xor <8 x i32> %_3.i1026, %v.i.i.sroa.137.03601
  %_34.i10303527 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %108, <8 x i32> %108, <8 x i32> splat (i32 16))
  %_3.i1031 = add <8 x i32> %_34.i10303527, %88
  %109 = xor <8 x i32> %_3.i1031, %84
  %_34.i10353528 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %109, <8 x i32> %109, <8 x i32> splat (i32 20))
  %_3.i1036 = add <8 x i32> %_24.i23525, %_3.i1026
  %_3.i1037 = add <8 x i32> %_3.i1036, %_34.i10353528
  %_3.i10383529 = xor <8 x i32> %_3.i1037, %_34.i10303527
  %_34.i10413530 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i10383529, <8 x i32> %_3.i10383529, <8 x i32> splat (i32 24))
  %_3.i1042 = add <8 x i32> %_34.i10413530, %_3.i1031
  %_3.i10433531 = xor <8 x i32> %_3.i1042, %_34.i10353528
  %_34.i10463532 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i10433531, <8 x i32> %_3.i10433531, <8 x i32> splat (i32 25))
  %110 = getelementptr inbounds nuw i8, ptr %s.i1, i64 56
  %_32.i = load i64, ptr %110, align 8, !noalias !95, !noundef !41
  %111 = getelementptr inbounds nuw i8, ptr %s.i1, i64 48
  %_29.i = load i64, ptr %111, align 8, !noalias !95, !noundef !41
  %112 = getelementptr inbounds nuw <4 x i64>, ptr %m.i, i64 %_29.i
  %_28.i33533 = load <8 x i32>, ptr %112, align 32, !alias.scope !92, !noalias !105
  %113 = getelementptr inbounds nuw <4 x i64>, ptr %m.i, i64 %_32.i
  %_31.i3534 = load <8 x i32>, ptr %113, align 32, !alias.scope !92, !noalias !105
  %_3.i1047 = add <8 x i32> %81, %85
  %_3.i1048 = add <8 x i32> %_3.i1047, %_28.i33533
  %114 = xor <8 x i32> %_3.i1048, %v.i.i.sroa.146.03600
  %_34.i10523536 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %114, <8 x i32> %114, <8 x i32> splat (i32 16))
  %_3.i1053 = add <8 x i32> %_34.i10523536, %89
  %115 = xor <8 x i32> %_3.i1053, %85
  %_34.i10573537 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %115, <8 x i32> %115, <8 x i32> splat (i32 20))
  %_3.i1058 = add <8 x i32> %_31.i3534, %_3.i1048
  %_3.i1059 = add <8 x i32> %_3.i1058, %_34.i10573537
  %_3.i10603538 = xor <8 x i32> %_3.i1059, %_34.i10523536
  %_34.i10633539 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i10603538, <8 x i32> %_3.i10603538, <8 x i32> splat (i32 24))
  %_3.i1064 = add <8 x i32> %_34.i10633539, %_3.i1053
  %_3.i10653540 = xor <8 x i32> %_3.i1064, %_34.i10573537
  %_34.i10683541 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i10653540, <8 x i32> %_3.i10653540, <8 x i32> splat (i32 25))
  %116 = getelementptr inbounds nuw i8, ptr %s.i1, i64 72
  %_39.i = load i64, ptr %116, align 8, !noalias !95, !noundef !41
  %117 = getelementptr inbounds nuw i8, ptr %s.i1, i64 64
  %_36.i = load i64, ptr %117, align 8, !noalias !95, !noundef !41
  %118 = getelementptr inbounds nuw <4 x i64>, ptr %m.i, i64 %_36.i
  %_35.i43542 = load <8 x i32>, ptr %118, align 32, !alias.scope !92, !noalias !105
  %119 = getelementptr inbounds nuw <4 x i64>, ptr %m.i, i64 %_39.i
  %_38.i3543 = load <8 x i32>, ptr %119, align 32, !alias.scope !92, !noalias !105
  %_3.i1069 = add <8 x i32> %_35.i43542, %_3.i993
  %_3.i1070 = add <8 x i32> %_3.i1069, %_34.i10243523
  %_3.i10713544 = xor <8 x i32> %_34.i10633539, %_3.i1070
  %_34.i10743545 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i10713544, <8 x i32> %_3.i10713544, <8 x i32> splat (i32 16))
  %_3.i1075 = add <8 x i32> %_34.i10743545, %_3.i1042
  %_3.i10763546 = xor <8 x i32> %_3.i1075, %_34.i10243523
  %_34.i10793547 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i10763546, <8 x i32> %_3.i10763546, <8 x i32> splat (i32 20))
  %_3.i1080 = add <8 x i32> %_3.i1070, %_38.i3543
  %_3.i1081 = add <8 x i32> %_3.i1080, %_34.i10793547
  %_3.i10823548 = xor <8 x i32> %_3.i1081, %_34.i10743545
  %_34.i10853549 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i10823548, <8 x i32> %_3.i10823548, <8 x i32> splat (i32 24))
  %_3.i1086 = add <8 x i32> %_34.i10853549, %_3.i1075
  %_3.i10873550 = xor <8 x i32> %_3.i1086, %_34.i10793547
  %_34.i10903551 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i10873550, <8 x i32> %_3.i10873550, <8 x i32> splat (i32 25))
  %120 = getelementptr inbounds nuw i8, ptr %s.i1, i64 88
  %_46.i = load i64, ptr %120, align 8, !noalias !95, !noundef !41
  %121 = getelementptr inbounds nuw i8, ptr %s.i1, i64 80
  %_43.i = load i64, ptr %121, align 8, !noalias !95, !noundef !41
  %122 = getelementptr inbounds nuw <4 x i64>, ptr %m.i, i64 %_43.i
  %_42.i3552 = load <8 x i32>, ptr %122, align 32, !alias.scope !92, !noalias !105
  %123 = getelementptr inbounds nuw <4 x i64>, ptr %m.i, i64 %_46.i
  %_45.i3553 = load <8 x i32>, ptr %123, align 32, !alias.scope !92, !noalias !105
  %_3.i1091 = add <8 x i32> %_42.i3552, %_3.i1015
  %_3.i1092 = add <8 x i32> %_3.i1091, %_34.i10463532
  %_3.i10933554 = xor <8 x i32> %_3.i1092, %_34.i9973512
  %_34.i10963555 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i10933554, <8 x i32> %_3.i10933554, <8 x i32> splat (i32 16))
  %_3.i1097 = add <8 x i32> %_34.i10963555, %_3.i1064
  %_3.i10983556 = xor <8 x i32> %_3.i1097, %_34.i10463532
  %_34.i11013557 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i10983556, <8 x i32> %_3.i10983556, <8 x i32> splat (i32 20))
  %_3.i1102 = add <8 x i32> %_3.i1092, %_45.i3553
  %_3.i1103 = add <8 x i32> %_3.i1102, %_34.i11013557
  %_3.i11043558 = xor <8 x i32> %_3.i1103, %_34.i10963555
  %_34.i11073559 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i11043558, <8 x i32> %_3.i11043558, <8 x i32> splat (i32 24))
  %_3.i1108 = add <8 x i32> %_34.i11073559, %_3.i1097
  %_3.i11093560 = xor <8 x i32> %_3.i1108, %_34.i11013557
  %_34.i11123561 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i11093560, <8 x i32> %_3.i11093560, <8 x i32> splat (i32 25))
  %124 = getelementptr inbounds nuw i8, ptr %s.i1, i64 104
  %_53.i = load i64, ptr %124, align 8, !noalias !95, !noundef !41
  %125 = getelementptr inbounds nuw i8, ptr %s.i1, i64 96
  %_50.i6 = load i64, ptr %125, align 8, !noalias !95, !noundef !41
  %126 = getelementptr inbounds nuw <4 x i64>, ptr %m.i, i64 %_50.i6
  %_49.i3562 = load <8 x i32>, ptr %126, align 32, !alias.scope !92, !noalias !105
  %127 = getelementptr inbounds nuw <4 x i64>, ptr %m.i, i64 %_53.i
  %_52.i73563 = load <8 x i32>, ptr %127, align 32, !alias.scope !92, !noalias !105
  %_3.i1113 = add <8 x i32> %_49.i3562, %_3.i1037
  %_3.i1114 = add <8 x i32> %_3.i1113, %_34.i10683541
  %_3.i11153564 = xor <8 x i32> %_3.i1114, %_34.i10193521
  %_34.i11183565 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i11153564, <8 x i32> %_3.i11153564, <8 x i32> splat (i32 16))
  %_3.i1119 = add <8 x i32> %_34.i11183565, %_3.i998
  %_3.i11203566 = xor <8 x i32> %_3.i1119, %_34.i10683541
  %_34.i11233567 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i11203566, <8 x i32> %_3.i11203566, <8 x i32> splat (i32 20))
  %_3.i1124 = add <8 x i32> %_3.i1114, %_52.i73563
  %_3.i1125 = add <8 x i32> %_3.i1124, %_34.i11233567
  %_3.i11263568 = xor <8 x i32> %_3.i1125, %_34.i11183565
  %_34.i11293569 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i11263568, <8 x i32> %_3.i11263568, <8 x i32> splat (i32 24))
  %_3.i1130 = add <8 x i32> %_34.i11293569, %_3.i1119
  %_3.i11313570 = xor <8 x i32> %_3.i1130, %_34.i11233567
  %_34.i11343571 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i11313570, <8 x i32> %_3.i11313570, <8 x i32> splat (i32 25))
  %128 = getelementptr inbounds nuw i8, ptr %s.i1, i64 120
  %_60.i = load i64, ptr %128, align 8, !noalias !95, !noundef !41
  %129 = getelementptr inbounds nuw i8, ptr %s.i1, i64 112
  %_57.i8 = load i64, ptr %129, align 8, !noalias !95, !noundef !41
  %130 = getelementptr inbounds nuw <4 x i64>, ptr %m.i, i64 %_57.i8
  %_56.i3572 = load <8 x i32>, ptr %130, align 32, !alias.scope !92, !noalias !105
  %131 = getelementptr inbounds nuw <4 x i64>, ptr %m.i, i64 %_60.i
  %_59.i3573 = load <8 x i32>, ptr %131, align 32, !alias.scope !92, !noalias !105
  %_3.i1135 = add <8 x i32> %_3.i1059, %_34.i10023514
  %_3.i1136 = add <8 x i32> %_3.i1135, %_56.i3572
  %_3.i11373574 = xor <8 x i32> %_3.i1136, %_34.i10413530
  %_34.i11403575 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i11373574, <8 x i32> %_3.i11373574, <8 x i32> splat (i32 16))
  %_3.i1141 = add <8 x i32> %_34.i11403575, %_3.i1020
  %_3.i11423576 = xor <8 x i32> %_3.i1141, %_34.i10023514
  %_34.i11453577 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i11423576, <8 x i32> %_3.i11423576, <8 x i32> splat (i32 20))
  %_3.i1146 = add <8 x i32> %_59.i3573, %_3.i1136
  %_3.i1147 = add <8 x i32> %_3.i1146, %_34.i11453577
  %_3.i11483578 = xor <8 x i32> %_3.i1147, %_34.i11403575
  %_34.i11513579 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i11483578, <8 x i32> %_3.i11483578, <8 x i32> splat (i32 24))
  %_3.i1152 = add <8 x i32> %_34.i11513579, %_3.i1141
  %_3.i11533580 = xor <8 x i32> %_3.i1152, %_34.i11453577
  %_34.i11563581 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i11533580, <8 x i32> %_3.i11533580, <8 x i32> splat (i32 25))
  %exitcond.not = icmp eq i64 %92, 7
  br i1 %exitcond.not, label %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit.i, label %bb3.i.i

_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit.i: ; preds = %bb3.i.i
  %132 = sext <8 x i1> %4 to <8 x i32>
  %133 = bitcast <8 x i32> %132 to <32 x i8>
  %134 = icmp slt <32 x i8> %133, zeroinitializer
  %_3.i13683787 = xor <8 x i32> %_3.i1130, %_3.i1081
  %135 = bitcast <4 x i64> %h.i.sroa.0.0 to <32 x i8>
  %136 = bitcast <8 x i32> %_3.i13683787 to <32 x i8>
  %_6.i1369 = select <32 x i1> %134, <32 x i8> %136, <32 x i8> %135
  %137 = bitcast <32 x i8> %_6.i1369 to <4 x i64>
  %_3.i1368.13788 = xor <8 x i32> %_3.i1152, %_3.i1103
  %138 = bitcast <4 x i64> %h.i.sroa.8.0 to <32 x i8>
  %139 = bitcast <8 x i32> %_3.i1368.13788 to <32 x i8>
  %_6.i1369.1 = select <32 x i1> %134, <32 x i8> %139, <32 x i8> %138
  %140 = bitcast <32 x i8> %_6.i1369.1 to <4 x i64>
  %_3.i1368.23789 = xor <8 x i32> %_3.i1086, %_3.i1125
  %141 = bitcast <4 x i64> %h.i.sroa.14.0 to <32 x i8>
  %142 = bitcast <8 x i32> %_3.i1368.23789 to <32 x i8>
  %_6.i1369.2 = select <32 x i1> %134, <32 x i8> %142, <32 x i8> %141
  %143 = bitcast <32 x i8> %_6.i1369.2 to <4 x i64>
  %_3.i1368.33790 = xor <8 x i32> %_3.i1108, %_3.i1147
  %144 = bitcast <4 x i64> %h.i.sroa.20.0 to <32 x i8>
  %145 = bitcast <8 x i32> %_3.i1368.33790 to <32 x i8>
  %_6.i1369.3 = select <32 x i1> %134, <32 x i8> %145, <32 x i8> %144
  %146 = bitcast <32 x i8> %_6.i1369.3 to <4 x i64>
  %_3.i1368.43791 = xor <8 x i32> %_34.i11073559, %_34.i11563581
  %147 = bitcast <4 x i64> %h.i.sroa.26.0 to <32 x i8>
  %148 = bitcast <8 x i32> %_3.i1368.43791 to <32 x i8>
  %_6.i1369.4 = select <32 x i1> %134, <32 x i8> %148, <32 x i8> %147
  %149 = bitcast <32 x i8> %_6.i1369.4 to <4 x i64>
  %_3.i1368.53792 = xor <8 x i32> %_34.i11293569, %_34.i10903551
  %150 = bitcast <4 x i64> %h.i.sroa.32.0 to <32 x i8>
  %151 = bitcast <8 x i32> %_3.i1368.53792 to <32 x i8>
  %_6.i1369.5 = select <32 x i1> %134, <32 x i8> %151, <32 x i8> %150
  %152 = bitcast <32 x i8> %_6.i1369.5 to <4 x i64>
  %_3.i1368.63793 = xor <8 x i32> %_34.i11513579, %_34.i11123561
  %153 = bitcast <4 x i64> %h.i.sroa.38.0 to <32 x i8>
  %154 = bitcast <8 x i32> %_3.i1368.63793 to <32 x i8>
  %_6.i1369.6 = select <32 x i1> %134, <32 x i8> %154, <32 x i8> %153
  %155 = bitcast <32 x i8> %_6.i1369.6 to <4 x i64>
  %_3.i1368.73794 = xor <8 x i32> %_34.i10853549, %_34.i11343571
  %156 = bitcast <4 x i64> %h.i.sroa.44.0 to <32 x i8>
  %157 = bitcast <8 x i32> %_3.i1368.73794 to <32 x i8>
  %_6.i1369.7 = select <32 x i1> %134, <32 x i8> %157, <32 x i8> %156
  %158 = bitcast <32 x i8> %_6.i1369.7 to <4 x i64>
  %159 = select <8 x i1> %4, <8 x i64> %2, <8 x i64> %1
  call void @llvm.lifetime.end.p0(ptr nonnull %m.i), !noalias !58
  br label %bb3.i

bb70.i:                                           ; preds = %bb24.i, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit57.i
  %iter4.sroa.0.0.i3624 = phi i64 [ 0, %bb24.i ], [ %271, %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit57.i ]
  %_87.i = trunc nuw nsw i64 %iter4.sroa.0.0.i3624 to i32
  %160 = insertelement <8 x i32> poison, i32 %_87.i, i64 0
  %161 = shufflevector <8 x i32> %160, <8 x i32> poison, <8 x i32> zeroinitializer
  br label %bb3.i56.i

bb3.i56.i:                                        ; preds = %bb70.i, %bb3.i56.i
  %iter.sroa.0.0.i54.i3619 = phi i64 [ 0, %bb70.i ], [ %175, %bb3.i56.i ]
  %162 = phi <8 x i32> [ %53, %bb70.i ], [ %_3.i1265, %bb3.i56.i ]
  %163 = phi <8 x i32> [ %54, %bb70.i ], [ %_3.i1287, %bb3.i56.i ]
  %164 = phi <8 x i32> [ %55, %bb70.i ], [ %_3.i1309, %bb3.i56.i ]
  %165 = phi <8 x i32> [ %56, %bb70.i ], [ %_3.i1331, %bb3.i56.i ]
  %166 = phi <8 x i32> [ %57, %bb70.i ], [ %_34.i13403504, %bb3.i56.i ]
  %167 = phi <8 x i32> [ %58, %bb70.i ], [ %_34.i12743474, %bb3.i56.i ]
  %168 = phi <8 x i32> [ %59, %bb70.i ], [ %_34.i12963484, %bb3.i56.i ]
  %169 = phi <8 x i32> [ %60, %bb70.i ], [ %_34.i13183494, %bb3.i56.i ]
  %170 = phi <8 x i32> [ splat (i32 1779033703), %bb70.i ], [ %_3.i1314, %bb3.i56.i ]
  %171 = phi <8 x i32> [ splat (i32 -1150833019), %bb70.i ], [ %_3.i1336, %bb3.i56.i ]
  %172 = phi <8 x i32> [ splat (i32 1013904242), %bb70.i ], [ %_3.i1270, %bb3.i56.i ]
  %173 = phi <8 x i32> [ splat (i32 -1521486534), %bb70.i ], [ %_3.i1292, %bb3.i56.i ]
  %v.i40.i.sroa.119.0.in3614 = phi <8 x i32> [ %161, %bb70.i ], [ %_34.i12913482, %bb3.i56.i ]
  %174 = phi <8 x i32> [ zeroinitializer, %bb70.i ], [ %_34.i13133492, %bb3.i56.i ]
  %v.i40.i.sroa.137.03612 = phi <8 x i32> [ %11, %bb70.i ], [ %_34.i13353502, %bb3.i56.i ]
  %v.i40.i.sroa.146.03611 = phi <8 x i32> [ %8, %bb70.i ], [ %_34.i12693472, %bb3.i56.i ]
  %175 = add nuw nsw i64 %iter.sroa.0.0.i54.i3619, 1
  tail call void @llvm.experimental.noalias.scope.decl(metadata !106)
  %s.i18 = getelementptr inbounds nuw [16 x i64], ptr @alloc_61fb4a9344bbdaf2573accd6331d7e32, i64 %iter.sroa.0.0.i54.i3619
  %176 = getelementptr inbounds nuw i8, ptr %s.i18, i64 8
  %_11.i19 = load i64, ptr %176, align 8, !noalias !109, !noundef !41
  %_8.i20 = load i64, ptr %s.i18, align 8, !noalias !109, !noundef !41
  %177 = getelementptr inbounds nuw <4 x i64>, ptr %root_m.i, i64 %_8.i20
  %_7.i213429 = load <8 x i32>, ptr %177, align 32, !alias.scope !106, !noalias !119
  %178 = getelementptr inbounds nuw <4 x i64>, ptr %root_m.i, i64 %_11.i19
  %_10.i223430 = load <8 x i32>, ptr %178, align 32, !alias.scope !106, !noalias !119
  %_3.i1165 = add <8 x i32> %162, %166
  %_3.i1166 = add <8 x i32> %_3.i1165, %_7.i213429
  %179 = xor <8 x i32> %_3.i1166, %v.i40.i.sroa.119.0.in3614
  %_34.i11703432 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %179, <8 x i32> %179, <8 x i32> splat (i32 16))
  %_3.i1171 = add <8 x i32> %_34.i11703432, %170
  %180 = xor <8 x i32> %_3.i1171, %166
  %_34.i11753433 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %180, <8 x i32> %180, <8 x i32> splat (i32 20))
  %_3.i1176 = add <8 x i32> %_10.i223430, %_3.i1166
  %_3.i1177 = add <8 x i32> %_3.i1176, %_34.i11753433
  %_3.i11783434 = xor <8 x i32> %_3.i1177, %_34.i11703432
  %_34.i11813435 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i11783434, <8 x i32> %_3.i11783434, <8 x i32> splat (i32 24))
  %_3.i1182 = add <8 x i32> %_34.i11813435, %_3.i1171
  %_3.i11833436 = xor <8 x i32> %_3.i1182, %_34.i11753433
  %_34.i11863437 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i11833436, <8 x i32> %_3.i11833436, <8 x i32> splat (i32 25))
  %181 = getelementptr inbounds nuw i8, ptr %s.i18, i64 24
  %_18.i46 = load i64, ptr %181, align 8, !noalias !109, !noundef !41
  %182 = getelementptr inbounds nuw i8, ptr %s.i18, i64 16
  %_15.i47 = load i64, ptr %182, align 8, !noalias !109, !noundef !41
  %183 = getelementptr inbounds nuw <4 x i64>, ptr %root_m.i, i64 %_15.i47
  %_14.i483438 = load <8 x i32>, ptr %183, align 32, !alias.scope !106, !noalias !119
  %184 = getelementptr inbounds nuw <4 x i64>, ptr %root_m.i, i64 %_18.i46
  %_17.i493439 = load <8 x i32>, ptr %184, align 32, !alias.scope !106, !noalias !119
  %_3.i1187 = add <8 x i32> %163, %167
  %_3.i1188 = add <8 x i32> %_3.i1187, %_14.i483438
  %185 = xor <8 x i32> %_3.i1188, %174
  %_34.i11923441 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %185, <8 x i32> %185, <8 x i32> splat (i32 16))
  %_3.i1193 = add <8 x i32> %_34.i11923441, %171
  %186 = xor <8 x i32> %_3.i1193, %167
  %_34.i11973442 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %186, <8 x i32> %186, <8 x i32> splat (i32 20))
  %_3.i1198 = add <8 x i32> %_17.i493439, %_3.i1188
  %_3.i1199 = add <8 x i32> %_3.i1198, %_34.i11973442
  %_3.i12003443 = xor <8 x i32> %_3.i1199, %_34.i11923441
  %_34.i12033444 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i12003443, <8 x i32> %_3.i12003443, <8 x i32> splat (i32 24))
  %_3.i1204 = add <8 x i32> %_34.i12033444, %_3.i1193
  %_3.i12053445 = xor <8 x i32> %_3.i1204, %_34.i11973442
  %_34.i12083446 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i12053445, <8 x i32> %_3.i12053445, <8 x i32> splat (i32 25))
  %187 = getelementptr inbounds nuw i8, ptr %s.i18, i64 40
  %_25.i73 = load i64, ptr %187, align 8, !noalias !109, !noundef !41
  %188 = getelementptr inbounds nuw i8, ptr %s.i18, i64 32
  %_22.i74 = load i64, ptr %188, align 8, !noalias !109, !noundef !41
  %189 = getelementptr inbounds nuw <4 x i64>, ptr %root_m.i, i64 %_22.i74
  %_21.i753447 = load <8 x i32>, ptr %189, align 32, !alias.scope !106, !noalias !119
  %190 = getelementptr inbounds nuw <4 x i64>, ptr %root_m.i, i64 %_25.i73
  %_24.i763448 = load <8 x i32>, ptr %190, align 32, !alias.scope !106, !noalias !119
  %_3.i1209 = add <8 x i32> %164, %168
  %_3.i1210 = add <8 x i32> %_3.i1209, %_21.i753447
  %191 = xor <8 x i32> %_3.i1210, %v.i40.i.sroa.137.03612
  %_34.i12143450 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %191, <8 x i32> %191, <8 x i32> splat (i32 16))
  %_3.i1215 = add <8 x i32> %_34.i12143450, %172
  %192 = xor <8 x i32> %_3.i1215, %168
  %_34.i12193451 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %192, <8 x i32> %192, <8 x i32> splat (i32 20))
  %_3.i1220 = add <8 x i32> %_24.i763448, %_3.i1210
  %_3.i1221 = add <8 x i32> %_3.i1220, %_34.i12193451
  %_3.i12223452 = xor <8 x i32> %_3.i1221, %_34.i12143450
  %_34.i12253453 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i12223452, <8 x i32> %_3.i12223452, <8 x i32> splat (i32 24))
  %_3.i1226 = add <8 x i32> %_34.i12253453, %_3.i1215
  %_3.i12273454 = xor <8 x i32> %_3.i1226, %_34.i12193451
  %_34.i12303455 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i12273454, <8 x i32> %_3.i12273454, <8 x i32> splat (i32 25))
  %193 = getelementptr inbounds nuw i8, ptr %s.i18, i64 56
  %_32.i100 = load i64, ptr %193, align 8, !noalias !109, !noundef !41
  %194 = getelementptr inbounds nuw i8, ptr %s.i18, i64 48
  %_29.i101 = load i64, ptr %194, align 8, !noalias !109, !noundef !41
  %195 = getelementptr inbounds nuw <4 x i64>, ptr %root_m.i, i64 %_29.i101
  %_28.i1023456 = load <8 x i32>, ptr %195, align 32, !alias.scope !106, !noalias !119
  %196 = getelementptr inbounds nuw <4 x i64>, ptr %root_m.i, i64 %_32.i100
  %_31.i1033457 = load <8 x i32>, ptr %196, align 32, !alias.scope !106, !noalias !119
  %_3.i1231 = add <8 x i32> %165, %169
  %_3.i1232 = add <8 x i32> %_3.i1231, %_28.i1023456
  %197 = xor <8 x i32> %_3.i1232, %v.i40.i.sroa.146.03611
  %_34.i12363459 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %197, <8 x i32> %197, <8 x i32> splat (i32 16))
  %_3.i1237 = add <8 x i32> %_34.i12363459, %173
  %198 = xor <8 x i32> %_3.i1237, %169
  %_34.i12413460 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %198, <8 x i32> %198, <8 x i32> splat (i32 20))
  %_3.i1242 = add <8 x i32> %_31.i1033457, %_3.i1232
  %_3.i1243 = add <8 x i32> %_3.i1242, %_34.i12413460
  %_3.i12443461 = xor <8 x i32> %_3.i1243, %_34.i12363459
  %_34.i12473462 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i12443461, <8 x i32> %_3.i12443461, <8 x i32> splat (i32 24))
  %_3.i1248 = add <8 x i32> %_34.i12473462, %_3.i1237
  %_3.i12493463 = xor <8 x i32> %_3.i1248, %_34.i12413460
  %_34.i12523464 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i12493463, <8 x i32> %_3.i12493463, <8 x i32> splat (i32 25))
  %199 = getelementptr inbounds nuw i8, ptr %s.i18, i64 72
  %_39.i127 = load i64, ptr %199, align 8, !noalias !109, !noundef !41
  %200 = getelementptr inbounds nuw i8, ptr %s.i18, i64 64
  %_36.i128 = load i64, ptr %200, align 8, !noalias !109, !noundef !41
  %201 = getelementptr inbounds nuw <4 x i64>, ptr %root_m.i, i64 %_36.i128
  %_35.i1293465 = load <8 x i32>, ptr %201, align 32, !alias.scope !106, !noalias !119
  %202 = getelementptr inbounds nuw <4 x i64>, ptr %root_m.i, i64 %_39.i127
  %_38.i1303466 = load <8 x i32>, ptr %202, align 32, !alias.scope !106, !noalias !119
  %_3.i1253 = add <8 x i32> %_35.i1293465, %_3.i1177
  %_3.i1254 = add <8 x i32> %_3.i1253, %_34.i12083446
  %_3.i12553467 = xor <8 x i32> %_34.i12473462, %_3.i1254
  %_34.i12583468 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i12553467, <8 x i32> %_3.i12553467, <8 x i32> splat (i32 16))
  %_3.i1259 = add <8 x i32> %_34.i12583468, %_3.i1226
  %_3.i12603469 = xor <8 x i32> %_3.i1259, %_34.i12083446
  %_34.i12633470 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i12603469, <8 x i32> %_3.i12603469, <8 x i32> splat (i32 20))
  %_3.i1264 = add <8 x i32> %_3.i1254, %_38.i1303466
  %_3.i1265 = add <8 x i32> %_3.i1264, %_34.i12633470
  %_3.i12663471 = xor <8 x i32> %_3.i1265, %_34.i12583468
  %_34.i12693472 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i12663471, <8 x i32> %_3.i12663471, <8 x i32> splat (i32 24))
  %_3.i1270 = add <8 x i32> %_34.i12693472, %_3.i1259
  %_3.i12713473 = xor <8 x i32> %_3.i1270, %_34.i12633470
  %_34.i12743474 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i12713473, <8 x i32> %_3.i12713473, <8 x i32> splat (i32 25))
  %203 = getelementptr inbounds nuw i8, ptr %s.i18, i64 88
  %_46.i154 = load i64, ptr %203, align 8, !noalias !109, !noundef !41
  %204 = getelementptr inbounds nuw i8, ptr %s.i18, i64 80
  %_43.i155 = load i64, ptr %204, align 8, !noalias !109, !noundef !41
  %205 = getelementptr inbounds nuw <4 x i64>, ptr %root_m.i, i64 %_43.i155
  %_42.i1563475 = load <8 x i32>, ptr %205, align 32, !alias.scope !106, !noalias !119
  %206 = getelementptr inbounds nuw <4 x i64>, ptr %root_m.i, i64 %_46.i154
  %_45.i1573476 = load <8 x i32>, ptr %206, align 32, !alias.scope !106, !noalias !119
  %_3.i1275 = add <8 x i32> %_42.i1563475, %_3.i1199
  %_3.i1276 = add <8 x i32> %_3.i1275, %_34.i12303455
  %_3.i12773477 = xor <8 x i32> %_3.i1276, %_34.i11813435
  %_34.i12803478 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i12773477, <8 x i32> %_3.i12773477, <8 x i32> splat (i32 16))
  %_3.i1281 = add <8 x i32> %_34.i12803478, %_3.i1248
  %_3.i12823479 = xor <8 x i32> %_3.i1281, %_34.i12303455
  %_34.i12853480 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i12823479, <8 x i32> %_3.i12823479, <8 x i32> splat (i32 20))
  %_3.i1286 = add <8 x i32> %_3.i1276, %_45.i1573476
  %_3.i1287 = add <8 x i32> %_3.i1286, %_34.i12853480
  %_3.i12883481 = xor <8 x i32> %_3.i1287, %_34.i12803478
  %_34.i12913482 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i12883481, <8 x i32> %_3.i12883481, <8 x i32> splat (i32 24))
  %_3.i1292 = add <8 x i32> %_34.i12913482, %_3.i1281
  %_3.i12933483 = xor <8 x i32> %_3.i1292, %_34.i12853480
  %_34.i12963484 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i12933483, <8 x i32> %_3.i12933483, <8 x i32> splat (i32 25))
  %207 = getelementptr inbounds nuw i8, ptr %s.i18, i64 104
  %_53.i181 = load i64, ptr %207, align 8, !noalias !109, !noundef !41
  %208 = getelementptr inbounds nuw i8, ptr %s.i18, i64 96
  %_50.i182 = load i64, ptr %208, align 8, !noalias !109, !noundef !41
  %209 = getelementptr inbounds nuw <4 x i64>, ptr %root_m.i, i64 %_50.i182
  %_49.i1833485 = load <8 x i32>, ptr %209, align 32, !alias.scope !106, !noalias !119
  %210 = getelementptr inbounds nuw <4 x i64>, ptr %root_m.i, i64 %_53.i181
  %_52.i1843486 = load <8 x i32>, ptr %210, align 32, !alias.scope !106, !noalias !119
  %_3.i1297 = add <8 x i32> %_49.i1833485, %_3.i1221
  %_3.i1298 = add <8 x i32> %_3.i1297, %_34.i12523464
  %_3.i12993487 = xor <8 x i32> %_3.i1298, %_34.i12033444
  %_34.i13023488 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i12993487, <8 x i32> %_3.i12993487, <8 x i32> splat (i32 16))
  %_3.i1303 = add <8 x i32> %_34.i13023488, %_3.i1182
  %_3.i13043489 = xor <8 x i32> %_3.i1303, %_34.i12523464
  %_34.i13073490 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i13043489, <8 x i32> %_3.i13043489, <8 x i32> splat (i32 20))
  %_3.i1308 = add <8 x i32> %_3.i1298, %_52.i1843486
  %_3.i1309 = add <8 x i32> %_3.i1308, %_34.i13073490
  %_3.i13103491 = xor <8 x i32> %_3.i1309, %_34.i13023488
  %_34.i13133492 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i13103491, <8 x i32> %_3.i13103491, <8 x i32> splat (i32 24))
  %_3.i1314 = add <8 x i32> %_34.i13133492, %_3.i1303
  %_3.i13153493 = xor <8 x i32> %_3.i1314, %_34.i13073490
  %_34.i13183494 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i13153493, <8 x i32> %_3.i13153493, <8 x i32> splat (i32 25))
  %211 = getelementptr inbounds nuw i8, ptr %s.i18, i64 120
  %_60.i208 = load i64, ptr %211, align 8, !noalias !109, !noundef !41
  %212 = getelementptr inbounds nuw i8, ptr %s.i18, i64 112
  %_57.i209 = load i64, ptr %212, align 8, !noalias !109, !noundef !41
  %213 = getelementptr inbounds nuw <4 x i64>, ptr %root_m.i, i64 %_57.i209
  %_56.i2103495 = load <8 x i32>, ptr %213, align 32, !alias.scope !106, !noalias !119
  %214 = getelementptr inbounds nuw <4 x i64>, ptr %root_m.i, i64 %_60.i208
  %_59.i2113496 = load <8 x i32>, ptr %214, align 32, !alias.scope !106, !noalias !119
  %_3.i1319 = add <8 x i32> %_3.i1243, %_34.i11863437
  %_3.i1320 = add <8 x i32> %_3.i1319, %_56.i2103495
  %_3.i13213497 = xor <8 x i32> %_3.i1320, %_34.i12253453
  %_34.i13243498 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i13213497, <8 x i32> %_3.i13213497, <8 x i32> splat (i32 16))
  %_3.i1325 = add <8 x i32> %_34.i13243498, %_3.i1204
  %_3.i13263499 = xor <8 x i32> %_3.i1325, %_34.i11863437
  %_34.i13293500 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i13263499, <8 x i32> %_3.i13263499, <8 x i32> splat (i32 20))
  %_3.i1330 = add <8 x i32> %_59.i2113496, %_3.i1320
  %_3.i1331 = add <8 x i32> %_3.i1330, %_34.i13293500
  %_3.i13323501 = xor <8 x i32> %_3.i1331, %_34.i13243498
  %_34.i13353502 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i13323501, <8 x i32> %_3.i13323501, <8 x i32> splat (i32 24))
  %_3.i1336 = add <8 x i32> %_34.i13353502, %_3.i1325
  %_3.i13373503 = xor <8 x i32> %_3.i1336, %_34.i13293500
  %_34.i13403504 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i13373503, <8 x i32> %_3.i13373503, <8 x i32> splat (i32 25))
  %exitcond3637.not = icmp eq i64 %175, 7
  br i1 %exitcond3637.not, label %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit57.i, label %bb3.i56.i

_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit57.i: ; preds = %bb3.i56.i
  %_3.i13413779 = xor <8 x i32> %_3.i1314, %_3.i1265
  %_3.i1341.13780 = xor <8 x i32> %_3.i1336, %_3.i1287
  %_3.i1341.23781 = xor <8 x i32> %_3.i1270, %_3.i1309
  %_3.i1341.33782 = xor <8 x i32> %_3.i1292, %_3.i1331
  %_3.i1341.43783 = xor <8 x i32> %_34.i12913482, %_34.i13403504
  %_3.i1341.53784 = xor <8 x i32> %_34.i13133492, %_34.i12743474
  %_3.i1341.63785 = xor <8 x i32> %_34.i13353502, %_34.i12963484
  %_3.i1341.73786 = xor <8 x i32> %_34.i12693472, %_34.i13183494
  %r.i = shufflevector <8 x i32> %_3.i13413779, <8 x i32> %_3.i1341.13780, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1343 = shufflevector <8 x i32> %_3.i13413779, <8 x i32> %_3.i1341.13780, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %r.i1344 = shufflevector <8 x i32> %_3.i1341.23781, <8 x i32> %_3.i1341.33782, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1345 = shufflevector <8 x i32> %_3.i1341.23781, <8 x i32> %_3.i1341.33782, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %r.i1346 = shufflevector <8 x i32> %_3.i1341.43783, <8 x i32> %_3.i1341.53784, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1347 = shufflevector <8 x i32> %_3.i1341.43783, <8 x i32> %_3.i1341.53784, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %r.i1348 = shufflevector <8 x i32> %_3.i1341.63785, <8 x i32> %_3.i1341.73786, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1349 = shufflevector <8 x i32> %_3.i1341.63785, <8 x i32> %_3.i1341.73786, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %215 = shufflevector <8 x i32> %r.i, <8 x i32> %r.i1344, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %216 = shufflevector <8 x i32> %r.i, <8 x i32> %r.i1344, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %217 = shufflevector <8 x i32> %r.i1343, <8 x i32> %r.i1345, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %218 = shufflevector <8 x i32> %r.i1343, <8 x i32> %r.i1345, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %219 = shufflevector <8 x i32> %r.i1346, <8 x i32> %r.i1348, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %220 = shufflevector <8 x i32> %r.i1346, <8 x i32> %r.i1348, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %221 = shufflevector <8 x i32> %r.i1347, <8 x i32> %r.i1349, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %222 = shufflevector <8 x i32> %r.i1347, <8 x i32> %r.i1349, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %223 = shufflevector <8 x i32> %215, <8 x i32> %219, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  %224 = shufflevector <8 x i32> %216, <8 x i32> %220, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  %225 = shufflevector <8 x i32> %217, <8 x i32> %221, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  %226 = shufflevector <8 x i32> %218, <8 x i32> %222, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  %227 = shufflevector <8 x i32> %215, <8 x i32> %219, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  %228 = shufflevector <8 x i32> %216, <8 x i32> %220, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  %229 = shufflevector <8 x i32> %217, <8 x i32> %221, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  %230 = shufflevector <8 x i32> %218, <8 x i32> %222, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  %231 = bitcast <8 x i32> %223 to <16 x i16>
  %232 = bitcast <8 x i32> %224 to <16 x i16>
  %_3.i1365 = add <16 x i16> %232, %231
  %233 = bitcast <8 x i32> %225 to <16 x i16>
  %_3.i1365.1 = add <16 x i16> %_3.i1365, %233
  %234 = bitcast <8 x i32> %226 to <16 x i16>
  %_3.i1365.2 = add <16 x i16> %_3.i1365.1, %234
  %235 = bitcast <8 x i32> %227 to <16 x i16>
  %_3.i1365.3 = add <16 x i16> %_3.i1365.2, %235
  %236 = bitcast <8 x i32> %228 to <16 x i16>
  %_3.i1365.4 = add <16 x i16> %_3.i1365.3, %236
  %237 = bitcast <8 x i32> %229 to <16 x i16>
  %_3.i1365.5 = add <16 x i16> %_3.i1365.4, %237
  %238 = bitcast <8 x i32> %230 to <16 x i16>
  %_3.i1365.6 = add <16 x i16> %_3.i1365.5, %238
  %_218.i.idx = shl nuw nsw i64 %iter4.sroa.0.0.i3624, 6
  %_218.i = getelementptr inbounds nuw i8, ptr %acc, i64 %_218.i.idx
  %dst.sroa.0.0.copyload.i13663428 = load <16 x i16>, ptr %_218.i, align 2, !noalias !120
  %_3.i1367 = add <16 x i16> %dst.sroa.0.0.copyload.i13663428, %_3.i1365.6
  store <16 x i16> %_3.i1367, ptr %_218.i, align 2, !noalias !123
  %239 = xor <8 x i32> %_3.i1314, %61
  %240 = xor <8 x i32> %_3.i1336, %62
  %241 = xor <8 x i32> %_3.i1270, %63
  %242 = xor <8 x i32> %_3.i1292, %64
  %243 = xor <8 x i32> %_34.i12913482, %65
  %244 = xor <8 x i32> %_34.i13133492, %66
  %245 = xor <8 x i32> %_34.i13353502, %67
  %246 = xor <8 x i32> %_34.i12693472, %68
  %r.i.1 = shufflevector <8 x i32> %239, <8 x i32> %240, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1343.1 = shufflevector <8 x i32> %239, <8 x i32> %240, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %r.i1344.1 = shufflevector <8 x i32> %241, <8 x i32> %242, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1345.1 = shufflevector <8 x i32> %241, <8 x i32> %242, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %r.i1346.1 = shufflevector <8 x i32> %243, <8 x i32> %244, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1347.1 = shufflevector <8 x i32> %243, <8 x i32> %244, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %r.i1348.1 = shufflevector <8 x i32> %245, <8 x i32> %246, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1349.1 = shufflevector <8 x i32> %245, <8 x i32> %246, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %247 = shufflevector <8 x i32> %r.i.1, <8 x i32> %r.i1344.1, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %248 = shufflevector <8 x i32> %r.i.1, <8 x i32> %r.i1344.1, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %249 = shufflevector <8 x i32> %r.i1343.1, <8 x i32> %r.i1345.1, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %250 = shufflevector <8 x i32> %r.i1343.1, <8 x i32> %r.i1345.1, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %251 = shufflevector <8 x i32> %r.i1346.1, <8 x i32> %r.i1348.1, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %252 = shufflevector <8 x i32> %r.i1346.1, <8 x i32> %r.i1348.1, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %253 = shufflevector <8 x i32> %r.i1347.1, <8 x i32> %r.i1349.1, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %254 = shufflevector <8 x i32> %r.i1347.1, <8 x i32> %r.i1349.1, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %255 = shufflevector <8 x i32> %247, <8 x i32> %251, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  %256 = shufflevector <8 x i32> %248, <8 x i32> %252, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  %257 = shufflevector <8 x i32> %249, <8 x i32> %253, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  %258 = shufflevector <8 x i32> %250, <8 x i32> %254, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  %259 = shufflevector <8 x i32> %247, <8 x i32> %251, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  %260 = shufflevector <8 x i32> %248, <8 x i32> %252, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  %261 = shufflevector <8 x i32> %249, <8 x i32> %253, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  %262 = shufflevector <8 x i32> %250, <8 x i32> %254, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  %263 = bitcast <8 x i32> %255 to <16 x i16>
  %264 = bitcast <8 x i32> %256 to <16 x i16>
  %_3.i1365.13641 = add <16 x i16> %264, %263
  %265 = bitcast <8 x i32> %257 to <16 x i16>
  %_3.i1365.1.1 = add <16 x i16> %_3.i1365.13641, %265
  %266 = bitcast <8 x i32> %258 to <16 x i16>
  %_3.i1365.2.1 = add <16 x i16> %_3.i1365.1.1, %266
  %267 = bitcast <8 x i32> %259 to <16 x i16>
  %_3.i1365.3.1 = add <16 x i16> %_3.i1365.2.1, %267
  %268 = bitcast <8 x i32> %260 to <16 x i16>
  %_3.i1365.4.1 = add <16 x i16> %_3.i1365.3.1, %268
  %269 = bitcast <8 x i32> %261 to <16 x i16>
  %_3.i1365.5.1 = add <16 x i16> %_3.i1365.4.1, %269
  %270 = bitcast <8 x i32> %262 to <16 x i16>
  %_3.i1365.6.1 = add <16 x i16> %_3.i1365.5.1, %270
  %_218.i.1 = getelementptr inbounds nuw i8, ptr %69, i64 %_218.i.idx
  %dst.sroa.0.0.copyload.i13663428.1 = load <16 x i16>, ptr %_218.i.1, align 2, !noalias !120
  %_3.i1367.1 = add <16 x i16> %dst.sroa.0.0.copyload.i13663428.1, %_3.i1365.6.1
  store <16 x i16> %_3.i1367.1, ptr %_218.i.1, align 2, !noalias !123
  %271 = add nuw nsw i64 %iter4.sroa.0.0.i3624, 1
  %exitcond3642.not = icmp eq i64 %271, 32
  br i1 %exitcond3642.not, label %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit, label %bb70.i

_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit: ; preds = %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit57.i
  call void @llvm.lifetime.end.p0(ptr nonnull %root_m.i), !noalias !58
  ret void
}

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
define void @agave_compress_pre_16(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([1024 x i8]) align 64 captures(none) dereferenceable(1024) %_0, ptr noalias nofree noundef readonly align 64 captures(none) dereferenceable(512) %cv, ptr noalias nofree noundef readonly align 64 captures(none) dereferenceable(512) %iv, ptr noalias nofree noundef readonly align 64 captures(none) dereferenceable(1024) %m, ptr dead_on_return noalias nofree noundef readonly align 64 captures(none) dereferenceable(64) %lo, ptr dead_on_return noalias nofree noundef readonly align 64 captures(none) dereferenceable(64) %hi, ptr dead_on_return noalias nofree noundef readonly align 64 captures(none) dereferenceable(64) %len, ptr dead_on_return noalias nofree noundef readonly align 64 captures(none) dereferenceable(64) %flags) unnamed_addr #4 {
start:
  %0 = load <16 x i32>, ptr %lo, align 64
  %1 = load <16 x i32>, ptr %hi, align 64
  %2 = load <16 x i32>, ptr %len, align 64
  %3 = load <16 x i32>, ptr %flags, align 64
  tail call void @llvm.experimental.noalias.scope.decl(metadata !130)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !133)
  %_9.i803 = load <16 x i32>, ptr %cv, align 64, !alias.scope !130, !noalias !135
  %4 = getelementptr inbounds nuw i8, ptr %cv, i64 64
  %_10.i808 = load <16 x i32>, ptr %4, align 64, !alias.scope !130, !noalias !135
  %5 = getelementptr inbounds nuw i8, ptr %cv, i64 128
  %_11.i813 = load <16 x i32>, ptr %5, align 64, !alias.scope !130, !noalias !135
  %6 = getelementptr inbounds nuw i8, ptr %cv, i64 192
  %_12.i818 = load <16 x i32>, ptr %6, align 64, !alias.scope !130, !noalias !135
  %7 = getelementptr inbounds nuw i8, ptr %cv, i64 256
  %_13.i804 = load <16 x i32>, ptr %7, align 64, !alias.scope !130, !noalias !135
  %8 = getelementptr inbounds nuw i8, ptr %cv, i64 320
  %_14.i809 = load <16 x i32>, ptr %8, align 64, !alias.scope !130, !noalias !135
  %9 = getelementptr inbounds nuw i8, ptr %cv, i64 384
  %_15.i814 = load <16 x i32>, ptr %9, align 64, !alias.scope !130, !noalias !135
  %10 = getelementptr inbounds nuw i8, ptr %cv, i64 448
  %_16.i819 = load <16 x i32>, ptr %10, align 64, !alias.scope !130, !noalias !135
  %_17.i805 = load <16 x i32>, ptr %iv, align 64, !alias.scope !133, !noalias !142
  %11 = getelementptr inbounds nuw i8, ptr %iv, i64 64
  %_18.i810 = load <16 x i32>, ptr %11, align 64, !alias.scope !133, !noalias !142
  %12 = getelementptr inbounds nuw i8, ptr %iv, i64 128
  %_19.i815 = load <16 x i32>, ptr %12, align 64, !alias.scope !133, !noalias !142
  %13 = getelementptr inbounds nuw i8, ptr %iv, i64 192
  %_20.i820 = load <16 x i32>, ptr %13, align 64, !alias.scope !133, !noalias !142
  br label %bb3.i

bb3.i:                                            ; preds = %start, %bb3.i
  %iter.sroa.0.0.i844 = phi i64 [ 0, %start ], [ %30, %bb3.i ]
  %14 = phi <16 x i32> [ %_9.i803, %start ], [ %_3.i70, %bb3.i ]
  %15 = phi <16 x i32> [ %_10.i808, %start ], [ %_3.i84, %bb3.i ]
  %16 = phi <16 x i32> [ %_11.i813, %start ], [ %_3.i98, %bb3.i ]
  %17 = phi <16 x i32> [ %_12.i818, %start ], [ %_3.i112, %bb3.i ]
  %18 = phi <16 x i32> [ %_13.i804, %start ], [ %_3.i.i117, %bb3.i ]
  %19 = phi <16 x i32> [ %_14.i809, %start ], [ %_3.i.i75, %bb3.i ]
  %20 = phi <16 x i32> [ %_15.i814, %start ], [ %_3.i.i89, %bb3.i ]
  %21 = phi <16 x i32> [ %_16.i819, %start ], [ %_3.i.i103, %bb3.i ]
  %22 = phi <16 x i32> [ %_17.i805, %start ], [ %_3.i101, %bb3.i ]
  %23 = phi <16 x i32> [ %_18.i810, %start ], [ %_3.i115, %bb3.i ]
  %24 = phi <16 x i32> [ %_19.i815, %start ], [ %_3.i73, %bb3.i ]
  %25 = phi <16 x i32> [ %_20.i820, %start ], [ %_3.i87, %bb3.i ]
  %26 = phi <16 x i32> [ %0, %start ], [ %_3.i.i86, %bb3.i ]
  %27 = phi <16 x i32> [ %1, %start ], [ %_3.i.i100, %bb3.i ]
  %28 = phi <16 x i32> [ %2, %start ], [ %_3.i.i114, %bb3.i ]
  %29 = phi <16 x i32> [ %3, %start ], [ %_3.i.i72, %bb3.i ]
  %30 = add nuw nsw i64 %iter.sroa.0.0.i844, 1
  tail call void @llvm.experimental.noalias.scope.decl(metadata !143)
  %s.i = getelementptr inbounds nuw [16 x i64], ptr @alloc_61fb4a9344bbdaf2573accd6331d7e32, i64 %iter.sroa.0.0.i844
  %31 = getelementptr inbounds nuw i8, ptr %s.i, i64 8
  %_11.i1 = load i64, ptr %31, align 8, !noalias !146, !noundef !41
  %_8.i = load i64, ptr %s.i, align 8, !noalias !146, !noundef !41
  %32 = getelementptr inbounds nuw <8 x i64>, ptr %m, i64 %_8.i
  %_7.i801 = load <16 x i32>, ptr %32, align 64, !alias.scope !143, !noalias !148
  %33 = getelementptr inbounds nuw <8 x i64>, ptr %m, i64 %_11.i1
  %_10.i2802 = load <16 x i32>, ptr %33, align 64, !alias.scope !143, !noalias !148
  %_3.i = add <16 x i32> %14, %18
  %_3.i8 = add <16 x i32> %_3.i, %_7.i801
  %_3.i9 = xor <16 x i32> %_3.i8, %26
  %_3.i.i = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i9, <16 x i32> %_3.i9, <16 x i32> splat (i32 16))
  %_3.i10 = add <16 x i32> %_3.i.i, %22
  %_3.i11 = xor <16 x i32> %_3.i10, %18
  %_3.i.i12 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i11, <16 x i32> %_3.i11, <16 x i32> splat (i32 20))
  %_3.i13 = add <16 x i32> %_10.i2802, %_3.i8
  %_3.i14 = add <16 x i32> %_3.i13, %_3.i.i12
  %_3.i15 = xor <16 x i32> %_3.i14, %_3.i.i
  %_3.i.i16 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i15, <16 x i32> %_3.i15, <16 x i32> splat (i32 24))
  %_3.i17 = add <16 x i32> %_3.i.i16, %_3.i10
  %_3.i18 = xor <16 x i32> %_3.i17, %_3.i.i12
  %_3.i.i19 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i18, <16 x i32> %_3.i18, <16 x i32> splat (i32 25))
  %34 = getelementptr inbounds nuw i8, ptr %s.i, i64 24
  %_18.i3 = load i64, ptr %34, align 8, !noalias !146, !noundef !41
  %35 = getelementptr inbounds nuw i8, ptr %s.i, i64 16
  %_15.i4 = load i64, ptr %35, align 8, !noalias !146, !noundef !41
  %36 = getelementptr inbounds nuw <8 x i64>, ptr %m, i64 %_15.i4
  %_14.i5806 = load <16 x i32>, ptr %36, align 64, !alias.scope !143, !noalias !148
  %37 = getelementptr inbounds nuw <8 x i64>, ptr %m, i64 %_18.i3
  %_17.i6807 = load <16 x i32>, ptr %37, align 64, !alias.scope !143, !noalias !148
  %_3.i20 = add <16 x i32> %15, %19
  %_3.i21 = add <16 x i32> %_3.i20, %_14.i5806
  %_3.i22 = xor <16 x i32> %_3.i21, %27
  %_3.i.i23 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i22, <16 x i32> %_3.i22, <16 x i32> splat (i32 16))
  %_3.i24 = add <16 x i32> %_3.i.i23, %23
  %_3.i25 = xor <16 x i32> %_3.i24, %19
  %_3.i.i26 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i25, <16 x i32> %_3.i25, <16 x i32> splat (i32 20))
  %_3.i27 = add <16 x i32> %_17.i6807, %_3.i21
  %_3.i28 = add <16 x i32> %_3.i27, %_3.i.i26
  %_3.i29 = xor <16 x i32> %_3.i28, %_3.i.i23
  %_3.i.i30 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i29, <16 x i32> %_3.i29, <16 x i32> splat (i32 24))
  %_3.i31 = add <16 x i32> %_3.i.i30, %_3.i24
  %_3.i32 = xor <16 x i32> %_3.i31, %_3.i.i26
  %_3.i.i33 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i32, <16 x i32> %_3.i32, <16 x i32> splat (i32 25))
  %38 = getelementptr inbounds nuw i8, ptr %s.i, i64 40
  %_25.i7 = load i64, ptr %38, align 8, !noalias !146, !noundef !41
  %39 = getelementptr inbounds nuw i8, ptr %s.i, i64 32
  %_22.i = load i64, ptr %39, align 8, !noalias !146, !noundef !41
  %40 = getelementptr inbounds nuw <8 x i64>, ptr %m, i64 %_22.i
  %_21.i811 = load <16 x i32>, ptr %40, align 64, !alias.scope !143, !noalias !148
  %41 = getelementptr inbounds nuw <8 x i64>, ptr %m, i64 %_25.i7
  %_24.i812 = load <16 x i32>, ptr %41, align 64, !alias.scope !143, !noalias !148
  %_3.i34 = add <16 x i32> %16, %20
  %_3.i35 = add <16 x i32> %_3.i34, %_21.i811
  %_3.i36 = xor <16 x i32> %_3.i35, %28
  %_3.i.i37 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i36, <16 x i32> %_3.i36, <16 x i32> splat (i32 16))
  %_3.i38 = add <16 x i32> %_3.i.i37, %24
  %_3.i39 = xor <16 x i32> %_3.i38, %20
  %_3.i.i40 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i39, <16 x i32> %_3.i39, <16 x i32> splat (i32 20))
  %_3.i41 = add <16 x i32> %_24.i812, %_3.i35
  %_3.i42 = add <16 x i32> %_3.i41, %_3.i.i40
  %_3.i43 = xor <16 x i32> %_3.i42, %_3.i.i37
  %_3.i.i44 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i43, <16 x i32> %_3.i43, <16 x i32> splat (i32 24))
  %_3.i45 = add <16 x i32> %_3.i.i44, %_3.i38
  %_3.i46 = xor <16 x i32> %_3.i45, %_3.i.i40
  %_3.i.i47 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i46, <16 x i32> %_3.i46, <16 x i32> splat (i32 25))
  %42 = getelementptr inbounds nuw i8, ptr %s.i, i64 56
  %_32.i = load i64, ptr %42, align 8, !noalias !146, !noundef !41
  %43 = getelementptr inbounds nuw i8, ptr %s.i, i64 48
  %_29.i = load i64, ptr %43, align 8, !noalias !146, !noundef !41
  %44 = getelementptr inbounds nuw <8 x i64>, ptr %m, i64 %_29.i
  %_28.i816 = load <16 x i32>, ptr %44, align 64, !alias.scope !143, !noalias !148
  %45 = getelementptr inbounds nuw <8 x i64>, ptr %m, i64 %_32.i
  %_31.i817 = load <16 x i32>, ptr %45, align 64, !alias.scope !143, !noalias !148
  %_3.i48 = add <16 x i32> %17, %21
  %_3.i49 = add <16 x i32> %_3.i48, %_28.i816
  %_3.i50 = xor <16 x i32> %_3.i49, %29
  %_3.i.i51 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i50, <16 x i32> %_3.i50, <16 x i32> splat (i32 16))
  %_3.i52 = add <16 x i32> %_3.i.i51, %25
  %_3.i53 = xor <16 x i32> %_3.i52, %21
  %_3.i.i54 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i53, <16 x i32> %_3.i53, <16 x i32> splat (i32 20))
  %_3.i55 = add <16 x i32> %_31.i817, %_3.i49
  %_3.i56 = add <16 x i32> %_3.i55, %_3.i.i54
  %_3.i57 = xor <16 x i32> %_3.i56, %_3.i.i51
  %_3.i.i58 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i57, <16 x i32> %_3.i57, <16 x i32> splat (i32 24))
  %_3.i59 = add <16 x i32> %_3.i.i58, %_3.i52
  %_3.i60 = xor <16 x i32> %_3.i59, %_3.i.i54
  %_3.i.i61 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i60, <16 x i32> %_3.i60, <16 x i32> splat (i32 25))
  %46 = getelementptr inbounds nuw i8, ptr %s.i, i64 72
  %_39.i = load i64, ptr %46, align 8, !noalias !146, !noundef !41
  %47 = getelementptr inbounds nuw i8, ptr %s.i, i64 64
  %_36.i = load i64, ptr %47, align 8, !noalias !146, !noundef !41
  %48 = getelementptr inbounds nuw <8 x i64>, ptr %m, i64 %_36.i
  %_35.i821 = load <16 x i32>, ptr %48, align 64, !alias.scope !143, !noalias !148
  %49 = getelementptr inbounds nuw <8 x i64>, ptr %m, i64 %_39.i
  %_38.i822 = load <16 x i32>, ptr %49, align 64, !alias.scope !143, !noalias !148
  %_3.i62 = add <16 x i32> %_35.i821, %_3.i14
  %_3.i63 = add <16 x i32> %_3.i62, %_3.i.i33
  %_3.i64 = xor <16 x i32> %_3.i.i58, %_3.i63
  %_3.i.i65 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i64, <16 x i32> %_3.i64, <16 x i32> splat (i32 16))
  %_3.i66 = add <16 x i32> %_3.i.i65, %_3.i45
  %_3.i67 = xor <16 x i32> %_3.i66, %_3.i.i33
  %_3.i.i68 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i67, <16 x i32> %_3.i67, <16 x i32> splat (i32 20))
  %_3.i69 = add <16 x i32> %_3.i63, %_38.i822
  %_3.i70 = add <16 x i32> %_3.i69, %_3.i.i68
  %_3.i71 = xor <16 x i32> %_3.i70, %_3.i.i65
  %_3.i.i72 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i71, <16 x i32> %_3.i71, <16 x i32> splat (i32 24))
  %_3.i73 = add <16 x i32> %_3.i.i72, %_3.i66
  %_3.i74 = xor <16 x i32> %_3.i73, %_3.i.i68
  %_3.i.i75 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i74, <16 x i32> %_3.i74, <16 x i32> splat (i32 25))
  %50 = getelementptr inbounds nuw i8, ptr %s.i, i64 88
  %_46.i = load i64, ptr %50, align 8, !noalias !146, !noundef !41
  %51 = getelementptr inbounds nuw i8, ptr %s.i, i64 80
  %_43.i = load i64, ptr %51, align 8, !noalias !146, !noundef !41
  %52 = getelementptr inbounds nuw <8 x i64>, ptr %m, i64 %_43.i
  %_42.i823 = load <16 x i32>, ptr %52, align 64, !alias.scope !143, !noalias !148
  %53 = getelementptr inbounds nuw <8 x i64>, ptr %m, i64 %_46.i
  %_45.i824 = load <16 x i32>, ptr %53, align 64, !alias.scope !143, !noalias !148
  %_3.i76 = add <16 x i32> %_42.i823, %_3.i28
  %_3.i77 = add <16 x i32> %_3.i76, %_3.i.i47
  %_3.i78 = xor <16 x i32> %_3.i77, %_3.i.i16
  %_3.i.i79 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i78, <16 x i32> %_3.i78, <16 x i32> splat (i32 16))
  %_3.i80 = add <16 x i32> %_3.i.i79, %_3.i59
  %_3.i81 = xor <16 x i32> %_3.i80, %_3.i.i47
  %_3.i.i82 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i81, <16 x i32> %_3.i81, <16 x i32> splat (i32 20))
  %_3.i83 = add <16 x i32> %_3.i77, %_45.i824
  %_3.i84 = add <16 x i32> %_3.i83, %_3.i.i82
  %_3.i85 = xor <16 x i32> %_3.i84, %_3.i.i79
  %_3.i.i86 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i85, <16 x i32> %_3.i85, <16 x i32> splat (i32 24))
  %_3.i87 = add <16 x i32> %_3.i.i86, %_3.i80
  %_3.i88 = xor <16 x i32> %_3.i87, %_3.i.i82
  %_3.i.i89 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i88, <16 x i32> %_3.i88, <16 x i32> splat (i32 25))
  %54 = getelementptr inbounds nuw i8, ptr %s.i, i64 104
  %_53.i = load i64, ptr %54, align 8, !noalias !146, !noundef !41
  %55 = getelementptr inbounds nuw i8, ptr %s.i, i64 96
  %_50.i = load i64, ptr %55, align 8, !noalias !146, !noundef !41
  %56 = getelementptr inbounds nuw <8 x i64>, ptr %m, i64 %_50.i
  %_49.i825 = load <16 x i32>, ptr %56, align 64, !alias.scope !143, !noalias !148
  %57 = getelementptr inbounds nuw <8 x i64>, ptr %m, i64 %_53.i
  %_52.i826 = load <16 x i32>, ptr %57, align 64, !alias.scope !143, !noalias !148
  %_3.i90 = add <16 x i32> %_49.i825, %_3.i42
  %_3.i91 = add <16 x i32> %_3.i90, %_3.i.i61
  %_3.i92 = xor <16 x i32> %_3.i91, %_3.i.i30
  %_3.i.i93 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i92, <16 x i32> %_3.i92, <16 x i32> splat (i32 16))
  %_3.i94 = add <16 x i32> %_3.i.i93, %_3.i17
  %_3.i95 = xor <16 x i32> %_3.i94, %_3.i.i61
  %_3.i.i96 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i95, <16 x i32> %_3.i95, <16 x i32> splat (i32 20))
  %_3.i97 = add <16 x i32> %_3.i91, %_52.i826
  %_3.i98 = add <16 x i32> %_3.i97, %_3.i.i96
  %_3.i99 = xor <16 x i32> %_3.i98, %_3.i.i93
  %_3.i.i100 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i99, <16 x i32> %_3.i99, <16 x i32> splat (i32 24))
  %_3.i101 = add <16 x i32> %_3.i.i100, %_3.i94
  %_3.i102 = xor <16 x i32> %_3.i101, %_3.i.i96
  %_3.i.i103 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i102, <16 x i32> %_3.i102, <16 x i32> splat (i32 25))
  %58 = getelementptr inbounds nuw i8, ptr %s.i, i64 120
  %_60.i = load i64, ptr %58, align 8, !noalias !146, !noundef !41
  %59 = getelementptr inbounds nuw i8, ptr %s.i, i64 112
  %_57.i = load i64, ptr %59, align 8, !noalias !146, !noundef !41
  %60 = getelementptr inbounds nuw <8 x i64>, ptr %m, i64 %_57.i
  %_56.i827 = load <16 x i32>, ptr %60, align 64, !alias.scope !143, !noalias !148
  %61 = getelementptr inbounds nuw <8 x i64>, ptr %m, i64 %_60.i
  %_59.i828 = load <16 x i32>, ptr %61, align 64, !alias.scope !143, !noalias !148
  %_3.i104 = add <16 x i32> %_3.i56, %_3.i.i19
  %_3.i105 = add <16 x i32> %_3.i104, %_56.i827
  %_3.i106 = xor <16 x i32> %_3.i105, %_3.i.i44
  %_3.i.i107 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i106, <16 x i32> %_3.i106, <16 x i32> splat (i32 16))
  %_3.i108 = add <16 x i32> %_3.i.i107, %_3.i31
  %_3.i109 = xor <16 x i32> %_3.i108, %_3.i.i19
  %_3.i.i110 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i109, <16 x i32> %_3.i109, <16 x i32> splat (i32 20))
  %_3.i111 = add <16 x i32> %_59.i828, %_3.i105
  %_3.i112 = add <16 x i32> %_3.i111, %_3.i.i110
  %_3.i113 = xor <16 x i32> %_3.i112, %_3.i.i107
  %_3.i.i114 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i113, <16 x i32> %_3.i113, <16 x i32> splat (i32 24))
  %_3.i115 = add <16 x i32> %_3.i.i114, %_3.i108
  %_3.i116 = xor <16 x i32> %_3.i115, %_3.i.i110
  %_3.i.i117 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i116, <16 x i32> %_3.i116, <16 x i32> splat (i32 25))
  %exitcond.not = icmp eq i64 %30, 7
  br i1 %exitcond.not, label %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit, label %bb3.i

_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_.exit: ; preds = %bb3.i
  store <16 x i32> %_3.i70, ptr %_0, align 64, !noalias !149
  %v.i.sroa.12.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 64
  store <16 x i32> %_3.i84, ptr %v.i.sroa.12.0._0.sroa_idx, align 64, !noalias !149
  %v.i.sroa.21.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 128
  store <16 x i32> %_3.i98, ptr %v.i.sroa.21.0._0.sroa_idx, align 64, !noalias !149
  %v.i.sroa.30.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 192
  store <16 x i32> %_3.i112, ptr %v.i.sroa.30.0._0.sroa_idx, align 64, !noalias !149
  %v.i.sroa.39.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 256
  store <16 x i32> %_3.i.i117, ptr %v.i.sroa.39.0._0.sroa_idx, align 64, !noalias !149
  %v.i.sroa.50.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 320
  store <16 x i32> %_3.i.i75, ptr %v.i.sroa.50.0._0.sroa_idx, align 64, !noalias !149
  %v.i.sroa.61.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 384
  store <16 x i32> %_3.i.i89, ptr %v.i.sroa.61.0._0.sroa_idx, align 64, !noalias !149
  %v.i.sroa.72.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 448
  store <16 x i32> %_3.i.i103, ptr %v.i.sroa.72.0._0.sroa_idx, align 64, !noalias !149
  %v.i.sroa.83.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 512
  store <16 x i32> %_3.i101, ptr %v.i.sroa.83.0._0.sroa_idx, align 64, !noalias !149
  %v.i.sroa.92.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 576
  store <16 x i32> %_3.i115, ptr %v.i.sroa.92.0._0.sroa_idx, align 64, !noalias !149
  %v.i.sroa.101.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 640
  store <16 x i32> %_3.i73, ptr %v.i.sroa.101.0._0.sroa_idx, align 64, !noalias !149
  %v.i.sroa.110.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 704
  store <16 x i32> %_3.i87, ptr %v.i.sroa.110.0._0.sroa_idx, align 64, !noalias !149
  %v.i.sroa.119.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 768
  store <16 x i32> %_3.i.i86, ptr %v.i.sroa.119.0._0.sroa_idx, align 64, !noalias !149
  %v.i.sroa.128.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 832
  store <16 x i32> %_3.i.i100, ptr %v.i.sroa.128.0._0.sroa_idx, align 64, !noalias !149
  %v.i.sroa.137.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 896
  store <16 x i32> %_3.i.i114, ptr %v.i.sroa.137.0._0.sroa_idx, align 64, !noalias !149
  %v.i.sroa.146.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 960
  store <16 x i32> %_3.i.i72, ptr %v.i.sroa.146.0._0.sroa_idx, align 64, !noalias !149
  ret void
}

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
define void @agave_compress_pre_8(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([512 x i8]) align 32 captures(none) dereferenceable(512) %_0, ptr noalias nofree noundef readonly align 32 captures(none) dereferenceable(256) %cv, ptr noalias nofree noundef readonly align 32 captures(none) dereferenceable(256) %iv, ptr noalias nofree noundef readonly align 32 captures(none) dereferenceable(512) %m, ptr dead_on_return noalias nofree noundef readonly align 32 captures(none) dereferenceable(32) %lo, ptr dead_on_return noalias nofree noundef readonly align 32 captures(none) dereferenceable(32) %hi, ptr dead_on_return noalias nofree noundef readonly align 32 captures(none) dereferenceable(32) %len, ptr dead_on_return noalias nofree noundef readonly align 32 captures(none) dereferenceable(32) %flags) unnamed_addr #5 {
start:
  %0 = load <8 x i32>, ptr %lo, align 32
  %1 = load <8 x i32>, ptr %hi, align 32
  %2 = load <8 x i32>, ptr %len, align 32
  %3 = load <8 x i32>, ptr %flags, align 32
  tail call void @llvm.experimental.noalias.scope.decl(metadata !150)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !153)
  %_9.i1406 = load <8 x i32>, ptr %cv, align 32, !alias.scope !150, !noalias !155
  %4 = getelementptr inbounds nuw i8, ptr %cv, i64 32
  %_10.i1416 = load <8 x i32>, ptr %4, align 32, !alias.scope !150, !noalias !155
  %5 = getelementptr inbounds nuw i8, ptr %cv, i64 64
  %_11.i1426 = load <8 x i32>, ptr %5, align 32, !alias.scope !150, !noalias !155
  %6 = getelementptr inbounds nuw i8, ptr %cv, i64 96
  %_12.i1436 = load <8 x i32>, ptr %6, align 32, !alias.scope !150, !noalias !155
  %7 = getelementptr inbounds nuw i8, ptr %cv, i64 128
  %_13.i1500 = load <8 x i32>, ptr %7, align 32, !alias.scope !150, !noalias !155
  %8 = getelementptr inbounds nuw i8, ptr %cv, i64 160
  %_14.i1501 = load <8 x i32>, ptr %8, align 32, !alias.scope !150, !noalias !155
  %9 = getelementptr inbounds nuw i8, ptr %cv, i64 192
  %_15.i1502 = load <8 x i32>, ptr %9, align 32, !alias.scope !150, !noalias !155
  %10 = getelementptr inbounds nuw i8, ptr %cv, i64 224
  %_16.i1503 = load <8 x i32>, ptr %10, align 32, !alias.scope !150, !noalias !155
  %_17.i1408 = load <8 x i32>, ptr %iv, align 32, !alias.scope !153, !noalias !162
  %11 = getelementptr inbounds nuw i8, ptr %iv, i64 32
  %_18.i1418 = load <8 x i32>, ptr %11, align 32, !alias.scope !153, !noalias !162
  %12 = getelementptr inbounds nuw i8, ptr %iv, i64 64
  %_19.i1428 = load <8 x i32>, ptr %12, align 32, !alias.scope !153, !noalias !162
  %13 = getelementptr inbounds nuw i8, ptr %iv, i64 96
  %_20.i1438 = load <8 x i32>, ptr %13, align 32, !alias.scope !153, !noalias !162
  br label %bb3.i

bb3.i:                                            ; preds = %start, %bb3.i
  %iter.sroa.0.0.i1499 = phi i64 [ 0, %start ], [ %30, %bb3.i ]
  %14 = phi <8 x i32> [ %_9.i1406, %start ], [ %_3.i453, %bb3.i ]
  %15 = phi <8 x i32> [ %_10.i1416, %start ], [ %_3.i475, %bb3.i ]
  %16 = phi <8 x i32> [ %_11.i1426, %start ], [ %_3.i497, %bb3.i ]
  %17 = phi <8 x i32> [ %_12.i1436, %start ], [ %_3.i519, %bb3.i ]
  %18 = phi <8 x i32> [ %_13.i1500, %start ], [ %_34.i5281483, %bb3.i ]
  %19 = phi <8 x i32> [ %_14.i1501, %start ], [ %_34.i4621453, %bb3.i ]
  %20 = phi <8 x i32> [ %_15.i1502, %start ], [ %_34.i4841463, %bb3.i ]
  %21 = phi <8 x i32> [ %_16.i1503, %start ], [ %_34.i5061473, %bb3.i ]
  %22 = phi <8 x i32> [ %_17.i1408, %start ], [ %_3.i502, %bb3.i ]
  %23 = phi <8 x i32> [ %_18.i1418, %start ], [ %_3.i524, %bb3.i ]
  %24 = phi <8 x i32> [ %_19.i1428, %start ], [ %_3.i458, %bb3.i ]
  %25 = phi <8 x i32> [ %_20.i1438, %start ], [ %_3.i480, %bb3.i ]
  %26 = phi <8 x i32> [ %0, %start ], [ %_34.i4791461, %bb3.i ]
  %27 = phi <8 x i32> [ %1, %start ], [ %_34.i5011471, %bb3.i ]
  %28 = phi <8 x i32> [ %2, %start ], [ %_34.i5231481, %bb3.i ]
  %29 = phi <8 x i32> [ %3, %start ], [ %_34.i4571451, %bb3.i ]
  %30 = add nuw nsw i64 %iter.sroa.0.0.i1499, 1
  tail call void @llvm.experimental.noalias.scope.decl(metadata !163)
  %s.i = getelementptr inbounds nuw [16 x i64], ptr @alloc_61fb4a9344bbdaf2573accd6331d7e32, i64 %iter.sroa.0.0.i1499
  %31 = getelementptr inbounds nuw i8, ptr %s.i, i64 8
  %_11.i1 = load i64, ptr %31, align 8, !noalias !166, !noundef !41
  %_8.i = load i64, ptr %s.i, align 8, !noalias !166, !noundef !41
  %32 = getelementptr inbounds nuw <4 x i64>, ptr %m, i64 %_8.i
  %_7.i1404 = load <8 x i32>, ptr %32, align 32, !alias.scope !163, !noalias !168
  %33 = getelementptr inbounds nuw <4 x i64>, ptr %m, i64 %_11.i1
  %_10.i21405 = load <8 x i32>, ptr %33, align 32, !alias.scope !163, !noalias !168
  %_3.i354 = add <8 x i32> %14, %18
  %_3.i355 = add <8 x i32> %_3.i354, %_7.i1404
  %34 = xor <8 x i32> %_3.i355, %26
  %_34.i1407 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %34, <8 x i32> %34, <8 x i32> splat (i32 16))
  %_3.i359 = add <8 x i32> %_34.i1407, %22
  %35 = xor <8 x i32> %_3.i359, %18
  %_34.i3631409 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %35, <8 x i32> %35, <8 x i32> splat (i32 20))
  %_3.i364 = add <8 x i32> %_10.i21405, %_3.i355
  %_3.i365 = add <8 x i32> %_3.i364, %_34.i3631409
  %_3.i3661410 = xor <8 x i32> %_3.i365, %_34.i1407
  %_34.i3691411 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i3661410, <8 x i32> %_3.i3661410, <8 x i32> splat (i32 24))
  %_3.i370 = add <8 x i32> %_34.i3691411, %_3.i359
  %_3.i3711412 = xor <8 x i32> %_3.i370, %_34.i3631409
  %_34.i3741413 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i3711412, <8 x i32> %_3.i3711412, <8 x i32> splat (i32 25))
  %36 = getelementptr inbounds nuw i8, ptr %s.i, i64 24
  %_18.i3 = load i64, ptr %36, align 8, !noalias !166, !noundef !41
  %37 = getelementptr inbounds nuw i8, ptr %s.i, i64 16
  %_15.i4 = load i64, ptr %37, align 8, !noalias !166, !noundef !41
  %38 = getelementptr inbounds nuw <4 x i64>, ptr %m, i64 %_15.i4
  %_14.i51414 = load <8 x i32>, ptr %38, align 32, !alias.scope !163, !noalias !168
  %39 = getelementptr inbounds nuw <4 x i64>, ptr %m, i64 %_18.i3
  %_17.i61415 = load <8 x i32>, ptr %39, align 32, !alias.scope !163, !noalias !168
  %_3.i375 = add <8 x i32> %15, %19
  %_3.i376 = add <8 x i32> %_3.i375, %_14.i51414
  %40 = xor <8 x i32> %_3.i376, %27
  %_34.i3801417 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %40, <8 x i32> %40, <8 x i32> splat (i32 16))
  %_3.i381 = add <8 x i32> %_34.i3801417, %23
  %41 = xor <8 x i32> %_3.i381, %19
  %_34.i3851419 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %41, <8 x i32> %41, <8 x i32> splat (i32 20))
  %_3.i386 = add <8 x i32> %_17.i61415, %_3.i376
  %_3.i387 = add <8 x i32> %_3.i386, %_34.i3851419
  %_3.i3881420 = xor <8 x i32> %_3.i387, %_34.i3801417
  %_34.i3911421 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i3881420, <8 x i32> %_3.i3881420, <8 x i32> splat (i32 24))
  %_3.i392 = add <8 x i32> %_34.i3911421, %_3.i381
  %_3.i3931422 = xor <8 x i32> %_3.i392, %_34.i3851419
  %_34.i3961423 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i3931422, <8 x i32> %_3.i3931422, <8 x i32> splat (i32 25))
  %42 = getelementptr inbounds nuw i8, ptr %s.i, i64 40
  %_25.i7 = load i64, ptr %42, align 8, !noalias !166, !noundef !41
  %43 = getelementptr inbounds nuw i8, ptr %s.i, i64 32
  %_22.i = load i64, ptr %43, align 8, !noalias !166, !noundef !41
  %44 = getelementptr inbounds nuw <4 x i64>, ptr %m, i64 %_22.i
  %_21.i1424 = load <8 x i32>, ptr %44, align 32, !alias.scope !163, !noalias !168
  %45 = getelementptr inbounds nuw <4 x i64>, ptr %m, i64 %_25.i7
  %_24.i1425 = load <8 x i32>, ptr %45, align 32, !alias.scope !163, !noalias !168
  %_3.i397 = add <8 x i32> %16, %20
  %_3.i398 = add <8 x i32> %_3.i397, %_21.i1424
  %46 = xor <8 x i32> %_3.i398, %28
  %_34.i4021427 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %46, <8 x i32> %46, <8 x i32> splat (i32 16))
  %_3.i403 = add <8 x i32> %_34.i4021427, %24
  %47 = xor <8 x i32> %_3.i403, %20
  %_34.i4071429 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %47, <8 x i32> %47, <8 x i32> splat (i32 20))
  %_3.i408 = add <8 x i32> %_24.i1425, %_3.i398
  %_3.i409 = add <8 x i32> %_3.i408, %_34.i4071429
  %_3.i4101430 = xor <8 x i32> %_3.i409, %_34.i4021427
  %_34.i4131431 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i4101430, <8 x i32> %_3.i4101430, <8 x i32> splat (i32 24))
  %_3.i414 = add <8 x i32> %_34.i4131431, %_3.i403
  %_3.i4151432 = xor <8 x i32> %_3.i414, %_34.i4071429
  %_34.i4181433 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i4151432, <8 x i32> %_3.i4151432, <8 x i32> splat (i32 25))
  %48 = getelementptr inbounds nuw i8, ptr %s.i, i64 56
  %_32.i = load i64, ptr %48, align 8, !noalias !166, !noundef !41
  %49 = getelementptr inbounds nuw i8, ptr %s.i, i64 48
  %_29.i = load i64, ptr %49, align 8, !noalias !166, !noundef !41
  %50 = getelementptr inbounds nuw <4 x i64>, ptr %m, i64 %_29.i
  %_28.i1434 = load <8 x i32>, ptr %50, align 32, !alias.scope !163, !noalias !168
  %51 = getelementptr inbounds nuw <4 x i64>, ptr %m, i64 %_32.i
  %_31.i1435 = load <8 x i32>, ptr %51, align 32, !alias.scope !163, !noalias !168
  %_3.i419 = add <8 x i32> %17, %21
  %_3.i420 = add <8 x i32> %_3.i419, %_28.i1434
  %52 = xor <8 x i32> %_3.i420, %29
  %_34.i4241437 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %52, <8 x i32> %52, <8 x i32> splat (i32 16))
  %_3.i425 = add <8 x i32> %_34.i4241437, %25
  %53 = xor <8 x i32> %_3.i425, %21
  %_34.i4291439 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %53, <8 x i32> %53, <8 x i32> splat (i32 20))
  %_3.i430 = add <8 x i32> %_31.i1435, %_3.i420
  %_3.i431 = add <8 x i32> %_3.i430, %_34.i4291439
  %_3.i4321440 = xor <8 x i32> %_3.i431, %_34.i4241437
  %_34.i4351441 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i4321440, <8 x i32> %_3.i4321440, <8 x i32> splat (i32 24))
  %_3.i436 = add <8 x i32> %_34.i4351441, %_3.i425
  %_3.i4371442 = xor <8 x i32> %_3.i436, %_34.i4291439
  %_34.i4401443 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i4371442, <8 x i32> %_3.i4371442, <8 x i32> splat (i32 25))
  %54 = getelementptr inbounds nuw i8, ptr %s.i, i64 72
  %_39.i = load i64, ptr %54, align 8, !noalias !166, !noundef !41
  %55 = getelementptr inbounds nuw i8, ptr %s.i, i64 64
  %_36.i = load i64, ptr %55, align 8, !noalias !166, !noundef !41
  %56 = getelementptr inbounds nuw <4 x i64>, ptr %m, i64 %_36.i
  %_35.i1444 = load <8 x i32>, ptr %56, align 32, !alias.scope !163, !noalias !168
  %57 = getelementptr inbounds nuw <4 x i64>, ptr %m, i64 %_39.i
  %_38.i1445 = load <8 x i32>, ptr %57, align 32, !alias.scope !163, !noalias !168
  %_3.i441 = add <8 x i32> %_35.i1444, %_3.i365
  %_3.i442 = add <8 x i32> %_3.i441, %_34.i3961423
  %_3.i4431446 = xor <8 x i32> %_34.i4351441, %_3.i442
  %_34.i4461447 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i4431446, <8 x i32> %_3.i4431446, <8 x i32> splat (i32 16))
  %_3.i447 = add <8 x i32> %_34.i4461447, %_3.i414
  %_3.i4481448 = xor <8 x i32> %_3.i447, %_34.i3961423
  %_34.i4511449 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i4481448, <8 x i32> %_3.i4481448, <8 x i32> splat (i32 20))
  %_3.i452 = add <8 x i32> %_3.i442, %_38.i1445
  %_3.i453 = add <8 x i32> %_3.i452, %_34.i4511449
  %_3.i4541450 = xor <8 x i32> %_3.i453, %_34.i4461447
  %_34.i4571451 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i4541450, <8 x i32> %_3.i4541450, <8 x i32> splat (i32 24))
  %_3.i458 = add <8 x i32> %_34.i4571451, %_3.i447
  %_3.i4591452 = xor <8 x i32> %_3.i458, %_34.i4511449
  %_34.i4621453 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i4591452, <8 x i32> %_3.i4591452, <8 x i32> splat (i32 25))
  %58 = getelementptr inbounds nuw i8, ptr %s.i, i64 88
  %_46.i = load i64, ptr %58, align 8, !noalias !166, !noundef !41
  %59 = getelementptr inbounds nuw i8, ptr %s.i, i64 80
  %_43.i = load i64, ptr %59, align 8, !noalias !166, !noundef !41
  %60 = getelementptr inbounds nuw <4 x i64>, ptr %m, i64 %_43.i
  %_42.i1454 = load <8 x i32>, ptr %60, align 32, !alias.scope !163, !noalias !168
  %61 = getelementptr inbounds nuw <4 x i64>, ptr %m, i64 %_46.i
  %_45.i1455 = load <8 x i32>, ptr %61, align 32, !alias.scope !163, !noalias !168
  %_3.i463 = add <8 x i32> %_42.i1454, %_3.i387
  %_3.i464 = add <8 x i32> %_3.i463, %_34.i4181433
  %_3.i4651456 = xor <8 x i32> %_3.i464, %_34.i3691411
  %_34.i4681457 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i4651456, <8 x i32> %_3.i4651456, <8 x i32> splat (i32 16))
  %_3.i469 = add <8 x i32> %_34.i4681457, %_3.i436
  %_3.i4701458 = xor <8 x i32> %_3.i469, %_34.i4181433
  %_34.i4731459 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i4701458, <8 x i32> %_3.i4701458, <8 x i32> splat (i32 20))
  %_3.i474 = add <8 x i32> %_3.i464, %_45.i1455
  %_3.i475 = add <8 x i32> %_3.i474, %_34.i4731459
  %_3.i4761460 = xor <8 x i32> %_3.i475, %_34.i4681457
  %_34.i4791461 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i4761460, <8 x i32> %_3.i4761460, <8 x i32> splat (i32 24))
  %_3.i480 = add <8 x i32> %_34.i4791461, %_3.i469
  %_3.i4811462 = xor <8 x i32> %_3.i480, %_34.i4731459
  %_34.i4841463 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i4811462, <8 x i32> %_3.i4811462, <8 x i32> splat (i32 25))
  %62 = getelementptr inbounds nuw i8, ptr %s.i, i64 104
  %_53.i = load i64, ptr %62, align 8, !noalias !166, !noundef !41
  %63 = getelementptr inbounds nuw i8, ptr %s.i, i64 96
  %_50.i = load i64, ptr %63, align 8, !noalias !166, !noundef !41
  %64 = getelementptr inbounds nuw <4 x i64>, ptr %m, i64 %_50.i
  %_49.i1464 = load <8 x i32>, ptr %64, align 32, !alias.scope !163, !noalias !168
  %65 = getelementptr inbounds nuw <4 x i64>, ptr %m, i64 %_53.i
  %_52.i1465 = load <8 x i32>, ptr %65, align 32, !alias.scope !163, !noalias !168
  %_3.i485 = add <8 x i32> %_49.i1464, %_3.i409
  %_3.i486 = add <8 x i32> %_3.i485, %_34.i4401443
  %_3.i4871466 = xor <8 x i32> %_3.i486, %_34.i3911421
  %_34.i4901467 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i4871466, <8 x i32> %_3.i4871466, <8 x i32> splat (i32 16))
  %_3.i491 = add <8 x i32> %_34.i4901467, %_3.i370
  %_3.i4921468 = xor <8 x i32> %_3.i491, %_34.i4401443
  %_34.i4951469 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i4921468, <8 x i32> %_3.i4921468, <8 x i32> splat (i32 20))
  %_3.i496 = add <8 x i32> %_3.i486, %_52.i1465
  %_3.i497 = add <8 x i32> %_3.i496, %_34.i4951469
  %_3.i4981470 = xor <8 x i32> %_3.i497, %_34.i4901467
  %_34.i5011471 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i4981470, <8 x i32> %_3.i4981470, <8 x i32> splat (i32 24))
  %_3.i502 = add <8 x i32> %_34.i5011471, %_3.i491
  %_3.i5031472 = xor <8 x i32> %_3.i502, %_34.i4951469
  %_34.i5061473 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i5031472, <8 x i32> %_3.i5031472, <8 x i32> splat (i32 25))
  %66 = getelementptr inbounds nuw i8, ptr %s.i, i64 120
  %_60.i = load i64, ptr %66, align 8, !noalias !166, !noundef !41
  %67 = getelementptr inbounds nuw i8, ptr %s.i, i64 112
  %_57.i = load i64, ptr %67, align 8, !noalias !166, !noundef !41
  %68 = getelementptr inbounds nuw <4 x i64>, ptr %m, i64 %_57.i
  %_56.i1474 = load <8 x i32>, ptr %68, align 32, !alias.scope !163, !noalias !168
  %69 = getelementptr inbounds nuw <4 x i64>, ptr %m, i64 %_60.i
  %_59.i1475 = load <8 x i32>, ptr %69, align 32, !alias.scope !163, !noalias !168
  %_3.i507 = add <8 x i32> %_3.i431, %_34.i3741413
  %_3.i508 = add <8 x i32> %_3.i507, %_56.i1474
  %_3.i5091476 = xor <8 x i32> %_3.i508, %_34.i4131431
  %_34.i5121477 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i5091476, <8 x i32> %_3.i5091476, <8 x i32> splat (i32 16))
  %_3.i513 = add <8 x i32> %_34.i5121477, %_3.i392
  %_3.i5141478 = xor <8 x i32> %_3.i513, %_34.i3741413
  %_34.i5171479 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i5141478, <8 x i32> %_3.i5141478, <8 x i32> splat (i32 20))
  %_3.i518 = add <8 x i32> %_59.i1475, %_3.i508
  %_3.i519 = add <8 x i32> %_3.i518, %_34.i5171479
  %_3.i5201480 = xor <8 x i32> %_3.i519, %_34.i5121477
  %_34.i5231481 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i5201480, <8 x i32> %_3.i5201480, <8 x i32> splat (i32 24))
  %_3.i524 = add <8 x i32> %_34.i5231481, %_3.i513
  %_3.i5251482 = xor <8 x i32> %_3.i524, %_34.i5171479
  %_34.i5281483 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i5251482, <8 x i32> %_3.i5251482, <8 x i32> splat (i32 25))
  %exitcond.not = icmp eq i64 %30, 7
  br i1 %exitcond.not, label %_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit, label %bb3.i

_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_.exit: ; preds = %bb3.i
  store <8 x i32> %_3.i453, ptr %_0, align 32, !noalias !169
  %v.i.sroa.12.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 32
  store <8 x i32> %_3.i475, ptr %v.i.sroa.12.0._0.sroa_idx, align 32, !noalias !169
  %v.i.sroa.21.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 64
  store <8 x i32> %_3.i497, ptr %v.i.sroa.21.0._0.sroa_idx, align 32, !noalias !169
  %v.i.sroa.30.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 96
  store <8 x i32> %_3.i519, ptr %v.i.sroa.30.0._0.sroa_idx, align 32, !noalias !169
  %v.i.sroa.39.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 128
  store <8 x i32> %_34.i5281483, ptr %v.i.sroa.39.0._0.sroa_idx, align 32, !noalias !169
  %v.i.sroa.50.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 160
  store <8 x i32> %_34.i4621453, ptr %v.i.sroa.50.0._0.sroa_idx, align 32, !noalias !169
  %v.i.sroa.61.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 192
  store <8 x i32> %_34.i4841463, ptr %v.i.sroa.61.0._0.sroa_idx, align 32, !noalias !169
  %v.i.sroa.72.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 224
  store <8 x i32> %_34.i5061473, ptr %v.i.sroa.72.0._0.sroa_idx, align 32, !noalias !169
  %v.i.sroa.83.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 256
  store <8 x i32> %_3.i502, ptr %v.i.sroa.83.0._0.sroa_idx, align 32, !noalias !169
  %v.i.sroa.92.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 288
  store <8 x i32> %_3.i524, ptr %v.i.sroa.92.0._0.sroa_idx, align 32, !noalias !169
  %v.i.sroa.101.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 320
  store <8 x i32> %_3.i458, ptr %v.i.sroa.101.0._0.sroa_idx, align 32, !noalias !169
  %v.i.sroa.110.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 352
  store <8 x i32> %_3.i480, ptr %v.i.sroa.110.0._0.sroa_idx, align 32, !noalias !169
  %v.i.sroa.119.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 384
  store <8 x i32> %_34.i4791461, ptr %v.i.sroa.119.0._0.sroa_idx, align 32, !noalias !169
  %v.i.sroa.128.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 416
  store <8 x i32> %_34.i5011471, ptr %v.i.sroa.128.0._0.sroa_idx, align 32, !noalias !169
  %v.i.sroa.137.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 448
  store <8 x i32> %_34.i5231481, ptr %v.i.sroa.137.0._0.sroa_idx, align 32, !noalias !169
  %v.i.sroa.146.0._0.sroa_idx = getelementptr inbounds nuw i8, ptr %_0, i64 480
  store <8 x i32> %_34.i4571451, ptr %v.i.sroa.146.0._0.sroa_idx, align 32, !noalias !169
  ret void
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
define void @agave_g_16(ptr noalias nofree noundef align 64 captures(none) dereferenceable(1024) %v, ptr dead_on_return noalias nofree noundef readonly align 64 captures(none) dereferenceable(64) %mx, ptr dead_on_return noalias nofree noundef readonly align 64 captures(none) dereferenceable(64) %my) unnamed_addr #0 {
start:
  %0 = load <16 x i32>, ptr %mx, align 64
  %1 = load <16 x i32>, ptr %my, align 64
  %_10.i90 = load <16 x i32>, ptr %v, align 64, !alias.scope !170, !noalias !173
  %2 = getelementptr inbounds nuw i8, ptr %v, i64 256
  %_12.i91 = load <16 x i32>, ptr %2, align 64, !alias.scope !170, !noalias !173
  %_3.i = add <16 x i32> %_10.i90, %0
  %_3.i1 = add <16 x i32> %_3.i, %_12.i91
  %3 = getelementptr inbounds nuw i8, ptr %v, i64 768
  %_16.i92 = load <16 x i32>, ptr %3, align 64, !alias.scope !170, !noalias !173
  %_3.i2 = xor <16 x i32> %_3.i1, %_16.i92
  %_3.i.i = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i2, <16 x i32> %_3.i2, <16 x i32> splat (i32 16))
  %4 = getelementptr inbounds nuw i8, ptr %v, i64 512
  %_20.i93 = load <16 x i32>, ptr %4, align 64, !alias.scope !170, !noalias !173
  %_3.i3 = add <16 x i32> %_3.i.i, %_20.i93
  %_3.i4 = xor <16 x i32> %_3.i3, %_12.i91
  %_3.i.i5 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i4, <16 x i32> %_3.i4, <16 x i32> splat (i32 20))
  %_3.i6 = add <16 x i32> %_3.i1, %1
  %_3.i7 = add <16 x i32> %_3.i6, %_3.i.i5
  store <16 x i32> %_3.i7, ptr %v, align 64, !alias.scope !170, !noalias !173
  %_3.i8 = xor <16 x i32> %_3.i7, %_3.i.i
  %_3.i.i9 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i8, <16 x i32> %_3.i8, <16 x i32> splat (i32 24))
  store <16 x i32> %_3.i.i9, ptr %3, align 64, !alias.scope !170, !noalias !173
  %_3.i10 = add <16 x i32> %_3.i.i9, %_3.i3
  store <16 x i32> %_3.i10, ptr %4, align 64, !alias.scope !170, !noalias !173
  %_3.i11 = xor <16 x i32> %_3.i10, %_3.i.i5
  %_3.i.i12 = tail call <16 x i32> @llvm.fshl.v16i32(<16 x i32> %_3.i11, <16 x i32> %_3.i11, <16 x i32> splat (i32 25))
  store <16 x i32> %_3.i.i12, ptr %2, align 64, !alias.scope !170, !noalias !173
  ret void
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
define void @agave_g_8(ptr noalias nofree noundef align 32 captures(none) dereferenceable(512) %v, ptr dead_on_return noalias nofree noundef readonly align 32 captures(none) dereferenceable(32) %mx, ptr dead_on_return noalias nofree noundef readonly align 32 captures(none) dereferenceable(32) %my) unnamed_addr #1 {
start:
  %0 = load <8 x i32>, ptr %mx, align 32
  %1 = load <8 x i32>, ptr %my, align 32
  %_10.i160 = load <8 x i32>, ptr %v, align 32, !alias.scope !176, !noalias !179
  %2 = getelementptr inbounds nuw i8, ptr %v, i64 128
  %_12.i169 = load <8 x i32>, ptr %2, align 32, !alias.scope !176, !noalias !179
  %_3.i38 = add <8 x i32> %_10.i160, %0
  %_3.i39 = add <8 x i32> %_3.i38, %_12.i169
  %3 = getelementptr inbounds nuw i8, ptr %v, i64 384
  %_16.i161 = load <8 x i32>, ptr %3, align 32, !alias.scope !176, !noalias !179
  %4 = xor <8 x i32> %_3.i39, %_16.i161
  %_34.i162 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %4, <8 x i32> %4, <8 x i32> splat (i32 16))
  %5 = getelementptr inbounds nuw i8, ptr %v, i64 256
  %_20.i163 = load <8 x i32>, ptr %5, align 32, !alias.scope !176, !noalias !179
  %_3.i43 = add <8 x i32> %_34.i162, %_20.i163
  %6 = xor <8 x i32> %_3.i43, %_12.i169
  %_34.i47164 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %6, <8 x i32> %6, <8 x i32> splat (i32 20))
  %_3.i48 = add <8 x i32> %_3.i39, %1
  %_3.i49 = add <8 x i32> %_3.i48, %_34.i47164
  store <8 x i32> %_3.i49, ptr %v, align 32, !alias.scope !176, !noalias !179
  %_3.i50165 = xor <8 x i32> %_3.i49, %_34.i162
  %_34.i53166 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i50165, <8 x i32> %_3.i50165, <8 x i32> splat (i32 24))
  store <8 x i32> %_34.i53166, ptr %3, align 32, !alias.scope !176, !noalias !179
  %_3.i54 = add <8 x i32> %_34.i53166, %_3.i43
  store <8 x i32> %_3.i54, ptr %5, align 32, !alias.scope !176, !noalias !179
  %_3.i55167 = xor <8 x i32> %_3.i54, %_34.i47164
  %_34.i58168 = tail call <8 x i32> @llvm.fshl.v8i32(<8 x i32> %_3.i55167, <8 x i32> %_3.i55167, <8 x i32> splat (i32 25))
  store <8 x i32> %_34.i58168, ptr %2, align 32, !alias.scope !176, !noalias !179
  ret void
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
define void @agave_transpose_16(ptr noalias nofree noundef align 64 captures(none) dereferenceable(1024) %v) unnamed_addr #0 {
start:
  %_4.i319 = load <16 x i32>, ptr %v, align 64, !alias.scope !182
  %0 = getelementptr inbounds nuw i8, ptr %v, i64 256
  %_5.i320 = load <16 x i32>, ptr %0, align 64, !alias.scope !182
  %r.i = shufflevector <16 x i32> %_4.i319, <16 x i32> %_5.i320, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %1 = getelementptr inbounds nuw i8, ptr %v, i64 64
  %_7.i321 = load <16 x i32>, ptr %1, align 64, !alias.scope !182
  %2 = getelementptr inbounds nuw i8, ptr %v, i64 320
  %_8.i322 = load <16 x i32>, ptr %2, align 64, !alias.scope !182
  %r.i1 = shufflevector <16 x i32> %_7.i321, <16 x i32> %_8.i322, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %3 = getelementptr inbounds nuw i8, ptr %v, i64 128
  %_10.i323 = load <16 x i32>, ptr %3, align 64, !alias.scope !182
  %4 = getelementptr inbounds nuw i8, ptr %v, i64 384
  %_11.i324 = load <16 x i32>, ptr %4, align 64, !alias.scope !182
  %r.i2 = shufflevector <16 x i32> %_10.i323, <16 x i32> %_11.i324, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %5 = getelementptr inbounds nuw i8, ptr %v, i64 192
  %_13.i325 = load <16 x i32>, ptr %5, align 64, !alias.scope !182
  %6 = getelementptr inbounds nuw i8, ptr %v, i64 448
  %_14.i326 = load <16 x i32>, ptr %6, align 64, !alias.scope !182
  %r.i3 = shufflevector <16 x i32> %_13.i325, <16 x i32> %_14.i326, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i4 = shufflevector <16 x i32> %_4.i319, <16 x i32> %_5.i320, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i5 = shufflevector <16 x i32> %_7.i321, <16 x i32> %_8.i322, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i6 = shufflevector <16 x i32> %_10.i323, <16 x i32> %_11.i324, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i7 = shufflevector <16 x i32> %_13.i325, <16 x i32> %_14.i326, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %7 = getelementptr inbounds nuw i8, ptr %v, i64 512
  %_20.i327 = load <16 x i32>, ptr %7, align 64, !alias.scope !182
  %8 = getelementptr inbounds nuw i8, ptr %v, i64 768
  %_21.i328 = load <16 x i32>, ptr %8, align 64, !alias.scope !182
  %r.i8 = shufflevector <16 x i32> %_20.i327, <16 x i32> %_21.i328, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %9 = getelementptr inbounds nuw i8, ptr %v, i64 576
  %_23.i329 = load <16 x i32>, ptr %9, align 64, !alias.scope !182
  %10 = getelementptr inbounds nuw i8, ptr %v, i64 832
  %_24.i330 = load <16 x i32>, ptr %10, align 64, !alias.scope !182
  %r.i9 = shufflevector <16 x i32> %_23.i329, <16 x i32> %_24.i330, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %11 = getelementptr inbounds nuw i8, ptr %v, i64 640
  %_26.i331 = load <16 x i32>, ptr %11, align 64, !alias.scope !182
  %12 = getelementptr inbounds nuw i8, ptr %v, i64 896
  %_27.i332 = load <16 x i32>, ptr %12, align 64, !alias.scope !182
  %r.i10 = shufflevector <16 x i32> %_26.i331, <16 x i32> %_27.i332, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %13 = getelementptr inbounds nuw i8, ptr %v, i64 704
  %_29.i333 = load <16 x i32>, ptr %13, align 64, !alias.scope !182
  %14 = getelementptr inbounds nuw i8, ptr %v, i64 960
  %_30.i334 = load <16 x i32>, ptr %14, align 64, !alias.scope !182
  %r.i11 = shufflevector <16 x i32> %_29.i333, <16 x i32> %_30.i334, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i12 = shufflevector <16 x i32> %_20.i327, <16 x i32> %_21.i328, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i13 = shufflevector <16 x i32> %_23.i329, <16 x i32> %_24.i330, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i14 = shufflevector <16 x i32> %_26.i331, <16 x i32> %_27.i332, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i15 = shufflevector <16 x i32> %_29.i333, <16 x i32> %_30.i334, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i16 = shufflevector <16 x i32> %r.i, <16 x i32> %r.i8, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i17 = shufflevector <16 x i32> %r.i1, <16 x i32> %r.i9, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i18 = shufflevector <16 x i32> %r.i2, <16 x i32> %r.i10, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i19 = shufflevector <16 x i32> %r.i3, <16 x i32> %r.i11, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i20 = shufflevector <16 x i32> %r.i4, <16 x i32> %r.i12, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i21 = shufflevector <16 x i32> %r.i5, <16 x i32> %r.i13, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i22 = shufflevector <16 x i32> %r.i6, <16 x i32> %r.i14, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i23 = shufflevector <16 x i32> %r.i7, <16 x i32> %r.i15, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11, i32 16, i32 17, i32 18, i32 19, i32 24, i32 25, i32 26, i32 27>
  %r.i24 = shufflevector <16 x i32> %r.i, <16 x i32> %r.i8, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i25 = shufflevector <16 x i32> %r.i1, <16 x i32> %r.i9, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i26 = shufflevector <16 x i32> %r.i2, <16 x i32> %r.i10, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i27 = shufflevector <16 x i32> %r.i3, <16 x i32> %r.i11, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i28 = shufflevector <16 x i32> %r.i4, <16 x i32> %r.i12, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i29 = shufflevector <16 x i32> %r.i5, <16 x i32> %r.i13, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i30 = shufflevector <16 x i32> %r.i6, <16 x i32> %r.i14, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i31 = shufflevector <16 x i32> %r.i7, <16 x i32> %r.i15, <16 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15, i32 20, i32 21, i32 22, i32 23, i32 28, i32 29, i32 30, i32 31>
  %r.i32 = shufflevector <16 x i32> %r.i16, <16 x i32> %r.i18, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i33 = shufflevector <16 x i32> %r.i17, <16 x i32> %r.i19, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i34 = shufflevector <16 x i32> %r.i16, <16 x i32> %r.i18, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i35 = shufflevector <16 x i32> %r.i17, <16 x i32> %r.i19, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i36 = shufflevector <16 x i32> %r.i20, <16 x i32> %r.i22, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i37 = shufflevector <16 x i32> %r.i21, <16 x i32> %r.i23, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i38 = shufflevector <16 x i32> %r.i20, <16 x i32> %r.i22, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i39 = shufflevector <16 x i32> %r.i21, <16 x i32> %r.i23, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i40 = shufflevector <16 x i32> %r.i24, <16 x i32> %r.i26, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i41 = shufflevector <16 x i32> %r.i25, <16 x i32> %r.i27, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i42 = shufflevector <16 x i32> %r.i24, <16 x i32> %r.i26, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i43 = shufflevector <16 x i32> %r.i25, <16 x i32> %r.i27, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i44 = shufflevector <16 x i32> %r.i28, <16 x i32> %r.i30, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i45 = shufflevector <16 x i32> %r.i29, <16 x i32> %r.i31, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  %r.i46 = shufflevector <16 x i32> %r.i28, <16 x i32> %r.i30, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i47 = shufflevector <16 x i32> %r.i29, <16 x i32> %r.i31, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  %r.i48 = shufflevector <16 x i32> %r.i32, <16 x i32> %r.i33, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  store <16 x i32> %r.i48, ptr %v, align 64, !alias.scope !182
  %r.i49 = shufflevector <16 x i32> %r.i32, <16 x i32> %r.i33, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  store <16 x i32> %r.i49, ptr %1, align 64, !alias.scope !182
  %r.i50 = shufflevector <16 x i32> %r.i34, <16 x i32> %r.i35, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  store <16 x i32> %r.i50, ptr %3, align 64, !alias.scope !182
  %r.i51 = shufflevector <16 x i32> %r.i34, <16 x i32> %r.i35, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  store <16 x i32> %r.i51, ptr %5, align 64, !alias.scope !182
  %r.i52 = shufflevector <16 x i32> %r.i36, <16 x i32> %r.i37, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  store <16 x i32> %r.i52, ptr %0, align 64, !alias.scope !182
  %r.i53 = shufflevector <16 x i32> %r.i36, <16 x i32> %r.i37, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  store <16 x i32> %r.i53, ptr %2, align 64, !alias.scope !182
  %r.i54 = shufflevector <16 x i32> %r.i38, <16 x i32> %r.i39, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  store <16 x i32> %r.i54, ptr %4, align 64, !alias.scope !182
  %r.i55 = shufflevector <16 x i32> %r.i38, <16 x i32> %r.i39, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  store <16 x i32> %r.i55, ptr %6, align 64, !alias.scope !182
  %r.i56 = shufflevector <16 x i32> %r.i40, <16 x i32> %r.i41, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  store <16 x i32> %r.i56, ptr %7, align 64, !alias.scope !182
  %r.i57 = shufflevector <16 x i32> %r.i40, <16 x i32> %r.i41, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  store <16 x i32> %r.i57, ptr %9, align 64, !alias.scope !182
  %r.i58 = shufflevector <16 x i32> %r.i42, <16 x i32> %r.i43, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  store <16 x i32> %r.i58, ptr %11, align 64, !alias.scope !182
  %r.i59 = shufflevector <16 x i32> %r.i42, <16 x i32> %r.i43, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  store <16 x i32> %r.i59, ptr %13, align 64, !alias.scope !182
  %r.i60 = shufflevector <16 x i32> %r.i44, <16 x i32> %r.i45, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  store <16 x i32> %r.i60, ptr %8, align 64, !alias.scope !182
  %r.i61 = shufflevector <16 x i32> %r.i44, <16 x i32> %r.i45, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  store <16 x i32> %r.i61, ptr %10, align 64, !alias.scope !182
  %r.i62 = shufflevector <16 x i32> %r.i46, <16 x i32> %r.i47, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 4, i32 20, i32 5, i32 21, i32 8, i32 24, i32 9, i32 25, i32 12, i32 28, i32 13, i32 29>
  store <16 x i32> %r.i62, ptr %12, align 64, !alias.scope !182
  %r.i63 = shufflevector <16 x i32> %r.i46, <16 x i32> %r.i47, <16 x i32> <i32 2, i32 18, i32 3, i32 19, i32 6, i32 22, i32 7, i32 23, i32 10, i32 26, i32 11, i32 27, i32 14, i32 30, i32 15, i32 31>
  store <16 x i32> %r.i63, ptr %14, align 64, !alias.scope !182
  ret void
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
define void @agave_transpose_8(ptr noalias nofree noundef align 32 captures(none) dereferenceable(256) %v) unnamed_addr #1 {
start:
  %a.i102 = load <8 x i32>, ptr %v, align 32, !alias.scope !185
  %0 = getelementptr inbounds nuw i8, ptr %v, i64 32
  %b.i103 = load <8 x i32>, ptr %0, align 32, !alias.scope !185
  %1 = getelementptr inbounds nuw i8, ptr %v, i64 64
  %c.i104 = load <8 x i32>, ptr %1, align 32, !alias.scope !185
  %2 = getelementptr inbounds nuw i8, ptr %v, i64 96
  %d.i105 = load <8 x i32>, ptr %2, align 32, !alias.scope !185
  %3 = getelementptr inbounds nuw i8, ptr %v, i64 128
  %e.i106 = load <8 x i32>, ptr %3, align 32, !alias.scope !185
  %4 = getelementptr inbounds nuw i8, ptr %v, i64 160
  %f.i107 = load <8 x i32>, ptr %4, align 32, !alias.scope !185
  %5 = getelementptr inbounds nuw i8, ptr %v, i64 192
  %g.i108 = load <8 x i32>, ptr %5, align 32, !alias.scope !185
  %6 = getelementptr inbounds nuw i8, ptr %v, i64 224
  %h.i109 = load <8 x i32>, ptr %6, align 32, !alias.scope !185
  %r.i = shufflevector <8 x i32> %a.i102, <8 x i32> %b.i103, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i1 = shufflevector <8 x i32> %a.i102, <8 x i32> %b.i103, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %r.i2 = shufflevector <8 x i32> %c.i104, <8 x i32> %d.i105, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i3 = shufflevector <8 x i32> %c.i104, <8 x i32> %d.i105, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %r.i4 = shufflevector <8 x i32> %e.i106, <8 x i32> %f.i107, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i5 = shufflevector <8 x i32> %e.i106, <8 x i32> %f.i107, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %r.i6 = shufflevector <8 x i32> %g.i108, <8 x i32> %h.i109, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  %r.i7 = shufflevector <8 x i32> %g.i108, <8 x i32> %h.i109, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  %7 = shufflevector <8 x i32> %r.i, <8 x i32> %r.i2, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %8 = shufflevector <8 x i32> %r.i, <8 x i32> %r.i2, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %9 = shufflevector <8 x i32> %r.i1, <8 x i32> %r.i3, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %10 = shufflevector <8 x i32> %r.i1, <8 x i32> %r.i3, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %11 = shufflevector <8 x i32> %r.i4, <8 x i32> %r.i6, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %12 = shufflevector <8 x i32> %r.i4, <8 x i32> %r.i6, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %13 = shufflevector <8 x i32> %r.i5, <8 x i32> %r.i7, <8 x i32> <i32 0, i32 1, i32 8, i32 9, i32 4, i32 5, i32 12, i32 13>
  %14 = shufflevector <8 x i32> %r.i5, <8 x i32> %r.i7, <8 x i32> <i32 2, i32 3, i32 10, i32 11, i32 6, i32 7, i32 14, i32 15>
  %15 = shufflevector <8 x i32> %7, <8 x i32> %11, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  store <8 x i32> %15, ptr %v, align 32, !alias.scope !185
  %16 = shufflevector <8 x i32> %8, <8 x i32> %12, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  store <8 x i32> %16, ptr %0, align 32, !alias.scope !185
  %17 = shufflevector <8 x i32> %9, <8 x i32> %13, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  store <8 x i32> %17, ptr %1, align 32, !alias.scope !185
  %18 = shufflevector <8 x i32> %10, <8 x i32> %14, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 9, i32 10, i32 11>
  store <8 x i32> %18, ptr %2, align 32, !alias.scope !185
  %19 = shufflevector <8 x i32> %7, <8 x i32> %11, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  store <8 x i32> %19, ptr %3, align 32, !alias.scope !185
  %20 = shufflevector <8 x i32> %8, <8 x i32> %12, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  store <8 x i32> %20, ptr %4, align 32, !alias.scope !185
  %21 = shufflevector <8 x i32> %9, <8 x i32> %13, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  store <8 x i32> %21, ptr %5, align 32, !alias.scope !185
  %22 = shufflevector <8 x i32> %10, <8 x i32> %14, <8 x i32> <i32 4, i32 5, i32 6, i32 7, i32 12, i32 13, i32 14, i32 15>
  store <8 x i32> %22, ptr %6, align 32, !alias.scope !185
  ret void
}

; Function Attrs: mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #6

; Function Attrs: mustprogress nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #7

; Function Attrs: mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #6

; Function Attrs: nounwind nonlazybind uwtable
declare noundef range(i32 0, 10) i32 @rust_eh_personality(i32 noundef, i32 noundef, i64 noundef, ptr noundef, ptr noundef) unnamed_addr #8

; core::slice::index::slice_index_fail
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtNtCsgxBkk5gSRhY_4core5slice5index16slice_index_fail(i64 noundef, i64 noundef, i64 noundef, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24)) unnamed_addr #9

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite)
declare void @llvm.experimental.noalias.scope.decl(metadata) #10

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare <16 x i32> @llvm.fshl.v16i32(<16 x i32>, <16 x i32>, <16 x i32>) #11

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare <8 x i32> @llvm.fshl.v8i32(<8 x i32>, <8 x i32>, <8 x i32>) #11

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare <8 x i64> @llvm.umin.v8i64(<8 x i64>, <8 x i64>) #11

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+avx512f,+f16c,+fma,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3,+avx,+avx2,+avx512bw,+avx512f,+f16c,+fma,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }
attributes #1 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }
attributes #2 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+avx512f,+f16c,+fma,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3,+avx,+avx2,+avx512bw,+avx512f,+f16c,+fma,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }
attributes #3 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }
attributes #4 = { nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+avx512f,+f16c,+fma,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3,+avx,+avx2,+avx512bw,+avx512f,+f16c,+fma,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }
attributes #5 = { nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }
attributes #6 = { mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #7 = { mustprogress nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #8 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #9 = { cold noinline noreturn nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #10 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite) }
attributes #11 = { nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none) }
attributes #12 = { noinline noreturn nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{!5}
!5 = distinct !{!5, !6, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x868avx512bw16__mm512_add_epi16: %_0"}
!6 = distinct !{!6, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x868avx512bw16__mm512_add_epi16"}
!7 = !{!8, !9, !10, !12}
!8 = distinct !{!8, !6, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x868avx512bw16__mm512_add_epi16: %a"}
!9 = distinct !{!9, !6, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x868avx512bw16__mm512_add_epi16: %b"}
!10 = distinct !{!10, !11, !"_RNvXs_NtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4archNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iNtB4_5Lanes7add_u16: %self"}
!11 = distinct !{!11, !"_RNvXs_NtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4archNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iNtB4_5Lanes7add_u16"}
!12 = distinct !{!12, !11, !"_RNvXs_NtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4archNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iNtB4_5Lanes7add_u16: %o"}
!13 = !{!14}
!14 = distinct !{!14, !15, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x864avx216__mm256_add_epi16: %_0"}
!15 = distinct !{!15, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x864avx216__mm256_add_epi16"}
!16 = !{!17, !19}
!17 = distinct !{!17, !18, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %batch"}
!18 = distinct !{!18, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_"}
!19 = distinct !{!19, !18, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %acc"}
!20 = !{!"branch_weights", !"expected", i32 1, i32 2000}
!21 = !{!"branch_weights", i32 22648651, i32 -1285701762}
!22 = !{!23, !25, !26, !17, !19}
!23 = distinct !{!23, !24, !"_RNCINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEs_0B8_: %_0"}
!24 = distinct !{!24, !"_RNCINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEs_0B8_"}
!25 = distinct !{!25, !24, !"_RNCINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEs_0B8_: %_1"}
!26 = distinct !{!26, !24, !"_RNCINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEs_0B8_: %off"}
!27 = !{!25, !26, !17, !19}
!28 = !{!29}
!29 = distinct !{!29, !30, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %m"}
!30 = distinct !{!30, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_"}
!31 = !{!32, !29, !33, !35, !36, !37, !38, !39, !40, !17, !19}
!32 = distinct !{!32, !30, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %v"}
!33 = distinct !{!33, !34, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %_0"}
!34 = distinct !{!34, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_"}
!35 = distinct !{!35, !34, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %cv"}
!36 = distinct !{!36, !34, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %iv"}
!37 = distinct !{!37, !34, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %counter_lo"}
!38 = distinct !{!38, !34, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %counter_hi"}
!39 = distinct !{!39, !34, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %block_len"}
!40 = distinct !{!40, !34, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %flags"}
!41 = !{}
!42 = !{!32, !33, !35, !36, !37, !38, !39, !40, !17, !19}
!43 = !{!44}
!44 = distinct !{!44, !45, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %m"}
!45 = distinct !{!45, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_"}
!46 = !{!47, !44, !48, !50, !51, !52, !53, !54, !55, !17}
!47 = distinct !{!47, !45, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %v"}
!48 = distinct !{!48, !49, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %_0"}
!49 = distinct !{!49, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_"}
!50 = distinct !{!50, !49, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %cv"}
!51 = distinct !{!51, !49, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %iv"}
!52 = distinct !{!52, !49, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %counter_lo"}
!53 = distinct !{!53, !49, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %counter_hi"}
!54 = distinct !{!54, !49, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %block_len"}
!55 = distinct !{!55, !49, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %flags"}
!56 = !{!47, !48, !50, !51, !52, !53, !54, !55, !17}
!57 = !{!17}
!58 = !{!59, !61}
!59 = distinct !{!59, !60, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %batch"}
!60 = distinct !{!60, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_"}
!61 = distinct !{!61, !60, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %acc"}
!62 = !{!63, !65, !67, !68, !59, !61}
!63 = distinct !{!63, !64, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256: %_0"}
!64 = distinct !{!64, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256"}
!65 = distinct !{!65, !66, !"_RNCINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEs_0B8_: %_0"}
!66 = distinct !{!66, !"_RNCINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEs_0B8_"}
!67 = distinct !{!67, !66, !"_RNCINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEs_0B8_: %_1"}
!68 = distinct !{!68, !66, !"_RNCINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch14compress_batchNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEs_0B8_: %off"}
!69 = !{!70, !65, !67, !68, !59, !61}
!70 = distinct !{!70, !71, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256: %_0"}
!71 = distinct !{!71, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256"}
!72 = !{!73, !65, !67, !68, !59, !61}
!73 = distinct !{!73, !74, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256: %_0"}
!74 = distinct !{!74, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256"}
!75 = !{!76, !65, !67, !68, !59, !61}
!76 = distinct !{!76, !77, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256: %_0"}
!77 = distinct !{!77, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256"}
!78 = !{!79, !65, !67, !68, !59, !61}
!79 = distinct !{!79, !80, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256: %_0"}
!80 = distinct !{!80, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256"}
!81 = !{!82, !65, !67, !68, !59, !61}
!82 = distinct !{!82, !83, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256: %_0"}
!83 = distinct !{!83, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256"}
!84 = !{!85, !65, !67, !68, !59, !61}
!85 = distinct !{!85, !86, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256: %_0"}
!86 = distinct !{!86, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256"}
!87 = !{!88, !65, !67, !68, !59, !61}
!88 = distinct !{!88, !89, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256: %_0"}
!89 = distinct !{!89, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256"}
!90 = !{!67, !68, !59, !61}
!91 = !{!65, !67, !68, !59, !61}
!92 = !{!93}
!93 = distinct !{!93, !94, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %m"}
!94 = distinct !{!94, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_"}
!95 = !{!96, !93, !97, !99, !100, !101, !102, !103, !104, !59, !61}
!96 = distinct !{!96, !94, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %v"}
!97 = distinct !{!97, !98, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %_0"}
!98 = distinct !{!98, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_"}
!99 = distinct !{!99, !98, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %cv"}
!100 = distinct !{!100, !98, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %iv"}
!101 = distinct !{!101, !98, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %counter_lo"}
!102 = distinct !{!102, !98, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %counter_hi"}
!103 = distinct !{!103, !98, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %block_len"}
!104 = distinct !{!104, !98, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %flags"}
!105 = !{!96, !97, !99, !100, !101, !102, !103, !104, !59, !61}
!106 = !{!107}
!107 = distinct !{!107, !108, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %m"}
!108 = distinct !{!108, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_"}
!109 = !{!110, !107, !111, !113, !114, !115, !116, !117, !118, !59}
!110 = distinct !{!110, !108, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %v"}
!111 = distinct !{!111, !112, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %_0"}
!112 = distinct !{!112, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_"}
!113 = distinct !{!113, !112, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %cv"}
!114 = distinct !{!114, !112, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %iv"}
!115 = distinct !{!115, !112, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %counter_lo"}
!116 = distinct !{!116, !112, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %counter_hi"}
!117 = distinct !{!117, !112, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %block_len"}
!118 = distinct !{!118, !112, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %flags"}
!119 = !{!110, !111, !113, !114, !115, !116, !117, !118, !59}
!120 = !{!121, !59}
!121 = distinct !{!121, !122, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256: %_0"}
!122 = distinct !{!122, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx18__mm256_loadu_si256"}
!123 = !{!124, !126, !128, !59}
!124 = distinct !{!124, !125, !"_RNvMNtNtCsgxBkk5gSRhY_4core3ptr7mut_ptrONtNtNtB6_9core_arch3x867___m256i15write_unalignedCskTCvM42Zdvn_20agave_lthash_extract: %val"}
!125 = distinct !{!125, !"_RNvMNtNtCsgxBkk5gSRhY_4core3ptr7mut_ptrONtNtNtB6_9core_arch3x867___m256i15write_unalignedCskTCvM42Zdvn_20agave_lthash_extract"}
!126 = distinct !{!126, !127, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx19__mm256_storeu_si256: %a"}
!127 = distinct !{!127, !"_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x863avx19__mm256_storeu_si256"}
!128 = distinct !{!128, !129, !"_RNvXNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4archNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iNtB2_5Lanes5store: %self"}
!129 = distinct !{!129, !"_RNvXNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4archNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iNtB2_5Lanes5store"}
!130 = !{!131}
!131 = distinct !{!131, !132, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %cv"}
!132 = distinct !{!132, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_"}
!133 = !{!134}
!134 = distinct !{!134, !132, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %iv"}
!135 = !{!136, !134, !137, !138, !139, !140, !141}
!136 = distinct !{!136, !132, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %_0"}
!137 = distinct !{!137, !132, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %m"}
!138 = distinct !{!138, !132, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %counter_lo"}
!139 = distinct !{!139, !132, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %counter_hi"}
!140 = distinct !{!140, !132, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %block_len"}
!141 = distinct !{!141, !132, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %flags"}
!142 = !{!136, !131, !137, !138, !139, !140, !141}
!143 = !{!144}
!144 = distinct !{!144, !145, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %m"}
!145 = distinct !{!145, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_"}
!146 = !{!147, !144, !136, !131, !134, !138, !139, !140, !141}
!147 = distinct !{!147, !145, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %v"}
!148 = !{!147, !136, !131, !134, !138, !139, !140, !141}
!149 = !{!131, !134, !137, !138, !139, !140, !141}
!150 = !{!151}
!151 = distinct !{!151, !152, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %cv"}
!152 = distinct !{!152, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_"}
!153 = !{!154}
!154 = distinct !{!154, !152, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %iv"}
!155 = !{!156, !154, !157, !158, !159, !160, !161}
!156 = distinct !{!156, !152, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %_0"}
!157 = distinct !{!157, !152, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %m"}
!158 = distinct !{!158, !152, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %counter_lo"}
!159 = distinct !{!159, !152, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %counter_hi"}
!160 = distinct !{!160, !152, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %block_len"}
!161 = distinct !{!161, !152, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch12compress_preNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %flags"}
!162 = !{!156, !151, !157, !158, !159, !160, !161}
!163 = !{!164}
!164 = distinct !{!164, !165, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %m"}
!165 = distinct !{!165, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_"}
!166 = !{!167, !164, !156, !151, !154, !158, !159, !160, !161}
!167 = distinct !{!167, !165, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch5roundNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %v"}
!168 = !{!167, !156, !151, !154, !158, !159, !160, !161}
!169 = !{!151, !154, !157, !158, !159, !160, !161}
!170 = !{!171}
!171 = distinct !{!171, !172, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch1gNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %v"}
!172 = distinct !{!172, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch1gNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_"}
!173 = !{!174, !175}
!174 = distinct !{!174, !172, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch1gNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %mx"}
!175 = distinct !{!175, !172, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch1gNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iEB6_: %my"}
!176 = !{!177}
!177 = distinct !{!177, !178, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch1gNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %v"}
!178 = distinct !{!178, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch1gNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_"}
!179 = !{!180, !181}
!180 = distinct !{!180, !178, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch1gNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %mx"}
!181 = distinct !{!181, !178, !"_RINvNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4arch1gNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iEB6_: %my"}
!182 = !{!183}
!183 = distinct !{!183, !184, !"_RNvXs_NtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4archNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iNtB4_5Lanes9transpose: %io.0"}
!184 = distinct !{!184, !"_RNvXs_NtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4archNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m512iNtB4_5Lanes9transpose"}
!185 = !{!186}
!186 = distinct !{!186, !187, !"_RNvXNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4archNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iNtB2_5Lanes9transpose: %io.0"}
!187 = distinct !{!187, !"_RNvXNtNtCskTCvM42Zdvn_20agave_lthash_extract5batch4archNtNtNtCsgxBkk5gSRhY_4core9core_arch3x867___m256iNtB2_5Lanes9transpose"}
