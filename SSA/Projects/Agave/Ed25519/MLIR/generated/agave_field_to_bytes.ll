; ModuleID = '/home/nine/Documents/anza-code/.lmf-rir-ed25519/SSA/Projects/Agave/Ed25519/MLIR/generated/agave_field_to_bytes.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
define void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement518to_bytes(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([32 x i8]) align 1 captures(none) dereferenceable(32) initializes((0, 32)) %s, ptr dead_on_return noalias nofree noundef readonly align 8 captures(none) dereferenceable(40) %self) unnamed_addr #0 {
start:
  %limbs.sroa.0.0.copyload = load i64, ptr %self, align 8
  %limbs.sroa.19.0.self.sroa_idx = getelementptr inbounds nuw i8, ptr %self, i64 8
  %limbs.sroa.19.0.copyload = load i64, ptr %limbs.sroa.19.0.self.sroa_idx, align 8
  %limbs.sroa.37.0.self.sroa_idx = getelementptr inbounds nuw i8, ptr %self, i64 16
  %limbs.sroa.37.0.copyload = load i64, ptr %limbs.sroa.37.0.self.sroa_idx, align 8
  %limbs.sroa.56.0.self.sroa_idx = getelementptr inbounds nuw i8, ptr %self, i64 24
  %limbs.sroa.56.0.copyload = load i64, ptr %limbs.sroa.56.0.self.sroa_idx, align 8
  %limbs.sroa.74.0.self.sroa_idx = getelementptr inbounds nuw i8, ptr %self, i64 32
  %limbs.sroa.74.0.copyload = load i64, ptr %limbs.sroa.74.0.self.sroa_idx, align 8
  %_98 = lshr i64 %limbs.sroa.0.0.copyload, 51
  %_100 = lshr i64 %limbs.sroa.19.0.copyload, 51
  %_102 = lshr i64 %limbs.sroa.37.0.copyload, 51
  %_104 = lshr i64 %limbs.sroa.56.0.copyload, 51
  %_106 = lshr i64 %limbs.sroa.74.0.copyload, 51
  %0 = and i64 %limbs.sroa.0.0.copyload, 2251799813685247
  %1 = and i64 %limbs.sroa.19.0.copyload, 2251799813685247
  %2 = and i64 %limbs.sroa.37.0.copyload, 2251799813685247
  %3 = and i64 %limbs.sroa.56.0.copyload, 2251799813685247
  %4 = and i64 %limbs.sroa.74.0.copyload, 2251799813685247
  %_108 = mul nuw nsw i64 %_106, 19
  %5 = add nuw nsw i64 %_108, %0
  %6 = add nuw nsw i64 %1, %_98
  %7 = add nuw nsw i64 %2, %_100
  %8 = add nuw nsw i64 %3, %_102
  %9 = add nuw nsw i64 %4, %_104
  %_4 = add nuw nsw i64 %5, 19
  %10 = lshr i64 %_4, 51
  %_6 = add nuw nsw i64 %10, %6
  %11 = lshr i64 %_6, 51
  %_8 = add nuw nsw i64 %11, %7
  %12 = lshr i64 %_8, 51
  %_10 = add nuw nsw i64 %12, %8
  %13 = lshr i64 %_10, 51
  %_12 = add nuw nsw i64 %13, %9
  %14 = lshr i64 %_12, 51
  %_14 = mul nuw nsw i64 %14, 19
  %15 = add nuw nsw i64 %_14, %5
  %_15 = lshr i64 %15, 51
  %16 = add nuw nsw i64 %_15, %6
  %_17 = lshr i64 %16, 51
  %17 = add nuw nsw i64 %_17, %7
  %18 = and i64 %16, 2251799813685247
  %_19 = lshr i64 %17, 51
  %19 = add nuw nsw i64 %_19, %8
  %20 = and i64 %17, 2251799813685247
  %_21 = lshr i64 %19, 51
  %21 = add nuw nsw i64 %_21, %9
  %22 = and i64 %19, 2251799813685247
  %23 = and i64 %21, 2251799813685247
  %24 = trunc i64 %15 to i8
  store i8 %24, ptr %s, align 1
  %_24 = lshr i64 %15, 8
  %25 = getelementptr inbounds nuw i8, ptr %s, i64 1
  %26 = trunc i64 %_24 to i8
  store i8 %26, ptr %25, align 1
  %_26 = lshr i64 %15, 16
  %27 = getelementptr inbounds nuw i8, ptr %s, i64 2
  %28 = trunc i64 %_26 to i8
  store i8 %28, ptr %27, align 1
  %_28 = lshr i64 %15, 24
  %29 = getelementptr inbounds nuw i8, ptr %s, i64 3
  %30 = trunc i64 %_28 to i8
  store i8 %30, ptr %29, align 1
  %_30 = lshr i64 %15, 32
  %31 = getelementptr inbounds nuw i8, ptr %s, i64 4
  %32 = trunc i64 %_30 to i8
  store i8 %32, ptr %31, align 1
  %_32 = lshr i64 %15, 40
  %33 = getelementptr inbounds nuw i8, ptr %s, i64 5
  %34 = trunc i64 %_32 to i8
  store i8 %34, ptr %33, align 1
  %35 = lshr i64 %15, 48
  %_35 = and i64 %35, 7
  %_37 = shl nuw nsw i64 %18, 3
  %_34 = or disjoint i64 %_37, %_35
  %36 = getelementptr inbounds nuw i8, ptr %s, i64 6
  %37 = trunc i64 %_34 to i8
  store i8 %37, ptr %36, align 1
  %_39 = lshr i64 %16, 5
  %38 = getelementptr inbounds nuw i8, ptr %s, i64 7
  %39 = trunc i64 %_39 to i8
  store i8 %39, ptr %38, align 1
  %_41 = lshr i64 %16, 13
  %40 = getelementptr inbounds nuw i8, ptr %s, i64 8
  %41 = trunc i64 %_41 to i8
  store i8 %41, ptr %40, align 1
  %_43 = lshr i64 %16, 21
  %42 = getelementptr inbounds nuw i8, ptr %s, i64 9
  %43 = trunc i64 %_43 to i8
  store i8 %43, ptr %42, align 1
  %_45 = lshr i64 %16, 29
  %44 = getelementptr inbounds nuw i8, ptr %s, i64 10
  %45 = trunc i64 %_45 to i8
  store i8 %45, ptr %44, align 1
  %_47 = lshr i64 %16, 37
  %46 = getelementptr inbounds nuw i8, ptr %s, i64 11
  %47 = trunc i64 %_47 to i8
  store i8 %47, ptr %46, align 1
  %_50 = lshr i64 %18, 45
  %_52 = shl nuw nsw i64 %20, 6
  %_49 = or disjoint i64 %_52, %_50
  %48 = getelementptr inbounds nuw i8, ptr %s, i64 12
  %49 = trunc i64 %_49 to i8
  store i8 %49, ptr %48, align 1
  %_54 = lshr i64 %17, 2
  %50 = getelementptr inbounds nuw i8, ptr %s, i64 13
  %51 = trunc i64 %_54 to i8
  store i8 %51, ptr %50, align 1
  %_56 = lshr i64 %17, 10
  %52 = getelementptr inbounds nuw i8, ptr %s, i64 14
  %53 = trunc i64 %_56 to i8
  store i8 %53, ptr %52, align 1
  %_58 = lshr i64 %17, 18
  %54 = getelementptr inbounds nuw i8, ptr %s, i64 15
  %55 = trunc i64 %_58 to i8
  store i8 %55, ptr %54, align 1
  %_60 = lshr i64 %17, 26
  %56 = getelementptr inbounds nuw i8, ptr %s, i64 16
  %57 = trunc i64 %_60 to i8
  store i8 %57, ptr %56, align 1
  %_62 = lshr i64 %17, 34
  %58 = getelementptr inbounds nuw i8, ptr %s, i64 17
  %59 = trunc i64 %_62 to i8
  store i8 %59, ptr %58, align 1
  %_64 = lshr i64 %17, 42
  %60 = getelementptr inbounds nuw i8, ptr %s, i64 18
  %61 = trunc i64 %_64 to i8
  store i8 %61, ptr %60, align 1
  %_67 = lshr i64 %20, 50
  %_69 = shl nuw nsw i64 %22, 1
  %_66 = or disjoint i64 %_69, %_67
  %62 = getelementptr inbounds nuw i8, ptr %s, i64 19
  %63 = trunc i64 %_66 to i8
  store i8 %63, ptr %62, align 1
  %_71 = lshr i64 %19, 7
  %64 = getelementptr inbounds nuw i8, ptr %s, i64 20
  %65 = trunc i64 %_71 to i8
  store i8 %65, ptr %64, align 1
  %_73 = lshr i64 %19, 15
  %66 = getelementptr inbounds nuw i8, ptr %s, i64 21
  %67 = trunc i64 %_73 to i8
  store i8 %67, ptr %66, align 1
  %_75 = lshr i64 %19, 23
  %68 = getelementptr inbounds nuw i8, ptr %s, i64 22
  %69 = trunc i64 %_75 to i8
  store i8 %69, ptr %68, align 1
  %_77 = lshr i64 %19, 31
  %70 = getelementptr inbounds nuw i8, ptr %s, i64 23
  %71 = trunc i64 %_77 to i8
  store i8 %71, ptr %70, align 1
  %_79 = lshr i64 %19, 39
  %72 = getelementptr inbounds nuw i8, ptr %s, i64 24
  %73 = trunc i64 %_79 to i8
  store i8 %73, ptr %72, align 1
  %_82 = lshr i64 %22, 47
  %_84 = shl nuw nsw i64 %23, 4
  %_81 = or disjoint i64 %_84, %_82
  %74 = getelementptr inbounds nuw i8, ptr %s, i64 25
  %75 = trunc i64 %_81 to i8
  store i8 %75, ptr %74, align 1
  %_86 = lshr i64 %21, 4
  %76 = getelementptr inbounds nuw i8, ptr %s, i64 26
  %77 = trunc i64 %_86 to i8
  store i8 %77, ptr %76, align 1
  %_88 = lshr i64 %21, 12
  %78 = getelementptr inbounds nuw i8, ptr %s, i64 27
  %79 = trunc i64 %_88 to i8
  store i8 %79, ptr %78, align 1
  %_90 = lshr i64 %21, 20
  %80 = getelementptr inbounds nuw i8, ptr %s, i64 28
  %81 = trunc i64 %_90 to i8
  store i8 %81, ptr %80, align 1
  %_92 = lshr i64 %21, 28
  %82 = getelementptr inbounds nuw i8, ptr %s, i64 29
  %83 = trunc i64 %_92 to i8
  store i8 %83, ptr %82, align 1
  %_94 = lshr i64 %21, 36
  %84 = getelementptr inbounds nuw i8, ptr %s, i64 30
  %85 = trunc i64 %_94 to i8
  store i8 %85, ptr %84, align 1
  %_96 = lshr i64 %23, 44
  %86 = getelementptr inbounds nuw i8, ptr %s, i64 31
  %87 = trunc nuw nsw i64 %_96 to i8
  store i8 %87, ptr %86, align 1
  ret void
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
