import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_cmovznz_u64

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fiat_25519_selectznz_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: i8, %arg2: !llvm.ptr, %arg3: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %5 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %6 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %7 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %8 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %9 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%5) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%6) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%7) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%8) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%9) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    %10 = "llvm.load"(%arg2) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %11 = "llvm.load"(%arg3) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%5, %arg1, %10, %11) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_cmovznz_u64, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i8, i64, i64) -> ()
    %12 = "llvm.getelementptr"(%arg2, %1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %13 = "llvm.load"(%12) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %14 = "llvm.getelementptr"(%arg3, %1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %15 = "llvm.load"(%14) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%6, %arg1, %13, %15) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_cmovznz_u64, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i8, i64, i64) -> ()
    %16 = "llvm.getelementptr"(%arg2, %2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %17 = "llvm.load"(%16) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %18 = "llvm.getelementptr"(%arg3, %2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %19 = "llvm.load"(%18) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%7, %arg1, %17, %19) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_cmovznz_u64, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i8, i64, i64) -> ()
    %20 = "llvm.getelementptr"(%arg2, %3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %21 = "llvm.load"(%20) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %22 = "llvm.getelementptr"(%arg3, %3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %23 = "llvm.load"(%22) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%8, %arg1, %21, %23) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_cmovznz_u64, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i8, i64, i64) -> ()
    %24 = "llvm.getelementptr"(%arg2, %4) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %25 = "llvm.load"(%24) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %26 = "llvm.getelementptr"(%arg3, %4) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %27 = "llvm.load"(%26) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%9, %arg1, %25, %27) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_cmovznz_u64, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i8, i64, i64) -> ()
    %28 = "llvm.load"(%5) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.store"(%28, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %29 = "llvm.load"(%6) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %30 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%29, %30) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %31 = "llvm.load"(%7) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %32 = "llvm.getelementptr"(%arg0, %2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%31, %32) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %33 = "llvm.load"(%8) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %34 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%33, %34) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %35 = "llvm.load"(%9) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %36 = "llvm.getelementptr"(%arg0, %4) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%35, %36) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%9) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%8) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%7) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%6) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%5) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

def fiat_25519_selectznz : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 8, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fiat_25519_selectznz_region with
    @fiat_25519_cmovznz_u64 := fiat_25519_cmovznz_u64]

end Firedancer.Ref
