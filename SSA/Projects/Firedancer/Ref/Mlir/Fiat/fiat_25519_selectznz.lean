-- build/native/gcc/mlir_canonicalized/ref/region/fiat_25519_selectznz.mlir
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_cmovznz_u64

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fiat_25519_selectznz_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: i8, %arg2: !llvm.ptr, %arg3: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %2 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %3 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %4 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %5 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%1) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%2) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%3) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%4) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%5) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    %6 = "llvm.load"(%arg2) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %7 = "llvm.load"(%arg3) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%1, %arg1, %6, %7) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_cmovznz_u64, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i8, i64, i64) -> ()
    %8 = "llvm.getelementptr"(%arg2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %9 = "llvm.load"(%8) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %10 = "llvm.getelementptr"(%arg3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %11 = "llvm.load"(%10) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%2, %arg1, %9, %11) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_cmovznz_u64, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i8, i64, i64) -> ()
    %12 = "llvm.getelementptr"(%arg2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %13 = "llvm.load"(%12) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %14 = "llvm.getelementptr"(%arg3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %15 = "llvm.load"(%14) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%3, %arg1, %13, %15) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_cmovznz_u64, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i8, i64, i64) -> ()
    %16 = "llvm.getelementptr"(%arg2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %17 = "llvm.load"(%16) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %18 = "llvm.getelementptr"(%arg3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %19 = "llvm.load"(%18) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%4, %arg1, %17, %19) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_cmovznz_u64, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i8, i64, i64) -> ()
    %20 = "llvm.getelementptr"(%arg2) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %21 = "llvm.load"(%20) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %22 = "llvm.getelementptr"(%arg3) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %23 = "llvm.load"(%22) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.call"(%5, %arg1, %21, %23) <{CConv = #llvm.cconv<fastcc>, callee = @fiat_25519_cmovznz_u64, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, i8, i64, i64) -> ()
    %24 = "llvm.load"(%1) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.store"(%24, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %25 = "llvm.load"(%2) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %26 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%25, %26) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %27 = "llvm.load"(%3) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %28 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%27, %28) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %29 = "llvm.load"(%4) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %30 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%29, %30) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %31 = "llvm.load"(%5) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %32 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%31, %32) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%5) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%4) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%3) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%2) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%1) <{size = 8 : i64}> : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
]

sllvm_cfg_def fiat_25519_selectznz : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 8, SLLVM.Ty.ptr]) [] :=
  [sllvm_cfg_of| fiat_25519_selectznz_region with
    @fiat_25519_cmovznz_u64 := fiat_25519_cmovznz_u64]

end Firedancer.Ref
