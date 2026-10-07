-- build/native/gcc/mlir_canonicalized/ref/region/fd_f25519_is_zero.mlir
module

public import SSA.Projects.SLLVM.Cfg

@[expose] public section

namespace Firedancer.Ref
open LeanMLIR SLLVM

def fd_f25519_is_zero_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %4 = "llvm.load"(%arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.switch"(%4)[^bb9, ^bb1, ^bb5] <{case_operand_segments = array<i32: 0, 0>, case_values = dense<[0, 2251799813685229]> : vector<2xi64>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i64) -> ()
  ^bb1:  // pred: ^bb0
    %5 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %6 = "llvm.load"(%5) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %7 = "llvm.icmp"(%6, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%7)[^bb2, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb2:  // pred: ^bb1
    %8 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %9 = "llvm.load"(%8) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %10 = "llvm.icmp"(%9, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%10)[^bb3, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb3:  // pred: ^bb2
    %11 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %12 = "llvm.load"(%11) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %13 = "llvm.icmp"(%12, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%13)[^bb4, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb4:  // pred: ^bb3
    %14 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %15 = "llvm.load"(%14) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %16 = "llvm.icmp"(%15, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%16, %1)[^bb10, ^bb9] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i32) -> ()
  ^bb5:  // pred: ^bb0
    %17 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %18 = "llvm.load"(%17) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %19 = "llvm.icmp"(%18, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%19)[^bb6, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb6:  // pred: ^bb5
    %20 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %21 = "llvm.load"(%20) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %22 = "llvm.icmp"(%21, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%22)[^bb7, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb7:  // pred: ^bb6
    %23 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %24 = "llvm.load"(%23) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %25 = "llvm.icmp"(%24, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%25)[^bb8, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb8:  // pred: ^bb7
    %26 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %27 = "llvm.load"(%26) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %28 = "llvm.icmp"(%27, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%28, %1)[^bb10, ^bb9] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i32) -> ()
  ^bb9:  // 9 preds: ^bb0, ^bb1, ^bb2, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8
    "llvm.br"(%3)[^bb10] : (i32) -> ()
  ^bb10(%29: i32):  // 3 preds: ^bb4, ^bb8, ^bb9
    "llvm.return"(%29) : (i32) -> ()
}
]

sllvm_cfg_def fd_f25519_is_zero : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.bitvec 32] :=
  [sllvm_cfg_of| fd_f25519_is_zero_region]

end Firedancer.Ref
