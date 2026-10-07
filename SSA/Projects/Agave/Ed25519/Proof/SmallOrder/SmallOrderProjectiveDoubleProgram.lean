module

public import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionElab

/-! Exact pinned region. Regenerate with MLIR/import_small_order.py.
No instruction rewrite. Direct import is distinct from execution refinement. -/

namespace Agave.Ed25519.Verifier.Execution.SmallOrderProjectiveDouble

open LeanMLIR.RIR
@[expose] public section

structure Primitives where
  /-- Exact external symbol `_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k`. -/
  pow2k : Vals [.ptr, .ptr, .bv 32] → EffectM (Vals [])

def Primitives.resolve (p : Primitives) : String → Option Callee
  | "_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k" => some ⟨[.ptr, .ptr, .bv 32], [], p.pow2k⟩
  | _ => none

execution_def program (p : Primitives) :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 80 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 56 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 72 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 36028797018963664 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 36028797018963952 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 88 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 96 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 104 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 112 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 120 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 136 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 144 : i64}> : () -> i64
    %25 = "llvm.mlir.constant"() <{value = 152 : i64}> : () -> i64
    %26 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %27 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %28 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %29 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %30 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%30) : (!llvm.ptr) -> ()
    "llvm.call"(%30, %arg1, %0) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope, #alias_scope1], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noundef}], callee = @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    "llvm.intr.lifetime.start"(%29) : (!llvm.ptr) -> ()
    %31 = "llvm.getelementptr"(%arg1, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%29, %31, %0) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope2, #alias_scope3], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noundef}], callee = @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    "llvm.intr.lifetime.start"(%28) : (!llvm.ptr) -> ()
    %32 = "llvm.getelementptr"(%arg1, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope4}> : () -> ()
    "llvm.call"(%28, %32, %0) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope5, #alias_scope4], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noundef}], callee = @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    %33 = "llvm.load"(%28) <{alias_scopes = [#alias_scope5], alignment = 8 : i64, noalias_scopes = [#alias_scope4], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %34 = "llvm.shl"(%33, %3) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %35 = "llvm.getelementptr"(%28, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %36 = "llvm.load"(%35) <{alias_scopes = [#alias_scope5], alignment = 8 : i64, noalias_scopes = [#alias_scope4], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %37 = "llvm.shl"(%36, %3) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %38 = "llvm.getelementptr"(%28, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %39 = "llvm.load"(%38) <{alias_scopes = [#alias_scope5], alignment = 8 : i64, noalias_scopes = [#alias_scope4], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %40 = "llvm.shl"(%39, %3) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %41 = "llvm.getelementptr"(%28, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %42 = "llvm.load"(%41) <{alias_scopes = [#alias_scope5], alignment = 8 : i64, noalias_scopes = [#alias_scope4], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %43 = "llvm.shl"(%42, %3) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %44 = "llvm.getelementptr"(%28, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %45 = "llvm.load"(%44) <{alias_scopes = [#alias_scope5], alignment = 8 : i64, noalias_scopes = [#alias_scope4], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %46 = "llvm.shl"(%45, %3) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    "llvm.intr.lifetime.start"(%27) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope6}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope7}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope8}> : () -> ()
    %47 = "llvm.getelementptr"(%arg1, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %48 = "llvm.getelementptr"(%arg1, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %49 = "llvm.load"(%48) <{alias_scopes = [#alias_scope7], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope8], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %50 = "llvm.getelementptr"(%arg1, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %51 = "llvm.getelementptr"(%arg1, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %52 = "llvm.load"(%51) <{alias_scopes = [#alias_scope9, #alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope10, #alias_scope6, #alias_scope7], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %53 = "llvm.add"(%52, %49) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %54 = "llvm.load"(%arg1) <{alias_scopes = [#alias_scope7], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope8], ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %55 = "llvm.load"(%31) <{alias_scopes = [#alias_scope9, #alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope10, #alias_scope6, #alias_scope7], ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %56 = "llvm.add"(%55, %54) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.store"(%56, %27) <{alias_scopes = [#alias_scope6], alignment = 16 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    %57 = "llvm.getelementptr"(%27, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %58 = "llvm.load"(%47) <{alias_scopes = [#alias_scope7], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope8], ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %59 = "llvm.load"(%50) <{alias_scopes = [#alias_scope9, #alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope10, #alias_scope6, #alias_scope7], ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %60 = "llvm.add"(%59, %58) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.store"(%60, %57) <{alias_scopes = [#alias_scope6], alignment = 16 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    %61 = "llvm.getelementptr"(%27, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%53, %61) <{alias_scopes = [#alias_scope6], alignment = 16 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%26) : (!llvm.ptr) -> ()
    "llvm.call"(%26, %27, %0) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope11, #alias_scope12], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noundef}], callee = @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope13}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope14}> : () -> ()
    %62 = "llvm.load"(%29) <{alias_scopes = [#alias_scope13], alignment = 8 : i64, noalias_scopes = [#alias_scope15, #alias_scope14], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %63 = "llvm.getelementptr"(%29, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %64 = "llvm.load"(%63) <{alias_scopes = [#alias_scope13], alignment = 8 : i64, noalias_scopes = [#alias_scope15, #alias_scope14], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %65 = "llvm.getelementptr"(%29, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %66 = "llvm.load"(%65) <{alias_scopes = [#alias_scope13], alignment = 8 : i64, noalias_scopes = [#alias_scope15, #alias_scope14], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %67 = "llvm.getelementptr"(%29, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %68 = "llvm.load"(%67) <{alias_scopes = [#alias_scope13], alignment = 8 : i64, noalias_scopes = [#alias_scope15, #alias_scope14], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %69 = "llvm.getelementptr"(%29, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %70 = "llvm.load"(%69) <{alias_scopes = [#alias_scope13], alignment = 8 : i64, noalias_scopes = [#alias_scope15, #alias_scope14], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %71 = "llvm.load"(%30) <{alias_scopes = [#alias_scope16, #alias_scope14], alignment = 8 : i64, noalias_scopes = [#alias_scope17, #alias_scope15, #alias_scope13], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %72 = "llvm.add"(%71, %62) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %73 = "llvm.getelementptr"(%30, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %74 = "llvm.load"(%73) <{alias_scopes = [#alias_scope16, #alias_scope14], alignment = 8 : i64, noalias_scopes = [#alias_scope17, #alias_scope15, #alias_scope13], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %75 = "llvm.add"(%74, %64) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %76 = "llvm.getelementptr"(%30, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %77 = "llvm.load"(%76) <{alias_scopes = [#alias_scope16, #alias_scope14], alignment = 8 : i64, noalias_scopes = [#alias_scope17, #alias_scope15, #alias_scope13], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %78 = "llvm.add"(%77, %66) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %79 = "llvm.getelementptr"(%30, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %80 = "llvm.load"(%79) <{alias_scopes = [#alias_scope16, #alias_scope14], alignment = 8 : i64, noalias_scopes = [#alias_scope17, #alias_scope15, #alias_scope13], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %81 = "llvm.add"(%80, %68) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %82 = "llvm.getelementptr"(%30, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %83 = "llvm.load"(%82) <{alias_scopes = [#alias_scope16, #alias_scope14], alignment = 8 : i64, noalias_scopes = [#alias_scope17, #alias_scope15, #alias_scope13], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %84 = "llvm.add"(%83, %70) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %85 = "llvm.add"(%62, %10) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %86 = "llvm.sub"(%85, %71) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %87 = "llvm.add"(%64, %11) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %88 = "llvm.sub"(%87, %74) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %89 = "llvm.add"(%66, %11) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %90 = "llvm.sub"(%89, %77) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %91 = "llvm.add"(%68, %11) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %92 = "llvm.sub"(%91, %80) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %93 = "llvm.add"(%70, %11) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %94 = "llvm.sub"(%93, %83) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %95 = "llvm.lshr"(%86, %12) : (i64, i64) -> i64
    %96 = "llvm.lshr"(%88, %12) : (i64, i64) -> i64
    %97 = "llvm.lshr"(%90, %12) : (i64, i64) -> i64
    %98 = "llvm.lshr"(%92, %12) : (i64, i64) -> i64
    %99 = "llvm.lshr"(%94, %12) : (i64, i64) -> i64
    %100 = "llvm.and"(%86, %13) : (i64, i64) -> i64
    %101 = "llvm.and"(%88, %13) : (i64, i64) -> i64
    %102 = "llvm.and"(%90, %13) : (i64, i64) -> i64
    %103 = "llvm.and"(%92, %13) : (i64, i64) -> i64
    %104 = "llvm.and"(%94, %13) : (i64, i64) -> i64
    %105 = "llvm.mul"(%99, %14) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %106 = "llvm.add"(%105, %100) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %107 = "llvm.add"(%101, %95) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %108 = "llvm.add"(%102, %96) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %109 = "llvm.add"(%103, %97) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %110 = "llvm.add"(%104, %98) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %111 = "llvm.load"(%26) <{alias_scopes = [#alias_scope18], alignment = 8 : i64, noalias_scopes = [#alias_scope19, #alias_scope20], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %112 = "llvm.sub"(%111, %72) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %113 = "llvm.add"(%112, %10) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %114 = "llvm.getelementptr"(%26, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %115 = "llvm.load"(%114) <{alias_scopes = [#alias_scope18], alignment = 8 : i64, noalias_scopes = [#alias_scope19, #alias_scope20], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %116 = "llvm.sub"(%115, %75) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %117 = "llvm.add"(%116, %11) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %118 = "llvm.getelementptr"(%26, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %119 = "llvm.load"(%118) <{alias_scopes = [#alias_scope18], alignment = 8 : i64, noalias_scopes = [#alias_scope19, #alias_scope20], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %120 = "llvm.sub"(%119, %78) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %121 = "llvm.add"(%120, %11) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %122 = "llvm.getelementptr"(%26, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %123 = "llvm.load"(%122) <{alias_scopes = [#alias_scope18], alignment = 8 : i64, noalias_scopes = [#alias_scope19, #alias_scope20], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %124 = "llvm.sub"(%123, %81) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %125 = "llvm.add"(%124, %11) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %126 = "llvm.getelementptr"(%26, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %127 = "llvm.load"(%126) <{alias_scopes = [#alias_scope18], alignment = 8 : i64, noalias_scopes = [#alias_scope19, #alias_scope20], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %128 = "llvm.sub"(%127, %84) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %129 = "llvm.add"(%128, %11) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %130 = "llvm.lshr"(%113, %12) : (i64, i64) -> i64
    %131 = "llvm.lshr"(%117, %12) : (i64, i64) -> i64
    %132 = "llvm.lshr"(%121, %12) : (i64, i64) -> i64
    %133 = "llvm.lshr"(%125, %12) : (i64, i64) -> i64
    %134 = "llvm.lshr"(%129, %12) : (i64, i64) -> i64
    %135 = "llvm.and"(%113, %13) : (i64, i64) -> i64
    %136 = "llvm.and"(%117, %13) : (i64, i64) -> i64
    %137 = "llvm.and"(%121, %13) : (i64, i64) -> i64
    %138 = "llvm.and"(%125, %13) : (i64, i64) -> i64
    %139 = "llvm.and"(%129, %13) : (i64, i64) -> i64
    %140 = "llvm.mul"(%134, %14) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %141 = "llvm.add"(%140, %135) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %142 = "llvm.add"(%136, %130) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %143 = "llvm.add"(%137, %131) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %144 = "llvm.add"(%138, %132) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %145 = "llvm.add"(%139, %133) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %146 = "llvm.add"(%34, %10) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %147 = "llvm.sub"(%146, %106) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %148 = "llvm.add"(%37, %11) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %149 = "llvm.sub"(%148, %107) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %150 = "llvm.add"(%40, %11) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %151 = "llvm.sub"(%150, %108) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %152 = "llvm.add"(%43, %11) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %153 = "llvm.sub"(%152, %109) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %154 = "llvm.add"(%46, %11) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %155 = "llvm.sub"(%154, %110) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %156 = "llvm.lshr"(%147, %12) : (i64, i64) -> i64
    %157 = "llvm.lshr"(%149, %12) : (i64, i64) -> i64
    %158 = "llvm.lshr"(%151, %12) : (i64, i64) -> i64
    %159 = "llvm.lshr"(%153, %12) : (i64, i64) -> i64
    %160 = "llvm.lshr"(%155, %12) : (i64, i64) -> i64
    %161 = "llvm.and"(%147, %13) : (i64, i64) -> i64
    %162 = "llvm.and"(%149, %13) : (i64, i64) -> i64
    %163 = "llvm.and"(%151, %13) : (i64, i64) -> i64
    %164 = "llvm.and"(%153, %13) : (i64, i64) -> i64
    %165 = "llvm.and"(%155, %13) : (i64, i64) -> i64
    %166 = "llvm.mul"(%160, %14) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %167 = "llvm.add"(%166, %161) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %168 = "llvm.add"(%156, %162) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %169 = "llvm.add"(%163, %157) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %170 = "llvm.add"(%164, %158) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %171 = "llvm.add"(%165, %159) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "llvm.store"(%141, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %172 = "llvm.getelementptr"(%arg0, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%142, %172) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %173 = "llvm.getelementptr"(%arg0, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%143, %173) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %174 = "llvm.getelementptr"(%arg0, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%144, %174) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %175 = "llvm.getelementptr"(%arg0, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%145, %175) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %176 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%72, %176) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %177 = "llvm.getelementptr"(%arg0, %15) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%75, %177) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %178 = "llvm.getelementptr"(%arg0, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%78, %178) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %179 = "llvm.getelementptr"(%arg0, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%81, %179) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %180 = "llvm.getelementptr"(%arg0, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%84, %180) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %181 = "llvm.getelementptr"(%arg0, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%106, %181) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %182 = "llvm.getelementptr"(%arg0, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%107, %182) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %183 = "llvm.getelementptr"(%arg0, %18) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%108, %183) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %184 = "llvm.getelementptr"(%arg0, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%109, %184) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %185 = "llvm.getelementptr"(%arg0, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%110, %185) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %186 = "llvm.getelementptr"(%arg0, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%167, %186) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %187 = "llvm.getelementptr"(%arg0, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%168, %187) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %188 = "llvm.getelementptr"(%arg0, %23) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%169, %188) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %189 = "llvm.getelementptr"(%arg0, %24) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%170, %189) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %190 = "llvm.getelementptr"(%arg0, %25) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%171, %190) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%26) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%27) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%28) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%29) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%30) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
with @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k := p.pow2k

theorem block_count (p : Primitives) : (program p).n = 1 := rfl

end
end Agave.Ed25519.Verifier.Execution.SmallOrderProjectiveDouble
