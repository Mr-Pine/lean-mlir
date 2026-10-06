module

public import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionElab

/-! Exact pinned MLIR region. Regenerate with MLIR/import_decompress.py.
All instructions and attributes are retained. Successful import is not an execution proof. -/

namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode

open LeanMLIR.RIR
@[expose] public section

structure Primitives where
  /-- Exact external symbol `_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k`. -/
  pow2k : Vals [.ptr, .ptr, .bv 32] → EffectM (Vals [])
  /-- Exact external symbol `_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul`. -/
  mul : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])
  /-- Exact external symbol `_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement5112sqrt_ratio_i`. -/
  sqrtRatio : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])
  /-- Exact external symbol `_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519`. -/
  blackBoxByte : Vals [.bv 8] → EffectM (Vals [.bv 8])

structure Globals where
  /-- Address of `alloc_781589f30b7aca1e8db8c1d787298044`; its exact initializer is a separate memory obligation. -/
  address0 : Pointer

execution_def program (p : Primitives) (g : Globals) :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 12 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = dense<[36028797018963663, 36028797018963952]> : vector<2xi64>}> : () -> vector<2xi64>
    %12 = "llvm.mlir.constant"() <{value = dense<36028797018963952> : vector<2xi64>}> : () -> vector<2xi64>
    %13 = "llvm.mlir.constant"() <{value = dense<51> : vector<2xi64>}> : () -> vector<2xi64>
    %14 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = dense<2251799813685247> : vector<2xi64>}> : () -> vector<2xi64>
    %16 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %17 = "llvm.mlir.addressof"() <{global_name = @alloc_781589f30b7aca1e8db8c1d787298044}> : () -> !llvm.ptr
    %18 = "llvm.mlir.constant"() <{value = dense<[1, 0]> : vector<2xi64>}> : () -> vector<2xi64>
    %19 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %21 = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 7 : i8}> : () -> i8
    %23 = "llvm.mlir.constant"() <{value = 2251799813684944 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = dense<[36028797018963664, 36028797018963952]> : vector<2xi64>}> : () -> vector<2xi64>
    %25 = "llvm.mlir.poison"() : () -> vector<2xi64>
    %26 = "llvm.mlir.constant"() <{value = 120 : i64}> : () -> i64
    %27 = "llvm.mlir.constant"() <{value = 80 : i64}> : () -> i64
    %28 = "llvm.mlir.constant"() <{value = 88 : i64}> : () -> i64
    %29 = "llvm.mlir.constant"() <{value = 160 : i64}> : () -> i64
    %30 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<48 x i8>}> : (i32) -> !llvm.ptr
    %31 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %32 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %33 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %34 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %35 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %36 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %37 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<80 x i8>}> : (i32) -> !llvm.ptr
    %38 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %39 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%37) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope}> : () -> ()
    "llvm.intr.lifetime.start"(%35) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope1}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope2}> : () -> ()
    %40 = "llvm.load"(%arg1) <{alias_scopes = [#alias_scope3, #alias_scope2, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope4], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %41 = "llvm.and"(%40, %1) : (i64, i64) -> i64
    %42 = "llvm.getelementptr"(%arg1, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %43 = "llvm.load"(%42) <{alias_scopes = [#alias_scope5, #alias_scope2, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope4], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %44 = "llvm.lshr"(%43, %3) : (i64, i64) -> i64
    %45 = "llvm.and"(%44, %1) : (i64, i64) -> i64
    %46 = "llvm.getelementptr"(%arg1, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %47 = "llvm.load"(%46) <{alias_scopes = [#alias_scope6, #alias_scope2, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope4], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %48 = "llvm.lshr"(%47, %2) : (i64, i64) -> i64
    %49 = "llvm.and"(%48, %1) : (i64, i64) -> i64
    %50 = "llvm.getelementptr"(%arg1, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %51 = "llvm.load"(%50) <{alias_scopes = [#alias_scope7, #alias_scope2, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope4], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %52 = "llvm.lshr"(%51, %6) : (i64, i64) -> i64
    %53 = "llvm.and"(%52, %1) : (i64, i64) -> i64
    %54 = "llvm.getelementptr"(%arg1, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %55 = "llvm.load"(%54) <{alias_scopes = [#alias_scope8, #alias_scope2, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope4], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %56 = "llvm.lshr"(%55, %4) : (i64, i64) -> i64
    %57 = "llvm.and"(%56, %1) : (i64, i64) -> i64
    "llvm.store"(%41, %35) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %58 = "llvm.getelementptr"(%35, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%45, %58) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %59 = "llvm.getelementptr"(%35, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%49, %59) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %60 = "llvm.getelementptr"(%35, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%53, %60) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %61 = "llvm.getelementptr"(%35, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%57, %61) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%34) : (!llvm.ptr) -> ()
    "llvm.call"(%34, %35, %0) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope9, #alias_scope10], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noundef}], callee = @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope4, #alias_scope], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    "llvm.intr.lifetime.start"(%33) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope11}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope12}> : () -> ()
    %62 = "llvm.getelementptr"(%34, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %63 = "llvm.getelementptr"(%34, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %64 = "llvm.getelementptr"(%33, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %65 = "llvm.load"(%34) <{alias_scopes = [#alias_scope12], alignment = 16 : i64, noalias_scopes = [#alias_scope11, #alias_scope13, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %66 = "llvm.load"(%62) <{alias_scopes = [#alias_scope12], alignment = 8 : i64, noalias_scopes = [#alias_scope11, #alias_scope13, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %67 = "llvm.add"(%65, %11) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %68 = "llvm.add"(%66, %12) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %69 = "llvm.lshr"(%67, %13) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %70 = "llvm.extractelement"(%67, %14) : (vector<2xi64>, i64) -> i64
    %71 = "llvm.and"(%70, %1) : (i64, i64) -> i64
    %72 = "llvm.and"(%68, %15) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %73 = "llvm.add"(%72, %69) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.store"(%73, %64) <{alias_scopes = [#alias_scope11], alignment = 8 : i64, noalias_scopes = [#alias_scope12, #alias_scope13, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    %74 = "llvm.getelementptr"(%33, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %75 = "llvm.load"(%63) <{alias_scopes = [#alias_scope12], alignment = 8 : i64, noalias_scopes = [#alias_scope11, #alias_scope13, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %76 = "llvm.add"(%75, %12) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %77 = "llvm.extractelement"(%76, %6) : (vector<2xi64>, i64) -> i64
    %78 = "llvm.lshr"(%77, %16) : (i64, i64) -> i64
    %79 = "llvm.and"(%76, %15) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %80 = "llvm.mul"(%78, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %81 = "llvm.shufflevector"(%68, %76) <{mask = array<i32: 1, 2>}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %82 = "llvm.lshr"(%81, %13) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %83 = "llvm.add"(%80, %71) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %84 = "llvm.add"(%79, %82) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.store"(%83, %33) <{alias_scopes = [#alias_scope11], alignment = 8 : i64, noalias_scopes = [#alias_scope12, #alias_scope13, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%84, %74) <{alias_scopes = [#alias_scope11], alignment = 8 : i64, noalias_scopes = [#alias_scope12, #alias_scope13, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%32) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%31) : (!llvm.ptr) -> ()
    "llvm.call"(%31, %34, %17) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope4, #alias_scope], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope14}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope15}> : () -> ()
    %85 = "llvm.getelementptr"(%31, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %86 = "llvm.getelementptr"(%31, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %87 = "llvm.load"(%86) <{alias_scopes = [#alias_scope15], alignment = 16 : i64, noalias_scopes = [#alias_scope14, #alias_scope16, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %88 = "llvm.load"(%31) <{alias_scopes = [#alias_scope15], alignment = 16 : i64, noalias_scopes = [#alias_scope14, #alias_scope16, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %89 = "llvm.add"(%88, %18) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.store"(%89, %32) <{alias_scopes = [#alias_scope14], alignment = 16 : i64, noalias_scopes = [#alias_scope15, #alias_scope16, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    %90 = "llvm.getelementptr"(%32, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %91 = "llvm.load"(%85) <{alias_scopes = [#alias_scope15], alignment = 16 : i64, noalias_scopes = [#alias_scope14, #alias_scope16, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    "llvm.store"(%91, %90) <{alias_scopes = [#alias_scope14], alignment = 16 : i64, noalias_scopes = [#alias_scope15, #alias_scope16, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    %92 = "llvm.getelementptr"(%32, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%87, %92) <{alias_scopes = [#alias_scope14], alignment = 16 : i64, noalias_scopes = [#alias_scope15, #alias_scope16, #alias_scope4, #alias_scope], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%31) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%30) : (!llvm.ptr) -> ()
    "llvm.call"(%30, %33, %32) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 48 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.noundef, llvm.readonly}], callee = @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement5112sqrt_ratio_i, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope4, #alias_scope], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    %93 = "llvm.load"(%30) <{alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %94 = "llvm.getelementptr"(%30, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%37, %94, %19) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%30) : (!llvm.ptr) -> ()
    %95 = "llvm.getelementptr"(%37, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%95, %35, %19) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%32) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%33) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%34) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%35) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%39) : (!llvm.ptr) -> ()
    "llvm.intr.memcpy"(%39, %37, %19) <{arg_attrs = [{llvm.align = 16 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.start"(%38) : (!llvm.ptr) -> ()
    "llvm.intr.memcpy"(%38, %95, %19) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%37) : (!llvm.ptr) -> ()
    %96 = "llvm.icmp"(%93, %20) <{predicate = 0 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%96, %14)[^bb2, ^bb1] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i64) -> ()
  ^bb1:  // pred: ^bb0
    "llvm.intr.lifetime.start"(%36) : (!llvm.ptr) -> ()
    %97 = "llvm.getelementptr"(%arg1, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %98 = "llvm.load"(%97) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope17}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope18}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope19}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope20}> : () -> ()
    %99 = "llvm.lshr"(%98, %22) : (i8, i8) -> i8
    %100 = "llvm.call"(%99) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %101 = "llvm.getelementptr"(%39, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %102 = "llvm.getelementptr"(%39, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %103 = "llvm.zext"(%100) : (i8) -> i64
    %104 = "llvm.sub"(%14, %103) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %105 = "llvm.load"(%39) <{alias_scopes = [#alias_scope21, #alias_scope18], alignment = 16 : i64, noalias_scopes = [#alias_scope22, #alias_scope17, #alias_scope19, #alias_scope20], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %106 = "llvm.load"(%39) <{alias_scopes = [#alias_scope21, #alias_scope18], alignment = 16 : i64, noalias_scopes = [#alias_scope22, #alias_scope17, #alias_scope19, #alias_scope20], ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %107 = "llvm.load"(%101) <{alias_scopes = [#alias_scope21, #alias_scope18], alignment = 8 : i64, noalias_scopes = [#alias_scope22, #alias_scope17, #alias_scope19, #alias_scope20], ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %108 = "llvm.sub"(%23, %105) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %109 = "llvm.sub"(%24, %106) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %110 = "llvm.sub"(%12, %107) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %111 = "llvm.lshr"(%109, %13) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %112 = "llvm.and"(%108, %1) : (i64, i64) -> i64
    %113 = "llvm.and"(%110, %15) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %114 = "llvm.add"(%113, %111) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %115 = "llvm.xor"(%114, %107) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %116 = "llvm.insertelement"(%25, %104, %14) : (vector<2xi64>, i64, i64) -> vector<2xi64>
    %117 = "llvm.shufflevector"(%116, %25) <{mask = array<i32: 0, 0>}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %118 = "llvm.and"(%115, %117) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %119 = "llvm.xor"(%118, %107) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.store"(%119, %101) <{alias_scopes = [#alias_scope23, #alias_scope18], alignment = 8 : i64, noalias_scopes = [#alias_scope24, #alias_scope17, #alias_scope19, #alias_scope20], ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    %120 = "llvm.load"(%102) <{alias_scopes = [#alias_scope21, #alias_scope18], alignment = 8 : i64, noalias_scopes = [#alias_scope22, #alias_scope17, #alias_scope19, #alias_scope20], ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %121 = "llvm.sub"(%12, %120) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %122 = "llvm.extractelement"(%121, %6) : (vector<2xi64>, i64) -> i64
    %123 = "llvm.lshr"(%122, %16) : (i64, i64) -> i64
    %124 = "llvm.and"(%121, %15) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %125 = "llvm.mul"(%123, %5) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %126 = "llvm.shufflevector"(%110, %121) <{mask = array<i32: 1, 2>}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %127 = "llvm.lshr"(%126, %13) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %128 = "llvm.add"(%125, %112) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %129 = "llvm.add"(%124, %127) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %130 = "llvm.xor"(%128, %105) : (i64, i64) -> i64
    %131 = "llvm.and"(%130, %104) : (i64, i64) -> i64
    %132 = "llvm.xor"(%131, %105) : (i64, i64) -> i64
    "llvm.store"(%132, %39) <{alias_scopes = [#alias_scope23, #alias_scope18], alignment = 16 : i64, noalias_scopes = [#alias_scope24, #alias_scope17, #alias_scope19, #alias_scope20], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %133 = "llvm.xor"(%129, %120) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %134 = "llvm.and"(%133, %117) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %135 = "llvm.xor"(%134, %120) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.store"(%135, %102) <{alias_scopes = [#alias_scope23, #alias_scope18], alignment = 8 : i64, noalias_scopes = [#alias_scope24, #alias_scope17, #alias_scope19, #alias_scope20], ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%36, %39, %19) <{alias_scopes = [#alias_scope17, #alias_scope18], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 16 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope19, #alias_scope20]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %136 = "llvm.getelementptr"(%36, %26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%136, %39, %38) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope17, #alias_scope18, #alias_scope19], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope20], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    %137 = "llvm.getelementptr"(%36, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%137, %38, %19) <{alias_scopes = [#alias_scope17, #alias_scope19], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef, llvm.readonly}, {}], isVolatile = false, noalias_scopes = [#alias_scope18, #alias_scope20]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %138 = "llvm.getelementptr"(%36, %27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%6, %138) <{alias_scopes = [#alias_scope17, #alias_scope20], alignment = 8 : i64, noalias_scopes = [#alias_scope18, #alias_scope19], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %139 = "llvm.getelementptr"(%36, %28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memset"(%139, %20, %10) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    %140 = "llvm.getelementptr"(%arg0, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%140, %36, %29) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%36) : (!llvm.ptr) -> ()
    "llvm.br"(%6)[^bb2] : (i64) -> ()
  ^bb2(%141: i64):  // 2 preds: ^bb0, ^bb1
    "llvm.store"(%141, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%38) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%39) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
with @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k := (p).pow2k,
  @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul := (p).mul,
  @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement5112sqrt_ratio_i := (p).sqrtRatio,
  @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519 := (p).blackBoxByte
globals @alloc_781589f30b7aca1e8db8c1d787298044 := (g).address0

theorem block_count (p : Primitives) (g : Globals) : (program p g).n = 3 := rfl

end
end Agave.Ed25519.Encoding.Decompress.Execution.Decode
