module

public import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionElab

/-! Exact pinned MLIR region. Regenerate with MLIR/import_compress.py.
All instructions and attributes are retained. Successful import is not an execution proof. -/

namespace Agave.Ed25519.Encoding.Compress.Execution

open LeanMLIR.RIR
@[expose] public section

structure Primitives where
  /-- Exact external symbol `_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement518pow22501`. -/
  pow22501 : Vals [.ptr, .ptr] → EffectM (Vals [])
  /-- Exact external symbol `_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k`. -/
  pow2k : Vals [.ptr, .ptr, .bv 32] → EffectM (Vals [])
  /-- Exact external symbol `_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul`. -/
  mul : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])
  /-- Exact external symbol `_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519`. -/
  blackBoxByte : Vals [.bv 8] → EffectM (Vals [.bv 8])

execution_def program (p : Primitives) :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 80 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %4 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 56 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 72 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 13 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 21 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 29 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 37 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 45 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %25 = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
    %26 = "llvm.mlir.constant"() <{value = 18 : i64}> : () -> i64
    %27 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %28 = "llvm.mlir.constant"() <{value = 34 : i64}> : () -> i64
    %29 = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %30 = "llvm.mlir.constant"() <{value = 50 : i64}> : () -> i64
    %31 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %32 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %33 = "llvm.mlir.constant"() <{value = 23 : i64}> : () -> i64
    %34 = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %35 = "llvm.mlir.constant"() <{value = 39 : i64}> : () -> i64
    %36 = "llvm.mlir.constant"() <{value = 47 : i64}> : () -> i64
    %37 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %38 = "llvm.mlir.constant"() <{value = 12 : i64}> : () -> i64
    %39 = "llvm.mlir.constant"() <{value = 20 : i64}> : () -> i64
    %40 = "llvm.mlir.constant"() <{value = 28 : i64}> : () -> i64
    %41 = "llvm.mlir.constant"() <{value = 36 : i64}> : () -> i64
    %42 = "llvm.mlir.constant"() <{value = 44 : i64}> : () -> i64
    %43 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %44 = "llvm.mlir.constant"() <{value = 7 : i8}> : () -> i8
    %45 = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    %46 = "llvm.mlir.constant"() <{value = 11 : i64}> : () -> i64
    %47 = "llvm.mlir.constant"() <{value = 14 : i64}> : () -> i64
    %48 = "llvm.mlir.constant"() <{value = 17 : i64}> : () -> i64
    %49 = "llvm.mlir.constant"() <{value = 22 : i64}> : () -> i64
    %50 = "llvm.mlir.constant"() <{value = 25 : i64}> : () -> i64
    %51 = "llvm.mlir.constant"() <{value = 27 : i64}> : () -> i64
    %52 = "llvm.mlir.constant"() <{value = 30 : i64}> : () -> i64
    %53 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %54 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<80 x i8>}> : (i32) -> !llvm.ptr
    %55 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %56 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %57 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %58 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<80 x i8>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%58) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%57) : (!llvm.ptr) -> ()
    %59 = "llvm.getelementptr"(%arg1, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%54) : (!llvm.ptr) -> ()
    "llvm.call"(%54, %59) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 80 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement518pow22501, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope, #alias_scope1], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%56) : (!llvm.ptr) -> ()
    "llvm.intr.memcpy"(%56, %54, %2) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope, #alias_scope2, #alias_scope1, #alias_scope3]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.start"(%55) : (!llvm.ptr) -> ()
    %60 = "llvm.getelementptr"(%54, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%55, %60, %2) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope, #alias_scope2, #alias_scope1, #alias_scope3]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%54) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%53) : (!llvm.ptr) -> ()
    "llvm.call"(%53, %56, %3) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noundef}], callee = @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope, #alias_scope2, #alias_scope1, #alias_scope3], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    "llvm.call"(%57, %53, %55) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope2, #alias_scope1, #alias_scope3], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%53) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%55) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%56) : (!llvm.ptr) -> ()
    "llvm.call"(%58, %arg1, %57) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 80 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    %61 = "llvm.getelementptr"(%arg1, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %62 = "llvm.getelementptr"(%58, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%62, %61, %57) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%57) : (!llvm.ptr) -> ()
    %63 = "llvm.load"(%62) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %64 = "llvm.getelementptr"(%58, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %65 = "llvm.load"(%64) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %66 = "llvm.getelementptr"(%58, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %67 = "llvm.load"(%66) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %68 = "llvm.getelementptr"(%58, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %69 = "llvm.load"(%68) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %70 = "llvm.getelementptr"(%58, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %71 = "llvm.load"(%70) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %72 = "llvm.lshr"(%63, %8) : (i64, i64) -> i64
    %73 = "llvm.lshr"(%65, %8) : (i64, i64) -> i64
    %74 = "llvm.lshr"(%67, %8) : (i64, i64) -> i64
    %75 = "llvm.lshr"(%69, %8) : (i64, i64) -> i64
    %76 = "llvm.lshr"(%71, %8) : (i64, i64) -> i64
    %77 = "llvm.and"(%63, %9) : (i64, i64) -> i64
    %78 = "llvm.and"(%65, %9) : (i64, i64) -> i64
    %79 = "llvm.and"(%67, %9) : (i64, i64) -> i64
    %80 = "llvm.and"(%69, %9) : (i64, i64) -> i64
    %81 = "llvm.and"(%71, %9) : (i64, i64) -> i64
    %82 = "llvm.mul"(%76, %10) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %83 = "llvm.add"(%82, %77) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %84 = "llvm.add"(%78, %72) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %85 = "llvm.add"(%79, %73) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %86 = "llvm.add"(%80, %74) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %87 = "llvm.add"(%81, %75) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %88 = "llvm.add"(%83, %10) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %89 = "llvm.lshr"(%88, %8) : (i64, i64) -> i64
    %90 = "llvm.add"(%89, %84) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %91 = "llvm.lshr"(%90, %8) : (i64, i64) -> i64
    %92 = "llvm.add"(%91, %85) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %93 = "llvm.lshr"(%92, %8) : (i64, i64) -> i64
    %94 = "llvm.add"(%93, %86) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %95 = "llvm.lshr"(%94, %8) : (i64, i64) -> i64
    %96 = "llvm.add"(%95, %87) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %97 = "llvm.lshr"(%96, %8) : (i64, i64) -> i64
    %98 = "llvm.mul"(%97, %10) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %99 = "llvm.add"(%98, %83) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %100 = "llvm.lshr"(%99, %8) : (i64, i64) -> i64
    %101 = "llvm.add"(%100, %84) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %102 = "llvm.lshr"(%101, %8) : (i64, i64) -> i64
    %103 = "llvm.add"(%102, %85) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %104 = "llvm.and"(%101, %9) : (i64, i64) -> i64
    %105 = "llvm.lshr"(%103, %8) : (i64, i64) -> i64
    %106 = "llvm.add"(%105, %86) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %107 = "llvm.and"(%103, %9) : (i64, i64) -> i64
    %108 = "llvm.lshr"(%106, %8) : (i64, i64) -> i64
    %109 = "llvm.add"(%108, %87) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %110 = "llvm.and"(%106, %9) : (i64, i64) -> i64
    %111 = "llvm.and"(%109, %9) : (i64, i64) -> i64
    %112 = "llvm.trunc"(%99) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %113 = "llvm.lshr"(%99, %11) : (i64, i64) -> i64
    %114 = "llvm.trunc"(%113) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %115 = "llvm.lshr"(%99, %12) : (i64, i64) -> i64
    %116 = "llvm.trunc"(%115) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %117 = "llvm.lshr"(%99, %13) : (i64, i64) -> i64
    %118 = "llvm.trunc"(%117) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %119 = "llvm.lshr"(%99, %14) : (i64, i64) -> i64
    %120 = "llvm.trunc"(%119) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %121 = "llvm.lshr"(%99, %2) : (i64, i64) -> i64
    %122 = "llvm.trunc"(%121) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %123 = "llvm.lshr"(%99, %4) : (i64, i64) -> i64
    %124 = "llvm.and"(%123, %15) : (i64, i64) -> i64
    %125 = "llvm.shl"(%104, %16) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %126 = "llvm.or"(%125, %124) <{isDisjoint}> : (i64, i64) -> i64
    %127 = "llvm.trunc"(%126) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %128 = "llvm.lshr"(%101, %17) : (i64, i64) -> i64
    %129 = "llvm.trunc"(%128) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %130 = "llvm.lshr"(%101, %18) : (i64, i64) -> i64
    %131 = "llvm.trunc"(%130) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %132 = "llvm.lshr"(%101, %19) : (i64, i64) -> i64
    %133 = "llvm.trunc"(%132) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %134 = "llvm.lshr"(%101, %20) : (i64, i64) -> i64
    %135 = "llvm.trunc"(%134) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %136 = "llvm.lshr"(%101, %21) : (i64, i64) -> i64
    %137 = "llvm.trunc"(%136) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %138 = "llvm.lshr"(%104, %22) : (i64, i64) -> i64
    %139 = "llvm.shl"(%107, %23) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %140 = "llvm.or"(%139, %138) <{isDisjoint}> : (i64, i64) -> i64
    %141 = "llvm.trunc"(%140) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %142 = "llvm.lshr"(%103, %24) : (i64, i64) -> i64
    %143 = "llvm.trunc"(%142) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %144 = "llvm.lshr"(%103, %25) : (i64, i64) -> i64
    %145 = "llvm.trunc"(%144) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %146 = "llvm.lshr"(%103, %26) : (i64, i64) -> i64
    %147 = "llvm.trunc"(%146) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %148 = "llvm.lshr"(%103, %27) : (i64, i64) -> i64
    %149 = "llvm.trunc"(%148) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %150 = "llvm.lshr"(%103, %28) : (i64, i64) -> i64
    %151 = "llvm.trunc"(%150) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %152 = "llvm.lshr"(%103, %29) : (i64, i64) -> i64
    %153 = "llvm.trunc"(%152) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %154 = "llvm.lshr"(%107, %30) : (i64, i64) -> i64
    %155 = "llvm.shl"(%110, %31) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %156 = "llvm.or"(%155, %154) <{isDisjoint}> : (i64, i64) -> i64
    %157 = "llvm.trunc"(%156) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %158 = "llvm.lshr"(%106, %15) : (i64, i64) -> i64
    %159 = "llvm.trunc"(%158) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %160 = "llvm.lshr"(%106, %32) : (i64, i64) -> i64
    %161 = "llvm.trunc"(%160) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %162 = "llvm.lshr"(%106, %33) : (i64, i64) -> i64
    %163 = "llvm.trunc"(%162) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %164 = "llvm.lshr"(%106, %34) : (i64, i64) -> i64
    %165 = "llvm.trunc"(%164) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %166 = "llvm.lshr"(%106, %35) : (i64, i64) -> i64
    %167 = "llvm.trunc"(%166) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %168 = "llvm.lshr"(%110, %36) : (i64, i64) -> i64
    %169 = "llvm.shl"(%111, %37) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %170 = "llvm.or"(%169, %168) <{isDisjoint}> : (i64, i64) -> i64
    %171 = "llvm.trunc"(%170) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %172 = "llvm.lshr"(%109, %37) : (i64, i64) -> i64
    %173 = "llvm.trunc"(%172) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %174 = "llvm.lshr"(%109, %38) : (i64, i64) -> i64
    %175 = "llvm.trunc"(%174) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %176 = "llvm.lshr"(%109, %39) : (i64, i64) -> i64
    %177 = "llvm.trunc"(%176) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %178 = "llvm.lshr"(%109, %40) : (i64, i64) -> i64
    %179 = "llvm.trunc"(%178) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %180 = "llvm.lshr"(%109, %41) : (i64, i64) -> i64
    %181 = "llvm.trunc"(%180) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %182 = "llvm.lshr"(%111, %42) : (i64, i64) -> i64
    %183 = "llvm.trunc"(%182) <{overflowFlags = 3 : i32}> : (i64) -> i8
    %184 = "llvm.load"(%58) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %185 = "llvm.getelementptr"(%58, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %186 = "llvm.load"(%185) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %187 = "llvm.getelementptr"(%58, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %188 = "llvm.load"(%187) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %189 = "llvm.getelementptr"(%58, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %190 = "llvm.load"(%189) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %191 = "llvm.getelementptr"(%58, %14) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %192 = "llvm.load"(%191) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %193 = "llvm.lshr"(%184, %8) : (i64, i64) -> i64
    %194 = "llvm.lshr"(%186, %8) : (i64, i64) -> i64
    %195 = "llvm.lshr"(%188, %8) : (i64, i64) -> i64
    %196 = "llvm.lshr"(%190, %8) : (i64, i64) -> i64
    %197 = "llvm.lshr"(%192, %8) : (i64, i64) -> i64
    %198 = "llvm.and"(%184, %9) : (i64, i64) -> i64
    %199 = "llvm.and"(%186, %9) : (i64, i64) -> i64
    %200 = "llvm.and"(%188, %9) : (i64, i64) -> i64
    %201 = "llvm.and"(%190, %9) : (i64, i64) -> i64
    %202 = "llvm.and"(%192, %9) : (i64, i64) -> i64
    %203 = "llvm.mul"(%197, %10) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %204 = "llvm.add"(%203, %198) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %205 = "llvm.add"(%199, %193) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %206 = "llvm.add"(%200, %194) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %207 = "llvm.add"(%201, %195) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %208 = "llvm.add"(%202, %196) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %209 = "llvm.add"(%204, %10) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %210 = "llvm.lshr"(%209, %8) : (i64, i64) -> i64
    %211 = "llvm.add"(%205, %210) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %212 = "llvm.lshr"(%211, %8) : (i64, i64) -> i64
    %213 = "llvm.add"(%206, %212) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %214 = "llvm.lshr"(%213, %8) : (i64, i64) -> i64
    %215 = "llvm.add"(%207, %214) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %216 = "llvm.lshr"(%215, %8) : (i64, i64) -> i64
    %217 = "llvm.add"(%208, %216) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %218 = "llvm.lshr"(%217, %8) : (i64, i64) -> i64
    %219 = "llvm.add"(%218, %204) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %220 = "llvm.trunc"(%219) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %221 = "llvm.and"(%220, %43) : (i8, i8) -> i8
    %222 = "llvm.call"(%221) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %223 = "llvm.shl"(%222, %44) <{overflowFlags = 0 : i32}> : (i8, i8) -> i8
    %224 = "llvm.or"(%223, %183) <{isDisjoint}> : (i8, i8) -> i8
    "llvm.store"(%112, %arg0) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %225 = "llvm.getelementptr"(%arg0, %31) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%114, %225) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %226 = "llvm.getelementptr"(%arg0, %24) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%116, %226) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %227 = "llvm.getelementptr"(%arg0, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%118, %227) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %228 = "llvm.getelementptr"(%arg0, %37) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%120, %228) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %229 = "llvm.getelementptr"(%arg0, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%122, %229) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %230 = "llvm.getelementptr"(%arg0, %23) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%127, %230) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %231 = "llvm.getelementptr"(%arg0, %15) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%129, %231) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %232 = "llvm.getelementptr"(%arg0, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%131, %232) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %233 = "llvm.getelementptr"(%arg0, %45) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%133, %233) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %234 = "llvm.getelementptr"(%arg0, %25) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%135, %234) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %235 = "llvm.getelementptr"(%arg0, %46) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%137, %235) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %236 = "llvm.getelementptr"(%arg0, %38) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%141, %236) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %237 = "llvm.getelementptr"(%arg0, %18) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%143, %237) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %238 = "llvm.getelementptr"(%arg0, %47) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%145, %238) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %239 = "llvm.getelementptr"(%arg0, %32) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%147, %239) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %240 = "llvm.getelementptr"(%arg0, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%149, %240) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %241 = "llvm.getelementptr"(%arg0, %48) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%151, %241) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %242 = "llvm.getelementptr"(%arg0, %26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%153, %242) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %243 = "llvm.getelementptr"(%arg0, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%157, %243) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %244 = "llvm.getelementptr"(%arg0, %39) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%159, %244) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %245 = "llvm.getelementptr"(%arg0, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%161, %245) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %246 = "llvm.getelementptr"(%arg0, %49) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%163, %246) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %247 = "llvm.getelementptr"(%arg0, %33) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%165, %247) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %248 = "llvm.getelementptr"(%arg0, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%167, %248) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %249 = "llvm.getelementptr"(%arg0, %50) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%171, %249) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %250 = "llvm.getelementptr"(%arg0, %27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%173, %250) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %251 = "llvm.getelementptr"(%arg0, %51) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%175, %251) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %252 = "llvm.getelementptr"(%arg0, %40) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%177, %252) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %253 = "llvm.getelementptr"(%arg0, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%179, %253) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %254 = "llvm.getelementptr"(%arg0, %52) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%181, %254) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %255 = "llvm.getelementptr"(%arg0, %34) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%224, %255) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%58) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
with @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255195fieldNtNtNtNtNtB7_7backend6serial3u645field14FieldElement518pow22501 := (p).pow22501,
  @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k := (p).pow2k,
  @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul := (p).mul,
  @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519 := (p).blackBoxByte

theorem block_count (p : Primitives) : (program p).n = 1 := rfl

end
end Agave.Ed25519.Encoding.Compress.Execution
