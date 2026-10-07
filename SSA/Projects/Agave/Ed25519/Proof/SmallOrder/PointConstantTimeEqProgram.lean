module

public import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionElab

/-! Exact pinned region. Regenerate with MLIR/import_small_order.py.
No instruction rewrite. Direct import is distinct from execution refinement. -/

namespace Agave.Ed25519.Verifier.Execution.PointConstantTimeEq

open LeanMLIR.RIR
@[expose] public section

structure Primitives where
  /-- Exact external symbol `_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul`. -/
  fieldMul : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])
  /-- Exact external symbol `_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519`. -/
  bytesConstantTimeEq : Vals [.ptr, .ptr] → EffectM (Vals [.bv 8])
  /-- Exact external symbol `_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519`. -/
  blackBoxByte : Vals [.bv 8] → EffectM (Vals [.bv 8])

def Primitives.resolve (p : Primitives) : String → Option Callee
  | "_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul" => some ⟨[.ptr, .ptr, .ptr], [], p.fieldMul⟩
  | "_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519" => some ⟨[.ptr, .ptr], [.bv 8], p.bytesConstantTimeEq⟩
  | "_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519" => some ⟨[.bv 8], [.bv 8], p.blackBoxByte⟩
  | _ => none

execution_def program (p : Primitives) :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 80 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 13 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 21 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 29 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 37 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 11 : i64}> : () -> i64
    %25 = "llvm.mlir.constant"() <{value = 45 : i64}> : () -> i64
    %26 = "llvm.mlir.constant"() <{value = 12 : i64}> : () -> i64
    %27 = "llvm.mlir.constant"() <{value = 14 : i64}> : () -> i64
    %28 = "llvm.mlir.constant"() <{value = 18 : i64}> : () -> i64
    %29 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %30 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %31 = "llvm.mlir.constant"() <{value = 34 : i64}> : () -> i64
    %32 = "llvm.mlir.constant"() <{value = 17 : i64}> : () -> i64
    %33 = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %34 = "llvm.mlir.constant"() <{value = 50 : i64}> : () -> i64
    %35 = "llvm.mlir.constant"() <{value = 20 : i64}> : () -> i64
    %36 = "llvm.mlir.constant"() <{value = 23 : i64}> : () -> i64
    %37 = "llvm.mlir.constant"() <{value = 22 : i64}> : () -> i64
    %38 = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %39 = "llvm.mlir.constant"() <{value = 39 : i64}> : () -> i64
    %40 = "llvm.mlir.constant"() <{value = 47 : i64}> : () -> i64
    %41 = "llvm.mlir.constant"() <{value = 25 : i64}> : () -> i64
    %42 = "llvm.mlir.constant"() <{value = 27 : i64}> : () -> i64
    %43 = "llvm.mlir.constant"() <{value = 28 : i64}> : () -> i64
    %44 = "llvm.mlir.constant"() <{value = 36 : i64}> : () -> i64
    %45 = "llvm.mlir.constant"() <{value = 30 : i64}> : () -> i64
    %46 = "llvm.mlir.constant"() <{value = 44 : i64}> : () -> i64
    %47 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<32 x i8>}> : (i32) -> !llvm.ptr
    %48 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<32 x i8>}> : (i32) -> !llvm.ptr
    %49 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<32 x i8>}> : (i32) -> !llvm.ptr
    %50 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<32 x i8>}> : (i32) -> !llvm.ptr
    %51 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %52 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %53 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %54 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%54) : (!llvm.ptr) -> ()
    %55 = "llvm.getelementptr"(%arg1, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%54, %arg0, %55) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%53) : (!llvm.ptr) -> ()
    %56 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%53, %arg1, %56) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%50) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope1}> : () -> ()
    %57 = "llvm.load"(%54) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %58 = "llvm.getelementptr"(%54, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %59 = "llvm.load"(%58) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %60 = "llvm.getelementptr"(%54, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %61 = "llvm.load"(%60) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %62 = "llvm.getelementptr"(%54, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %63 = "llvm.load"(%62) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %64 = "llvm.getelementptr"(%54, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %65 = "llvm.load"(%64) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %66 = "llvm.lshr"(%57, %6) : (i64, i64) -> i64
    %67 = "llvm.lshr"(%59, %6) : (i64, i64) -> i64
    %68 = "llvm.lshr"(%61, %6) : (i64, i64) -> i64
    %69 = "llvm.lshr"(%63, %6) : (i64, i64) -> i64
    %70 = "llvm.lshr"(%65, %6) : (i64, i64) -> i64
    %71 = "llvm.and"(%57, %7) : (i64, i64) -> i64
    %72 = "llvm.and"(%59, %7) : (i64, i64) -> i64
    %73 = "llvm.and"(%61, %7) : (i64, i64) -> i64
    %74 = "llvm.and"(%63, %7) : (i64, i64) -> i64
    %75 = "llvm.and"(%65, %7) : (i64, i64) -> i64
    %76 = "llvm.mul"(%70, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %77 = "llvm.add"(%76, %71) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %78 = "llvm.add"(%72, %66) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %79 = "llvm.add"(%73, %67) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %80 = "llvm.add"(%74, %68) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %81 = "llvm.add"(%75, %69) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %82 = "llvm.add"(%77, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %83 = "llvm.lshr"(%82, %6) : (i64, i64) -> i64
    %84 = "llvm.add"(%83, %78) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %85 = "llvm.lshr"(%84, %6) : (i64, i64) -> i64
    %86 = "llvm.add"(%85, %79) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %87 = "llvm.lshr"(%86, %6) : (i64, i64) -> i64
    %88 = "llvm.add"(%87, %80) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %89 = "llvm.lshr"(%88, %6) : (i64, i64) -> i64
    %90 = "llvm.add"(%89, %81) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %91 = "llvm.lshr"(%90, %6) : (i64, i64) -> i64
    %92 = "llvm.mul"(%91, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %93 = "llvm.add"(%92, %77) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %94 = "llvm.lshr"(%93, %6) : (i64, i64) -> i64
    %95 = "llvm.add"(%94, %78) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %96 = "llvm.lshr"(%95, %6) : (i64, i64) -> i64
    %97 = "llvm.add"(%96, %79) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %98 = "llvm.and"(%95, %7) : (i64, i64) -> i64
    %99 = "llvm.lshr"(%97, %6) : (i64, i64) -> i64
    %100 = "llvm.add"(%99, %80) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %101 = "llvm.and"(%97, %7) : (i64, i64) -> i64
    %102 = "llvm.lshr"(%100, %6) : (i64, i64) -> i64
    %103 = "llvm.add"(%102, %81) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %104 = "llvm.and"(%100, %7) : (i64, i64) -> i64
    %105 = "llvm.and"(%103, %7) : (i64, i64) -> i64
    %106 = "llvm.trunc"(%93) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%106, %50) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %107 = "llvm.lshr"(%93, %2) : (i64, i64) -> i64
    %108 = "llvm.getelementptr"(%50, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %109 = "llvm.trunc"(%107) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%109, %108) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %110 = "llvm.lshr"(%93, %3) : (i64, i64) -> i64
    %111 = "llvm.getelementptr"(%50, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %112 = "llvm.trunc"(%110) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%112, %111) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %113 = "llvm.lshr"(%93, %4) : (i64, i64) -> i64
    %114 = "llvm.getelementptr"(%50, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %115 = "llvm.trunc"(%113) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%115, %114) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %116 = "llvm.lshr"(%93, %5) : (i64, i64) -> i64
    %117 = "llvm.getelementptr"(%50, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %118 = "llvm.trunc"(%116) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%118, %117) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %119 = "llvm.lshr"(%93, %13) : (i64, i64) -> i64
    %120 = "llvm.getelementptr"(%50, %14) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %121 = "llvm.trunc"(%119) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%121, %120) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %122 = "llvm.lshr"(%93, %15) : (i64, i64) -> i64
    %123 = "llvm.and"(%122, %16) : (i64, i64) -> i64
    %124 = "llvm.shl"(%98, %11) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %125 = "llvm.or"(%124, %123) <{isDisjoint}> : (i64, i64) -> i64
    %126 = "llvm.getelementptr"(%50, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %127 = "llvm.trunc"(%125) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%127, %126) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %128 = "llvm.lshr"(%95, %14) : (i64, i64) -> i64
    %129 = "llvm.getelementptr"(%50, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %130 = "llvm.trunc"(%128) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%130, %129) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %131 = "llvm.lshr"(%95, %18) : (i64, i64) -> i64
    %132 = "llvm.getelementptr"(%50, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %133 = "llvm.trunc"(%131) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%133, %132) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %134 = "llvm.lshr"(%95, %19) : (i64, i64) -> i64
    %135 = "llvm.getelementptr"(%50, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %136 = "llvm.trunc"(%134) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%136, %135) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %137 = "llvm.lshr"(%95, %21) : (i64, i64) -> i64
    %138 = "llvm.getelementptr"(%50, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %139 = "llvm.trunc"(%137) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%139, %138) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %140 = "llvm.lshr"(%95, %23) : (i64, i64) -> i64
    %141 = "llvm.getelementptr"(%50, %24) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %142 = "llvm.trunc"(%140) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%142, %141) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %143 = "llvm.lshr"(%98, %25) : (i64, i64) -> i64
    %144 = "llvm.shl"(%101, %17) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %145 = "llvm.or"(%144, %143) <{isDisjoint}> : (i64, i64) -> i64
    %146 = "llvm.getelementptr"(%50, %26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %147 = "llvm.trunc"(%145) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%147, %146) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %148 = "llvm.lshr"(%97, %10) : (i64, i64) -> i64
    %149 = "llvm.getelementptr"(%50, %18) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %150 = "llvm.trunc"(%148) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%150, %149) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %151 = "llvm.lshr"(%97, %22) : (i64, i64) -> i64
    %152 = "llvm.getelementptr"(%50, %27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %153 = "llvm.trunc"(%151) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%153, %152) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %154 = "llvm.lshr"(%97, %28) : (i64, i64) -> i64
    %155 = "llvm.getelementptr"(%50, %29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %156 = "llvm.trunc"(%154) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%156, %155) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %157 = "llvm.lshr"(%97, %30) : (i64, i64) -> i64
    %158 = "llvm.getelementptr"(%50, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %159 = "llvm.trunc"(%157) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%159, %158) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %160 = "llvm.lshr"(%97, %31) : (i64, i64) -> i64
    %161 = "llvm.getelementptr"(%50, %32) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %162 = "llvm.trunc"(%160) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%162, %161) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %163 = "llvm.lshr"(%97, %33) : (i64, i64) -> i64
    %164 = "llvm.getelementptr"(%50, %28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %165 = "llvm.trunc"(%163) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%165, %164) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %166 = "llvm.lshr"(%101, %34) : (i64, i64) -> i64
    %167 = "llvm.shl"(%104, %9) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %168 = "llvm.or"(%167, %166) <{isDisjoint}> : (i64, i64) -> i64
    %169 = "llvm.getelementptr"(%50, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %170 = "llvm.trunc"(%168) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%170, %169) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %171 = "llvm.lshr"(%100, %16) : (i64, i64) -> i64
    %172 = "llvm.getelementptr"(%50, %35) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %173 = "llvm.trunc"(%171) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%173, %172) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %174 = "llvm.lshr"(%100, %29) : (i64, i64) -> i64
    %175 = "llvm.getelementptr"(%50, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %176 = "llvm.trunc"(%174) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%176, %175) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %177 = "llvm.lshr"(%100, %36) : (i64, i64) -> i64
    %178 = "llvm.getelementptr"(%50, %37) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %179 = "llvm.trunc"(%177) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%179, %178) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %180 = "llvm.lshr"(%100, %38) : (i64, i64) -> i64
    %181 = "llvm.getelementptr"(%50, %36) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %182 = "llvm.trunc"(%180) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%182, %181) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %183 = "llvm.lshr"(%100, %39) : (i64, i64) -> i64
    %184 = "llvm.getelementptr"(%50, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %185 = "llvm.trunc"(%183) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%185, %184) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %186 = "llvm.lshr"(%104, %40) : (i64, i64) -> i64
    %187 = "llvm.shl"(%105, %12) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %188 = "llvm.or"(%187, %186) <{isDisjoint}> : (i64, i64) -> i64
    %189 = "llvm.getelementptr"(%50, %41) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %190 = "llvm.trunc"(%188) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%190, %189) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %191 = "llvm.lshr"(%103, %12) : (i64, i64) -> i64
    %192 = "llvm.getelementptr"(%50, %30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %193 = "llvm.trunc"(%191) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%193, %192) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %194 = "llvm.lshr"(%103, %26) : (i64, i64) -> i64
    %195 = "llvm.getelementptr"(%50, %42) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %196 = "llvm.trunc"(%194) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%196, %195) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %197 = "llvm.lshr"(%103, %35) : (i64, i64) -> i64
    %198 = "llvm.getelementptr"(%50, %43) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %199 = "llvm.trunc"(%197) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%199, %198) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %200 = "llvm.lshr"(%103, %43) : (i64, i64) -> i64
    %201 = "llvm.getelementptr"(%50, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %202 = "llvm.trunc"(%200) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%202, %201) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %203 = "llvm.lshr"(%103, %44) : (i64, i64) -> i64
    %204 = "llvm.getelementptr"(%50, %45) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %205 = "llvm.trunc"(%203) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%205, %204) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %206 = "llvm.lshr"(%105, %46) : (i64, i64) -> i64
    %207 = "llvm.getelementptr"(%50, %38) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %208 = "llvm.trunc"(%206) <{overflowFlags = 3 : i32}> : (i64) -> i8
    "llvm.store"(%208, %207) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%49) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope3}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope4}> : () -> ()
    %209 = "llvm.load"(%53) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope3, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %210 = "llvm.getelementptr"(%53, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %211 = "llvm.load"(%210) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope3, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %212 = "llvm.getelementptr"(%53, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %213 = "llvm.load"(%212) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope3, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %214 = "llvm.getelementptr"(%53, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %215 = "llvm.load"(%214) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope3, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %216 = "llvm.getelementptr"(%53, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %217 = "llvm.load"(%216) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope3, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %218 = "llvm.lshr"(%209, %6) : (i64, i64) -> i64
    %219 = "llvm.lshr"(%211, %6) : (i64, i64) -> i64
    %220 = "llvm.lshr"(%213, %6) : (i64, i64) -> i64
    %221 = "llvm.lshr"(%215, %6) : (i64, i64) -> i64
    %222 = "llvm.lshr"(%217, %6) : (i64, i64) -> i64
    %223 = "llvm.and"(%209, %7) : (i64, i64) -> i64
    %224 = "llvm.and"(%211, %7) : (i64, i64) -> i64
    %225 = "llvm.and"(%213, %7) : (i64, i64) -> i64
    %226 = "llvm.and"(%215, %7) : (i64, i64) -> i64
    %227 = "llvm.and"(%217, %7) : (i64, i64) -> i64
    %228 = "llvm.mul"(%222, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %229 = "llvm.add"(%228, %223) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %230 = "llvm.add"(%224, %218) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %231 = "llvm.add"(%225, %219) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %232 = "llvm.add"(%226, %220) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %233 = "llvm.add"(%227, %221) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %234 = "llvm.add"(%229, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %235 = "llvm.lshr"(%234, %6) : (i64, i64) -> i64
    %236 = "llvm.add"(%235, %230) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %237 = "llvm.lshr"(%236, %6) : (i64, i64) -> i64
    %238 = "llvm.add"(%237, %231) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %239 = "llvm.lshr"(%238, %6) : (i64, i64) -> i64
    %240 = "llvm.add"(%239, %232) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %241 = "llvm.lshr"(%240, %6) : (i64, i64) -> i64
    %242 = "llvm.add"(%241, %233) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %243 = "llvm.lshr"(%242, %6) : (i64, i64) -> i64
    %244 = "llvm.mul"(%243, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %245 = "llvm.add"(%244, %229) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %246 = "llvm.lshr"(%245, %6) : (i64, i64) -> i64
    %247 = "llvm.add"(%246, %230) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %248 = "llvm.lshr"(%247, %6) : (i64, i64) -> i64
    %249 = "llvm.add"(%248, %231) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %250 = "llvm.and"(%247, %7) : (i64, i64) -> i64
    %251 = "llvm.lshr"(%249, %6) : (i64, i64) -> i64
    %252 = "llvm.add"(%251, %232) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %253 = "llvm.and"(%249, %7) : (i64, i64) -> i64
    %254 = "llvm.lshr"(%252, %6) : (i64, i64) -> i64
    %255 = "llvm.add"(%254, %233) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %256 = "llvm.and"(%252, %7) : (i64, i64) -> i64
    %257 = "llvm.and"(%255, %7) : (i64, i64) -> i64
    %258 = "llvm.trunc"(%245) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%258, %49) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %259 = "llvm.lshr"(%245, %2) : (i64, i64) -> i64
    %260 = "llvm.getelementptr"(%49, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %261 = "llvm.trunc"(%259) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%261, %260) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %262 = "llvm.lshr"(%245, %3) : (i64, i64) -> i64
    %263 = "llvm.getelementptr"(%49, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %264 = "llvm.trunc"(%262) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%264, %263) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %265 = "llvm.lshr"(%245, %4) : (i64, i64) -> i64
    %266 = "llvm.getelementptr"(%49, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %267 = "llvm.trunc"(%265) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%267, %266) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %268 = "llvm.lshr"(%245, %5) : (i64, i64) -> i64
    %269 = "llvm.getelementptr"(%49, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %270 = "llvm.trunc"(%268) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%270, %269) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %271 = "llvm.lshr"(%245, %13) : (i64, i64) -> i64
    %272 = "llvm.getelementptr"(%49, %14) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %273 = "llvm.trunc"(%271) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%273, %272) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %274 = "llvm.lshr"(%245, %15) : (i64, i64) -> i64
    %275 = "llvm.and"(%274, %16) : (i64, i64) -> i64
    %276 = "llvm.shl"(%250, %11) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %277 = "llvm.or"(%276, %275) <{isDisjoint}> : (i64, i64) -> i64
    %278 = "llvm.getelementptr"(%49, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %279 = "llvm.trunc"(%277) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%279, %278) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %280 = "llvm.lshr"(%247, %14) : (i64, i64) -> i64
    %281 = "llvm.getelementptr"(%49, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %282 = "llvm.trunc"(%280) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%282, %281) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %283 = "llvm.lshr"(%247, %18) : (i64, i64) -> i64
    %284 = "llvm.getelementptr"(%49, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %285 = "llvm.trunc"(%283) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%285, %284) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %286 = "llvm.lshr"(%247, %19) : (i64, i64) -> i64
    %287 = "llvm.getelementptr"(%49, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %288 = "llvm.trunc"(%286) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%288, %287) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %289 = "llvm.lshr"(%247, %21) : (i64, i64) -> i64
    %290 = "llvm.getelementptr"(%49, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %291 = "llvm.trunc"(%289) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%291, %290) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %292 = "llvm.lshr"(%247, %23) : (i64, i64) -> i64
    %293 = "llvm.getelementptr"(%49, %24) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %294 = "llvm.trunc"(%292) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%294, %293) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %295 = "llvm.lshr"(%250, %25) : (i64, i64) -> i64
    %296 = "llvm.shl"(%253, %17) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %297 = "llvm.or"(%296, %295) <{isDisjoint}> : (i64, i64) -> i64
    %298 = "llvm.getelementptr"(%49, %26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %299 = "llvm.trunc"(%297) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%299, %298) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %300 = "llvm.lshr"(%249, %10) : (i64, i64) -> i64
    %301 = "llvm.getelementptr"(%49, %18) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %302 = "llvm.trunc"(%300) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%302, %301) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %303 = "llvm.lshr"(%249, %22) : (i64, i64) -> i64
    %304 = "llvm.getelementptr"(%49, %27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %305 = "llvm.trunc"(%303) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%305, %304) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %306 = "llvm.lshr"(%249, %28) : (i64, i64) -> i64
    %307 = "llvm.getelementptr"(%49, %29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %308 = "llvm.trunc"(%306) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%308, %307) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %309 = "llvm.lshr"(%249, %30) : (i64, i64) -> i64
    %310 = "llvm.getelementptr"(%49, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %311 = "llvm.trunc"(%309) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%311, %310) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %312 = "llvm.lshr"(%249, %31) : (i64, i64) -> i64
    %313 = "llvm.getelementptr"(%49, %32) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %314 = "llvm.trunc"(%312) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%314, %313) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %315 = "llvm.lshr"(%249, %33) : (i64, i64) -> i64
    %316 = "llvm.getelementptr"(%49, %28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %317 = "llvm.trunc"(%315) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%317, %316) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %318 = "llvm.lshr"(%253, %34) : (i64, i64) -> i64
    %319 = "llvm.shl"(%256, %9) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %320 = "llvm.or"(%319, %318) <{isDisjoint}> : (i64, i64) -> i64
    %321 = "llvm.getelementptr"(%49, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %322 = "llvm.trunc"(%320) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%322, %321) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %323 = "llvm.lshr"(%252, %16) : (i64, i64) -> i64
    %324 = "llvm.getelementptr"(%49, %35) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %325 = "llvm.trunc"(%323) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%325, %324) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %326 = "llvm.lshr"(%252, %29) : (i64, i64) -> i64
    %327 = "llvm.getelementptr"(%49, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %328 = "llvm.trunc"(%326) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%328, %327) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %329 = "llvm.lshr"(%252, %36) : (i64, i64) -> i64
    %330 = "llvm.getelementptr"(%49, %37) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %331 = "llvm.trunc"(%329) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%331, %330) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %332 = "llvm.lshr"(%252, %38) : (i64, i64) -> i64
    %333 = "llvm.getelementptr"(%49, %36) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %334 = "llvm.trunc"(%332) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%334, %333) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %335 = "llvm.lshr"(%252, %39) : (i64, i64) -> i64
    %336 = "llvm.getelementptr"(%49, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %337 = "llvm.trunc"(%335) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%337, %336) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %338 = "llvm.lshr"(%256, %40) : (i64, i64) -> i64
    %339 = "llvm.shl"(%257, %12) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %340 = "llvm.or"(%339, %338) <{isDisjoint}> : (i64, i64) -> i64
    %341 = "llvm.getelementptr"(%49, %41) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %342 = "llvm.trunc"(%340) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%342, %341) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %343 = "llvm.lshr"(%255, %12) : (i64, i64) -> i64
    %344 = "llvm.getelementptr"(%49, %30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %345 = "llvm.trunc"(%343) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%345, %344) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %346 = "llvm.lshr"(%255, %26) : (i64, i64) -> i64
    %347 = "llvm.getelementptr"(%49, %42) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %348 = "llvm.trunc"(%346) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%348, %347) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %349 = "llvm.lshr"(%255, %35) : (i64, i64) -> i64
    %350 = "llvm.getelementptr"(%49, %43) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %351 = "llvm.trunc"(%349) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%351, %350) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %352 = "llvm.lshr"(%255, %43) : (i64, i64) -> i64
    %353 = "llvm.getelementptr"(%49, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %354 = "llvm.trunc"(%352) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%354, %353) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %355 = "llvm.lshr"(%255, %44) : (i64, i64) -> i64
    %356 = "llvm.getelementptr"(%49, %45) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %357 = "llvm.trunc"(%355) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%357, %356) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %358 = "llvm.lshr"(%257, %46) : (i64, i64) -> i64
    %359 = "llvm.getelementptr"(%49, %38) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %360 = "llvm.trunc"(%358) <{overflowFlags = 3 : i32}> : (i64) -> i8
    "llvm.store"(%360, %359) <{alias_scopes = [#alias_scope3], alignment = 1 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %361 = "llvm.call"(%50, %49) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, inline_hint, memory_effects = #llvm.memory_effects<other = none, argMem = read, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>, res_attrs = [{llvm.noundef}]}> : (!llvm.ptr, !llvm.ptr) -> i8
    "llvm.intr.lifetime.end"(%49) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%50) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%52) : (!llvm.ptr) -> ()
    %362 = "llvm.getelementptr"(%arg0, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%52, %362, %55) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%51) : (!llvm.ptr) -> ()
    %363 = "llvm.getelementptr"(%arg1, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%51, %363, %56) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%48) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope6}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope7}> : () -> ()
    %364 = "llvm.load"(%52) <{alias_scopes = [#alias_scope7], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope8], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %365 = "llvm.getelementptr"(%52, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %366 = "llvm.load"(%365) <{alias_scopes = [#alias_scope7], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope8], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %367 = "llvm.getelementptr"(%52, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %368 = "llvm.load"(%367) <{alias_scopes = [#alias_scope7], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope8], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %369 = "llvm.getelementptr"(%52, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %370 = "llvm.load"(%369) <{alias_scopes = [#alias_scope7], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope8], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %371 = "llvm.getelementptr"(%52, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %372 = "llvm.load"(%371) <{alias_scopes = [#alias_scope7], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope8], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %373 = "llvm.lshr"(%364, %6) : (i64, i64) -> i64
    %374 = "llvm.lshr"(%366, %6) : (i64, i64) -> i64
    %375 = "llvm.lshr"(%368, %6) : (i64, i64) -> i64
    %376 = "llvm.lshr"(%370, %6) : (i64, i64) -> i64
    %377 = "llvm.lshr"(%372, %6) : (i64, i64) -> i64
    %378 = "llvm.and"(%364, %7) : (i64, i64) -> i64
    %379 = "llvm.and"(%366, %7) : (i64, i64) -> i64
    %380 = "llvm.and"(%368, %7) : (i64, i64) -> i64
    %381 = "llvm.and"(%370, %7) : (i64, i64) -> i64
    %382 = "llvm.and"(%372, %7) : (i64, i64) -> i64
    %383 = "llvm.mul"(%377, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %384 = "llvm.add"(%383, %378) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %385 = "llvm.add"(%379, %373) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %386 = "llvm.add"(%380, %374) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %387 = "llvm.add"(%381, %375) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %388 = "llvm.add"(%382, %376) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %389 = "llvm.add"(%384, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %390 = "llvm.lshr"(%389, %6) : (i64, i64) -> i64
    %391 = "llvm.add"(%390, %385) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %392 = "llvm.lshr"(%391, %6) : (i64, i64) -> i64
    %393 = "llvm.add"(%392, %386) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %394 = "llvm.lshr"(%393, %6) : (i64, i64) -> i64
    %395 = "llvm.add"(%394, %387) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %396 = "llvm.lshr"(%395, %6) : (i64, i64) -> i64
    %397 = "llvm.add"(%396, %388) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %398 = "llvm.lshr"(%397, %6) : (i64, i64) -> i64
    %399 = "llvm.mul"(%398, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %400 = "llvm.add"(%399, %384) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %401 = "llvm.lshr"(%400, %6) : (i64, i64) -> i64
    %402 = "llvm.add"(%401, %385) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %403 = "llvm.lshr"(%402, %6) : (i64, i64) -> i64
    %404 = "llvm.add"(%403, %386) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %405 = "llvm.and"(%402, %7) : (i64, i64) -> i64
    %406 = "llvm.lshr"(%404, %6) : (i64, i64) -> i64
    %407 = "llvm.add"(%406, %387) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %408 = "llvm.and"(%404, %7) : (i64, i64) -> i64
    %409 = "llvm.lshr"(%407, %6) : (i64, i64) -> i64
    %410 = "llvm.add"(%409, %388) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %411 = "llvm.and"(%407, %7) : (i64, i64) -> i64
    %412 = "llvm.and"(%410, %7) : (i64, i64) -> i64
    %413 = "llvm.trunc"(%400) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%413, %48) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %414 = "llvm.lshr"(%400, %2) : (i64, i64) -> i64
    %415 = "llvm.getelementptr"(%48, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %416 = "llvm.trunc"(%414) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%416, %415) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %417 = "llvm.lshr"(%400, %3) : (i64, i64) -> i64
    %418 = "llvm.getelementptr"(%48, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %419 = "llvm.trunc"(%417) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%419, %418) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %420 = "llvm.lshr"(%400, %4) : (i64, i64) -> i64
    %421 = "llvm.getelementptr"(%48, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %422 = "llvm.trunc"(%420) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%422, %421) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %423 = "llvm.lshr"(%400, %5) : (i64, i64) -> i64
    %424 = "llvm.getelementptr"(%48, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %425 = "llvm.trunc"(%423) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%425, %424) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %426 = "llvm.lshr"(%400, %13) : (i64, i64) -> i64
    %427 = "llvm.getelementptr"(%48, %14) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %428 = "llvm.trunc"(%426) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%428, %427) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %429 = "llvm.lshr"(%400, %15) : (i64, i64) -> i64
    %430 = "llvm.and"(%429, %16) : (i64, i64) -> i64
    %431 = "llvm.shl"(%405, %11) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %432 = "llvm.or"(%431, %430) <{isDisjoint}> : (i64, i64) -> i64
    %433 = "llvm.getelementptr"(%48, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %434 = "llvm.trunc"(%432) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%434, %433) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %435 = "llvm.lshr"(%402, %14) : (i64, i64) -> i64
    %436 = "llvm.getelementptr"(%48, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %437 = "llvm.trunc"(%435) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%437, %436) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %438 = "llvm.lshr"(%402, %18) : (i64, i64) -> i64
    %439 = "llvm.getelementptr"(%48, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %440 = "llvm.trunc"(%438) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%440, %439) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %441 = "llvm.lshr"(%402, %19) : (i64, i64) -> i64
    %442 = "llvm.getelementptr"(%48, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %443 = "llvm.trunc"(%441) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%443, %442) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %444 = "llvm.lshr"(%402, %21) : (i64, i64) -> i64
    %445 = "llvm.getelementptr"(%48, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %446 = "llvm.trunc"(%444) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%446, %445) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %447 = "llvm.lshr"(%402, %23) : (i64, i64) -> i64
    %448 = "llvm.getelementptr"(%48, %24) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %449 = "llvm.trunc"(%447) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%449, %448) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %450 = "llvm.lshr"(%405, %25) : (i64, i64) -> i64
    %451 = "llvm.shl"(%408, %17) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %452 = "llvm.or"(%451, %450) <{isDisjoint}> : (i64, i64) -> i64
    %453 = "llvm.getelementptr"(%48, %26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %454 = "llvm.trunc"(%452) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%454, %453) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %455 = "llvm.lshr"(%404, %10) : (i64, i64) -> i64
    %456 = "llvm.getelementptr"(%48, %18) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %457 = "llvm.trunc"(%455) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%457, %456) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %458 = "llvm.lshr"(%404, %22) : (i64, i64) -> i64
    %459 = "llvm.getelementptr"(%48, %27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %460 = "llvm.trunc"(%458) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%460, %459) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %461 = "llvm.lshr"(%404, %28) : (i64, i64) -> i64
    %462 = "llvm.getelementptr"(%48, %29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %463 = "llvm.trunc"(%461) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%463, %462) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %464 = "llvm.lshr"(%404, %30) : (i64, i64) -> i64
    %465 = "llvm.getelementptr"(%48, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %466 = "llvm.trunc"(%464) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%466, %465) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %467 = "llvm.lshr"(%404, %31) : (i64, i64) -> i64
    %468 = "llvm.getelementptr"(%48, %32) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %469 = "llvm.trunc"(%467) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%469, %468) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %470 = "llvm.lshr"(%404, %33) : (i64, i64) -> i64
    %471 = "llvm.getelementptr"(%48, %28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %472 = "llvm.trunc"(%470) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%472, %471) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %473 = "llvm.lshr"(%408, %34) : (i64, i64) -> i64
    %474 = "llvm.shl"(%411, %9) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %475 = "llvm.or"(%474, %473) <{isDisjoint}> : (i64, i64) -> i64
    %476 = "llvm.getelementptr"(%48, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %477 = "llvm.trunc"(%475) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%477, %476) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %478 = "llvm.lshr"(%407, %16) : (i64, i64) -> i64
    %479 = "llvm.getelementptr"(%48, %35) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %480 = "llvm.trunc"(%478) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%480, %479) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %481 = "llvm.lshr"(%407, %29) : (i64, i64) -> i64
    %482 = "llvm.getelementptr"(%48, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %483 = "llvm.trunc"(%481) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%483, %482) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %484 = "llvm.lshr"(%407, %36) : (i64, i64) -> i64
    %485 = "llvm.getelementptr"(%48, %37) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %486 = "llvm.trunc"(%484) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%486, %485) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %487 = "llvm.lshr"(%407, %38) : (i64, i64) -> i64
    %488 = "llvm.getelementptr"(%48, %36) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %489 = "llvm.trunc"(%487) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%489, %488) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %490 = "llvm.lshr"(%407, %39) : (i64, i64) -> i64
    %491 = "llvm.getelementptr"(%48, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %492 = "llvm.trunc"(%490) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%492, %491) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %493 = "llvm.lshr"(%411, %40) : (i64, i64) -> i64
    %494 = "llvm.shl"(%412, %12) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %495 = "llvm.or"(%494, %493) <{isDisjoint}> : (i64, i64) -> i64
    %496 = "llvm.getelementptr"(%48, %41) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %497 = "llvm.trunc"(%495) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%497, %496) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %498 = "llvm.lshr"(%410, %12) : (i64, i64) -> i64
    %499 = "llvm.getelementptr"(%48, %30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %500 = "llvm.trunc"(%498) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%500, %499) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %501 = "llvm.lshr"(%410, %26) : (i64, i64) -> i64
    %502 = "llvm.getelementptr"(%48, %42) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %503 = "llvm.trunc"(%501) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%503, %502) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %504 = "llvm.lshr"(%410, %35) : (i64, i64) -> i64
    %505 = "llvm.getelementptr"(%48, %43) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %506 = "llvm.trunc"(%504) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%506, %505) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %507 = "llvm.lshr"(%410, %43) : (i64, i64) -> i64
    %508 = "llvm.getelementptr"(%48, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %509 = "llvm.trunc"(%507) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%509, %508) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %510 = "llvm.lshr"(%410, %44) : (i64, i64) -> i64
    %511 = "llvm.getelementptr"(%48, %45) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %512 = "llvm.trunc"(%510) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%512, %511) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %513 = "llvm.lshr"(%412, %46) : (i64, i64) -> i64
    %514 = "llvm.getelementptr"(%48, %38) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %515 = "llvm.trunc"(%513) <{overflowFlags = 3 : i32}> : (i64) -> i8
    "llvm.store"(%515, %514) <{alias_scopes = [#alias_scope6], alignment = 1 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%47) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope9}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope10}> : () -> ()
    %516 = "llvm.load"(%51) <{alias_scopes = [#alias_scope10], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope11], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %517 = "llvm.getelementptr"(%51, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %518 = "llvm.load"(%517) <{alias_scopes = [#alias_scope10], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope11], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %519 = "llvm.getelementptr"(%51, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %520 = "llvm.load"(%519) <{alias_scopes = [#alias_scope10], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope11], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %521 = "llvm.getelementptr"(%51, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %522 = "llvm.load"(%521) <{alias_scopes = [#alias_scope10], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope11], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %523 = "llvm.getelementptr"(%51, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %524 = "llvm.load"(%523) <{alias_scopes = [#alias_scope10], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope11], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %525 = "llvm.lshr"(%516, %6) : (i64, i64) -> i64
    %526 = "llvm.lshr"(%518, %6) : (i64, i64) -> i64
    %527 = "llvm.lshr"(%520, %6) : (i64, i64) -> i64
    %528 = "llvm.lshr"(%522, %6) : (i64, i64) -> i64
    %529 = "llvm.lshr"(%524, %6) : (i64, i64) -> i64
    %530 = "llvm.and"(%516, %7) : (i64, i64) -> i64
    %531 = "llvm.and"(%518, %7) : (i64, i64) -> i64
    %532 = "llvm.and"(%520, %7) : (i64, i64) -> i64
    %533 = "llvm.and"(%522, %7) : (i64, i64) -> i64
    %534 = "llvm.and"(%524, %7) : (i64, i64) -> i64
    %535 = "llvm.mul"(%529, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %536 = "llvm.add"(%535, %530) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %537 = "llvm.add"(%531, %525) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %538 = "llvm.add"(%532, %526) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %539 = "llvm.add"(%533, %527) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %540 = "llvm.add"(%534, %528) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %541 = "llvm.add"(%536, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %542 = "llvm.lshr"(%541, %6) : (i64, i64) -> i64
    %543 = "llvm.add"(%542, %537) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %544 = "llvm.lshr"(%543, %6) : (i64, i64) -> i64
    %545 = "llvm.add"(%544, %538) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %546 = "llvm.lshr"(%545, %6) : (i64, i64) -> i64
    %547 = "llvm.add"(%546, %539) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %548 = "llvm.lshr"(%547, %6) : (i64, i64) -> i64
    %549 = "llvm.add"(%548, %540) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %550 = "llvm.lshr"(%549, %6) : (i64, i64) -> i64
    %551 = "llvm.mul"(%550, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %552 = "llvm.add"(%551, %536) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %553 = "llvm.lshr"(%552, %6) : (i64, i64) -> i64
    %554 = "llvm.add"(%553, %537) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %555 = "llvm.lshr"(%554, %6) : (i64, i64) -> i64
    %556 = "llvm.add"(%555, %538) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %557 = "llvm.and"(%554, %7) : (i64, i64) -> i64
    %558 = "llvm.lshr"(%556, %6) : (i64, i64) -> i64
    %559 = "llvm.add"(%558, %539) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %560 = "llvm.and"(%556, %7) : (i64, i64) -> i64
    %561 = "llvm.lshr"(%559, %6) : (i64, i64) -> i64
    %562 = "llvm.add"(%561, %540) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %563 = "llvm.and"(%559, %7) : (i64, i64) -> i64
    %564 = "llvm.and"(%562, %7) : (i64, i64) -> i64
    %565 = "llvm.trunc"(%552) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%565, %47) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %566 = "llvm.lshr"(%552, %2) : (i64, i64) -> i64
    %567 = "llvm.getelementptr"(%47, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %568 = "llvm.trunc"(%566) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%568, %567) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %569 = "llvm.lshr"(%552, %3) : (i64, i64) -> i64
    %570 = "llvm.getelementptr"(%47, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %571 = "llvm.trunc"(%569) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%571, %570) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %572 = "llvm.lshr"(%552, %4) : (i64, i64) -> i64
    %573 = "llvm.getelementptr"(%47, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %574 = "llvm.trunc"(%572) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%574, %573) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %575 = "llvm.lshr"(%552, %5) : (i64, i64) -> i64
    %576 = "llvm.getelementptr"(%47, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %577 = "llvm.trunc"(%575) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%577, %576) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %578 = "llvm.lshr"(%552, %13) : (i64, i64) -> i64
    %579 = "llvm.getelementptr"(%47, %14) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %580 = "llvm.trunc"(%578) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%580, %579) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %581 = "llvm.lshr"(%552, %15) : (i64, i64) -> i64
    %582 = "llvm.and"(%581, %16) : (i64, i64) -> i64
    %583 = "llvm.shl"(%557, %11) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %584 = "llvm.or"(%583, %582) <{isDisjoint}> : (i64, i64) -> i64
    %585 = "llvm.getelementptr"(%47, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %586 = "llvm.trunc"(%584) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%586, %585) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %587 = "llvm.lshr"(%554, %14) : (i64, i64) -> i64
    %588 = "llvm.getelementptr"(%47, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %589 = "llvm.trunc"(%587) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%589, %588) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %590 = "llvm.lshr"(%554, %18) : (i64, i64) -> i64
    %591 = "llvm.getelementptr"(%47, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %592 = "llvm.trunc"(%590) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%592, %591) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %593 = "llvm.lshr"(%554, %19) : (i64, i64) -> i64
    %594 = "llvm.getelementptr"(%47, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %595 = "llvm.trunc"(%593) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%595, %594) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %596 = "llvm.lshr"(%554, %21) : (i64, i64) -> i64
    %597 = "llvm.getelementptr"(%47, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %598 = "llvm.trunc"(%596) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%598, %597) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %599 = "llvm.lshr"(%554, %23) : (i64, i64) -> i64
    %600 = "llvm.getelementptr"(%47, %24) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %601 = "llvm.trunc"(%599) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%601, %600) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %602 = "llvm.lshr"(%557, %25) : (i64, i64) -> i64
    %603 = "llvm.shl"(%560, %17) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %604 = "llvm.or"(%603, %602) <{isDisjoint}> : (i64, i64) -> i64
    %605 = "llvm.getelementptr"(%47, %26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %606 = "llvm.trunc"(%604) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%606, %605) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %607 = "llvm.lshr"(%556, %10) : (i64, i64) -> i64
    %608 = "llvm.getelementptr"(%47, %18) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %609 = "llvm.trunc"(%607) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%609, %608) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %610 = "llvm.lshr"(%556, %22) : (i64, i64) -> i64
    %611 = "llvm.getelementptr"(%47, %27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %612 = "llvm.trunc"(%610) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%612, %611) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %613 = "llvm.lshr"(%556, %28) : (i64, i64) -> i64
    %614 = "llvm.getelementptr"(%47, %29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %615 = "llvm.trunc"(%613) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%615, %614) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %616 = "llvm.lshr"(%556, %30) : (i64, i64) -> i64
    %617 = "llvm.getelementptr"(%47, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %618 = "llvm.trunc"(%616) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%618, %617) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %619 = "llvm.lshr"(%556, %31) : (i64, i64) -> i64
    %620 = "llvm.getelementptr"(%47, %32) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %621 = "llvm.trunc"(%619) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%621, %620) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %622 = "llvm.lshr"(%556, %33) : (i64, i64) -> i64
    %623 = "llvm.getelementptr"(%47, %28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %624 = "llvm.trunc"(%622) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%624, %623) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %625 = "llvm.lshr"(%560, %34) : (i64, i64) -> i64
    %626 = "llvm.shl"(%563, %9) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %627 = "llvm.or"(%626, %625) <{isDisjoint}> : (i64, i64) -> i64
    %628 = "llvm.getelementptr"(%47, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %629 = "llvm.trunc"(%627) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%629, %628) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %630 = "llvm.lshr"(%559, %16) : (i64, i64) -> i64
    %631 = "llvm.getelementptr"(%47, %35) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %632 = "llvm.trunc"(%630) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%632, %631) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %633 = "llvm.lshr"(%559, %29) : (i64, i64) -> i64
    %634 = "llvm.getelementptr"(%47, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %635 = "llvm.trunc"(%633) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%635, %634) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %636 = "llvm.lshr"(%559, %36) : (i64, i64) -> i64
    %637 = "llvm.getelementptr"(%47, %37) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %638 = "llvm.trunc"(%636) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%638, %637) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %639 = "llvm.lshr"(%559, %38) : (i64, i64) -> i64
    %640 = "llvm.getelementptr"(%47, %36) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %641 = "llvm.trunc"(%639) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%641, %640) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %642 = "llvm.lshr"(%559, %39) : (i64, i64) -> i64
    %643 = "llvm.getelementptr"(%47, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %644 = "llvm.trunc"(%642) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%644, %643) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %645 = "llvm.lshr"(%563, %40) : (i64, i64) -> i64
    %646 = "llvm.shl"(%564, %12) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %647 = "llvm.or"(%646, %645) <{isDisjoint}> : (i64, i64) -> i64
    %648 = "llvm.getelementptr"(%47, %41) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %649 = "llvm.trunc"(%647) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%649, %648) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %650 = "llvm.lshr"(%562, %12) : (i64, i64) -> i64
    %651 = "llvm.getelementptr"(%47, %30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %652 = "llvm.trunc"(%650) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%652, %651) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %653 = "llvm.lshr"(%562, %26) : (i64, i64) -> i64
    %654 = "llvm.getelementptr"(%47, %42) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %655 = "llvm.trunc"(%653) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%655, %654) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %656 = "llvm.lshr"(%562, %35) : (i64, i64) -> i64
    %657 = "llvm.getelementptr"(%47, %43) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %658 = "llvm.trunc"(%656) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%658, %657) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %659 = "llvm.lshr"(%562, %43) : (i64, i64) -> i64
    %660 = "llvm.getelementptr"(%47, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %661 = "llvm.trunc"(%659) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%661, %660) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %662 = "llvm.lshr"(%562, %44) : (i64, i64) -> i64
    %663 = "llvm.getelementptr"(%47, %45) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %664 = "llvm.trunc"(%662) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%664, %663) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %665 = "llvm.lshr"(%564, %46) : (i64, i64) -> i64
    %666 = "llvm.getelementptr"(%47, %38) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %667 = "llvm.trunc"(%665) <{overflowFlags = 3 : i32}> : (i64) -> i8
    "llvm.store"(%667, %666) <{alias_scopes = [#alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %668 = "llvm.call"(%48, %47) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, inline_hint, memory_effects = #llvm.memory_effects<other = none, argMem = read, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>, res_attrs = [{llvm.noundef}]}> : (!llvm.ptr, !llvm.ptr) -> i8
    "llvm.intr.lifetime.end"(%47) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%48) : (!llvm.ptr) -> ()
    %669 = "llvm.and"(%668, %361) : (i8, i8) -> i8
    %670 = "llvm.call"(%669) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    "llvm.intr.lifetime.end"(%51) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%52) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%53) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%54) : (!llvm.ptr) -> ()
    "llvm.return"(%670) : (i8) -> ()
}
with @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul := p.fieldMul,
  @_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519 := p.bytesConstantTimeEq,
  @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519 := p.blackBoxByte

theorem block_count (p : Primitives) : (program p).n = 1 := rfl

end
end Agave.Ed25519.Verifier.Execution.PointConstantTimeEq
