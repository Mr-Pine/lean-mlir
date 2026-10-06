module

public import SSA.Projects.RIR.Syntax.Elab

/-! Complete pinned compiler CFG, copied without instruction changes.
Regenerate using import_cfg.py. The source MLIR and all source constants
remain in MLIR/generated; the extraction manifest records provenance.

`program` is a checked import attempt, not a successful-refinement theorem.
Each external primitive has its exact call-site signature and each global
address is explicit. Primitive behavior, memory separation, table contents,
allocation invariants and termination remain independent proof obligations.
-/

namespace Agave.Ed25519.DoubleBase.SerialCFG

open LeanMLIR.RIR
@[expose] public section

structure Primitives where
  /-- `_RNvXs0_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable5NtNtNtNtB7_7backend6serial12curve_models20ProjectiveNielsPointEINtNtCsgxBkk5gSRhY_4core7convert4FromRNtNtB7_7edwards12EdwardsPointE4from` -/
  call0 : Vals [.ptr, .ptr] → EffectM (Vals [])
  /-- `_RNvMsa_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_15ProjectivePoint6double` -/
  call1 : Vals [.ptr, .ptr] → EffectM (Vals [])
  /-- `_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul` -/
  call2 : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])
  /-- `_RNvXsc_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB5_20ProjectiveNielsPointE3sub` -/
  call3 : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])
  /-- `_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check` -/
  call4 : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals [])
  /-- `_RNvXsb_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB5_20ProjectiveNielsPointE3add` -/
  call5 : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])
  /-- `_RNvXse_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB5_16AffineNielsPointE3sub` -/
  call6 : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])
  /-- `_RNvXsd_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB5_16AffineNielsPointE3add` -/
  call7 : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])
  /-- `_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k` -/
  call8 : Vals [.ptr, .ptr, .bv 32] → EffectM (Vals [])

def Primitives.resolve (p : Primitives) : String → Option Callee
  | "_RNvXs0_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable5NtNtNtNtB7_7backend6serial12curve_models20ProjectiveNielsPointEINtNtCsgxBkk5gSRhY_4core7convert4FromRNtNtB7_7edwards12EdwardsPointE4from" => some ⟨[.ptr, .ptr], [], p.call0⟩
  | "_RNvMsa_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_15ProjectivePoint6double" => some ⟨[.ptr, .ptr], [], p.call1⟩
  | "_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul" => some ⟨[.ptr, .ptr, .ptr], [], p.call2⟩
  | "_RNvXsc_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB5_20ProjectiveNielsPointE3sub" => some ⟨[.ptr, .ptr, .ptr], [], p.call3⟩
  | "_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check" => some ⟨[.bv 64, .bv 64, .ptr], [], p.call4⟩
  | "_RNvXsb_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB5_20ProjectiveNielsPointE3add" => some ⟨[.ptr, .ptr, .ptr], [], p.call5⟩
  | "_RNvXse_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB5_16AffineNielsPointE3sub" => some ⟨[.ptr, .ptr, .ptr], [], p.call6⟩
  | "_RNvXsd_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB5_16AffineNielsPointE3add" => some ⟨[.ptr, .ptr, .ptr], [], p.call7⟩
  | "_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k" => some ⟨[.ptr, .ptr, .bv 32], [], p.call8⟩
  | _ => none

structure Globals where
  /-- `alloc_d6091242425a18f93aa551ed73483e0d`; its source initializer must be present in memory. -/
  address0 : Pointer
  /-- `alloc_a8fabae8f73f66aef6660ad7c9447c5d`; its source initializer must be present in memory. -/
  address1 : Pointer
  /-- `alloc_f7b128ba219626851d37833adc9e2368`; its source initializer must be present in memory. -/
  address2 : Pointer
  /-- `alloc_eaf951945d20f8425ce4c25607db196f`; its source initializer must be present in memory. -/
  address3 : Pointer

def Globals.resolve (g : Globals) : String → Option Pointer
  | "alloc_d6091242425a18f93aa551ed73483e0d" => some g.address0
  | "alloc_a8fabae8f73f66aef6660ad7c9447c5d" => some g.address1
  | "alloc_f7b128ba219626851d37833adc9e2368" => some g.address2
  | "alloc_eaf951945d20f8425ce4c25607db196f" => some g.address3
  | _ => none

def region : MLIR.Region := mlir_region%
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %2 = "llvm.mlir.constant"() <{value = 256 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 63 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 59 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = -32 : i8}> : () -> i8
    %13 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 251 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 56 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 255 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 127 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 248 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %21 = "llvm.mlir.addressof"() <{global_name = @alloc_d6091242425a18f93aa551ed73483e0d}> : () -> !llvm.ptr
    %22 = "llvm.mlir.constant"() <{value = 80 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 120 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 16 : i8}> : () -> i8
    %25 = "llvm.mlir.addressof"() <{global_name = @alloc_a8fabae8f73f66aef6660ad7c9447c5d}> : () -> !llvm.ptr
    %26 = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    %27 = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
    %28 = "llvm.mlir.addressof"() <{global_name = @alloc_f7b128ba219626851d37833adc9e2368}> : () -> !llvm.ptr
    %29 = "llvm.mlir.addressof"() <{global_name = @alloc_eaf951945d20f8425ce4c25607db196f}> : () -> !llvm.ptr
    %30 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %31 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %32 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<120 x i8>}> : (i32) -> !llvm.ptr
    %33 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %34 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %35 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %36 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %37 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %38 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<120 x i8>}> : (i32) -> !llvm.ptr
    %39 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<1280 x i8>}> : (i32) -> !llvm.ptr
    %40 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<256 x i8>}> : (i32) -> !llvm.ptr
    %41 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<256 x i8>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%41) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope}> : () -> ()
    "llvm.intr.memset"(%41, %1, %2) <{alias_scopes = [#alias_scope], arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 256 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false, noalias_scopes = [#alias_scope1]}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.intr.lifetime.start"(%31) : (!llvm.ptr) -> ()
    %42 = "llvm.getelementptr"(%31, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%4, %42) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%31, %arg1, %3) <{alias_scopes = [#alias_scope2, #alias_scope3], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef, llvm.readonly}, {}], isVolatile = false, noalias_scopes = [#alias_scope]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.br"(%4, %4)[^bb1] : (i64, i64) -> ()
  ^bb1(%43: i64, %44: i64):  // 2 preds: ^bb0, ^bb6
    "llvm.br"(%43)[^bb2] : (i64) -> ()
  ^bb2(%45: i64):  // 2 preds: ^bb1, ^bb5
    %46 = "llvm.lshr"(%45, %5) : (i64, i64) -> i64
    %47 = "llvm.and"(%45, %6) : (i64, i64) -> i64
    %48 = "llvm.icmp"(%47, %7) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %49 = "llvm.getelementptr"(%31, %46) <{elem_type = i64, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %50 = "llvm.load"(%49) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %51 = "llvm.lshr"(%50, %47) : (i64, i64) -> i64
    "llvm.cond_br"(%48, %51)[^bb4, ^bb3] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i64) -> ()
  ^bb3:  // pred: ^bb2
    %52 = "llvm.getelementptr"(%49, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %53 = "llvm.load"(%52) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %54 = "llvm.sub"(%4, %45) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %55 = "llvm.and"(%54, %6) : (i64, i64) -> i64
    %56 = "llvm.shl"(%53, %55) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %57 = "llvm.or"(%56, %51) : (i64, i64) -> i64
    "llvm.br"(%57)[^bb4] : (i64) -> ()
  ^bb4(%58: i64):  // 2 preds: ^bb2, ^bb3
    %59 = "llvm.and"(%58, %9) : (i64, i64) -> i64
    %60 = "llvm.add"(%59, %44) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %61 = "llvm.and"(%60, %10) : (i64, i64) -> i64
    %62 = "llvm.icmp"(%61, %4) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%62)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb5:  // pred: ^bb4
    %63 = "llvm.add"(%45, %10) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %64 = "llvm.icmp"(%63, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%64, %63)[^bb7, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
  ^bb6:  // pred: ^bb4
    %65 = "llvm.icmp"(%60, %11) <{predicate = 8 : i64}> : (i64, i64) -> i1
    %66 = "llvm.trunc"(%60) <{overflowFlags = 3 : i32}> : (i64) -> i8
    %67 = "llvm.select"(%65, %12, %1) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, i8, i8) -> i8
    %68 = "llvm.add"(%67, %66) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %69 = "llvm.zext"(%65) : (i1) -> i64
    %70 = "llvm.getelementptr"(%41, %45) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%68, %70) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %71 = "llvm.add"(%45, %13) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %72 = "llvm.icmp"(%45, %14) <{predicate = 6 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%72, %71, %69)[^bb1, ^bb7] <{operandSegmentSizes = array<i32: 1, 2, 0>}> : (i1, i64, i64) -> ()
  ^bb7:  // 2 preds: ^bb5, ^bb6
    "llvm.intr.lifetime.end"(%31) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%40) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope4}> : () -> ()
    "llvm.intr.memset"(%40, %1, %2) <{alias_scopes = [#alias_scope4], arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 256 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false, noalias_scopes = [#alias_scope5]}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.intr.lifetime.start"(%30) : (!llvm.ptr) -> ()
    %73 = "llvm.getelementptr"(%30, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%4, %73) <{alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%30, %arg3, %3) <{alias_scopes = [#alias_scope6, #alias_scope7], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef, llvm.readonly}, {}], isVolatile = false, noalias_scopes = [#alias_scope4]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.br"(%4, %4)[^bb8] : (i64, i64) -> ()
  ^bb8(%74: i64, %75: i64):  // 2 preds: ^bb7, ^bb13
    "llvm.br"(%74)[^bb9] : (i64) -> ()
  ^bb9(%76: i64):  // 2 preds: ^bb8, ^bb12
    %77 = "llvm.lshr"(%76, %5) : (i64, i64) -> i64
    %78 = "llvm.and"(%76, %6) : (i64, i64) -> i64
    %79 = "llvm.icmp"(%78, %15) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %80 = "llvm.getelementptr"(%30, %77) <{elem_type = i64, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %81 = "llvm.load"(%80) <{alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %82 = "llvm.lshr"(%81, %78) : (i64, i64) -> i64
    "llvm.cond_br"(%79, %82)[^bb11, ^bb10] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i64) -> ()
  ^bb10:  // pred: ^bb9
    %83 = "llvm.getelementptr"(%80, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %84 = "llvm.load"(%83) <{alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %85 = "llvm.sub"(%4, %76) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %86 = "llvm.and"(%85, %6) : (i64, i64) -> i64
    %87 = "llvm.shl"(%84, %86) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %88 = "llvm.or"(%87, %82) : (i64, i64) -> i64
    "llvm.br"(%88)[^bb11] : (i64) -> ()
  ^bb11(%89: i64):  // 2 preds: ^bb9, ^bb10
    %90 = "llvm.and"(%89, %16) : (i64, i64) -> i64
    %91 = "llvm.add"(%90, %75) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %92 = "llvm.and"(%91, %10) : (i64, i64) -> i64
    %93 = "llvm.icmp"(%92, %4) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%93)[^bb12, ^bb13] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb12:  // pred: ^bb11
    %94 = "llvm.add"(%76, %10) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %95 = "llvm.icmp"(%94, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%95, %94)[^bb14, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
  ^bb13:  // pred: ^bb11
    %96 = "llvm.icmp"(%91, %17) <{predicate = 8 : i64}> : (i64, i64) -> i1
    %97 = "llvm.trunc"(%91) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %98 = "llvm.zext"(%96) : (i1) -> i64
    %99 = "llvm.getelementptr"(%40, %76) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%97, %99) <{alias_scopes = [#alias_scope4], alignment = 1 : i64, noalias_scopes = [#alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %100 = "llvm.add"(%76, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %101 = "llvm.icmp"(%76, %18) <{predicate = 6 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%101, %100, %98)[^bb8, ^bb14] <{operandSegmentSizes = array<i32: 1, 2, 0>}> : (i1, i64, i64) -> ()
  ^bb14:  // 2 preds: ^bb12, ^bb13
    "llvm.intr.lifetime.end"(%30) : (!llvm.ptr) -> ()
    "llvm.br"(%2)[^bb15] : (i64) -> ()
  ^bb15(%102: i64):  // 2 preds: ^bb14, ^bb17
    %103 = "llvm.add"(%102, %19) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %104 = "llvm.getelementptr"(%41, %103) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %105 = "llvm.load"(%104) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %106 = "llvm.icmp"(%105, %1) <{predicate = 0 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%106)[^bb17, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb16:  // 2 preds: ^bb15, ^bb17
    "llvm.intr.lifetime.start"(%39) : (!llvm.ptr) -> ()
    "llvm.call"(%39, %arg2) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 1280 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<1280 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs0_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable5NtNtNtNtB7_7backend6serial12curve_models20ProjectiveNielsPointEINtNtCsgxBkk5gSRhY_4core7convert4FromRNtNtB7_7edwards12EdwardsPointE4from, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%38) : (!llvm.ptr) -> ()
    "llvm.intr.memset"(%38, %1, %20) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    %107 = "llvm.getelementptr"(%38, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%107, %21, %20) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %108 = "llvm.getelementptr"(%38, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%108, %21, %20) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %109 = "llvm.getelementptr"(%37, %23) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %110 = "llvm.getelementptr"(%37, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %111 = "llvm.getelementptr"(%37, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %112 = "llvm.getelementptr"(%36, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %113 = "llvm.getelementptr"(%36, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %114 = "llvm.getelementptr"(%36, %23) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %115 = "llvm.getelementptr"(%35, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %116 = "llvm.getelementptr"(%35, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %117 = "llvm.getelementptr"(%35, %23) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %118 = "llvm.getelementptr"(%34, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %119 = "llvm.getelementptr"(%34, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %120 = "llvm.getelementptr"(%34, %23) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %121 = "llvm.getelementptr"(%33, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %122 = "llvm.getelementptr"(%33, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %123 = "llvm.getelementptr"(%33, %23) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %124 = "llvm.getelementptr"(%32, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %125 = "llvm.getelementptr"(%32, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.br"(%103)[^bb18] : (i64) -> ()
  ^bb17:  // pred: ^bb15
    %126 = "llvm.getelementptr"(%40, %103) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %127 = "llvm.load"(%126) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %128 = "llvm.icmp"(%127, %1) <{predicate = 1 : i64}> : (i8, i8) -> i1
    %129 = "llvm.icmp"(%103, %4) <{predicate = 0 : i64}> : (i64, i64) -> i1
    %130 = "llvm.or"(%128, %129) : (i1, i1) -> i1
    "llvm.cond_br"(%130, %103)[^bb16, ^bb15] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
  ^bb18(%131: i64):  // 2 preds: ^bb16, ^bb35
    "llvm.intr.lifetime.start"(%37) : (!llvm.ptr) -> ()
    "llvm.call"(%37, %38) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<160 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 120 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvMsa_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_15ProjectivePoint6double, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, !llvm.ptr) -> ()
    %132 = "llvm.getelementptr"(%41, %131) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %133 = "llvm.load"(%132) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %134 = "llvm.intr.scmp"(%133, %1) : (i8, i8) -> i8
    "llvm.switch"(%134)[^bb19, ^bb20, ^bb26, ^bb21] <{case_operand_segments = array<i32: 0, 0, 0>, case_values = dense<[-1, 0, 1]> : vector<3xi8>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i8) -> ()
  ^bb19:  // 2 preds: ^bb18, ^bb26
    "llvm.unreachable"() : () -> ()
  ^bb20:  // pred: ^bb18
    "llvm.intr.lifetime.start"(%35) : (!llvm.ptr) -> ()
    "llvm.call"(%35, %37, %109) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope8, #alias_scope9], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.call"(%115, %110, %111) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope8, #alias_scope9], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.call"(%116, %111, %109) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope8, #alias_scope9], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.call"(%117, %37, %110) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope8, #alias_scope9], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    %135 = "llvm.sub"(%1, %133) <{overflowFlags = 0 : i32}> : (i8, i8) -> i8
    %136 = "llvm.sext"(%135) : (i8) -> i64
    %137 = "llvm.lshr"(%136, %10) : (i64, i64) -> i64
    %138 = "llvm.icmp"(%135, %24) <{predicate = 6 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%138)[^bb22, ^bb23] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb21:  // pred: ^bb18
    "llvm.intr.lifetime.start"(%36) : (!llvm.ptr) -> ()
    "llvm.call"(%36, %37, %109) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope10, #alias_scope11], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.call"(%112, %110, %111) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope10, #alias_scope11], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.call"(%113, %111, %109) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope10, #alias_scope11], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.call"(%114, %37, %110) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope10, #alias_scope11], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    %139 = "llvm.sext"(%133) : (i8) -> i64
    %140 = "llvm.lshr"(%139, %10) : (i64, i64) -> i64
    %141 = "llvm.icmp"(%133, %24) <{predicate = 6 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%141)[^bb24, ^bb25] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb22:  // pred: ^bb20
    %142 = "llvm.getelementptr"(%39, %137) <{elem_type = !llvm.struct<"backend::serial::curve_models::ProjectiveNielsPoint", (struct<"backend::serial::u64::field::FieldElement51", (array<5 x i64>)>, struct<"backend::serial::u64::field::FieldElement51", (array<5 x i64>)>, struct<"backend::serial::u64::field::FieldElement51", (array<5 x i64>)>, struct<"backend::serial::u64::field::FieldElement51", (array<5 x i64>)>)>, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%37, %35, %142) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<160 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXsc_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB5_20ProjectiveNielsPointE3sub, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%35) : (!llvm.ptr) -> ()
    "llvm.br"()[^bb26] : () -> ()
  ^bb23:  // pred: ^bb20
    "llvm.call"(%137, %8, %25) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.noalias, llvm.nofree, llvm.noundef, llvm.readonly}], callee = @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check, fastmathFlags = #llvm.fastmath<none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, !llvm.ptr) -> ()
    "llvm.unreachable"() : () -> ()
  ^bb24:  // pred: ^bb21
    %143 = "llvm.getelementptr"(%39, %140) <{elem_type = !llvm.struct<"backend::serial::curve_models::ProjectiveNielsPoint", (struct<"backend::serial::u64::field::FieldElement51", (array<5 x i64>)>, struct<"backend::serial::u64::field::FieldElement51", (array<5 x i64>)>, struct<"backend::serial::u64::field::FieldElement51", (array<5 x i64>)>, struct<"backend::serial::u64::field::FieldElement51", (array<5 x i64>)>)>, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%37, %36, %143) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<160 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXsb_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB5_20ProjectiveNielsPointE3add, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%36) : (!llvm.ptr) -> ()
    "llvm.br"()[^bb26] : () -> ()
  ^bb25:  // pred: ^bb21
    "llvm.call"(%140, %8, %25) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.noalias, llvm.nofree, llvm.noundef, llvm.readonly}], callee = @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check, fastmathFlags = #llvm.fastmath<none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, !llvm.ptr) -> ()
    "llvm.unreachable"() : () -> ()
  ^bb26:  // 3 preds: ^bb18, ^bb22, ^bb24
    %144 = "llvm.getelementptr"(%40, %131) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %145 = "llvm.load"(%144) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %146 = "llvm.intr.scmp"(%145, %1) : (i8, i8) -> i8
    "llvm.switch"(%146)[^bb19, ^bb27, ^bb28, ^bb29] <{case_operand_segments = array<i32: 0, 0, 0>, case_values = dense<[-1, 0, 1]> : vector<3xi8>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i8) -> ()
  ^bb27:  // pred: ^bb26
    "llvm.intr.lifetime.start"(%33) : (!llvm.ptr) -> ()
    "llvm.call"(%33, %37, %109) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope12, #alias_scope13], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.call"(%121, %110, %111) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope12, #alias_scope13], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.call"(%122, %111, %109) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope12, #alias_scope13], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.call"(%123, %37, %110) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope12, #alias_scope13], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    %147 = "llvm.sub"(%1, %145) <{overflowFlags = 0 : i32}> : (i8, i8) -> i8
    %148 = "llvm.sext"(%147) : (i8) -> i64
    %149 = "llvm.lshr"(%148, %10) : (i64, i64) -> i64
    %150 = "llvm.icmp"(%147, %26) <{predicate = 4 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%150)[^bb30, ^bb31] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb28:  // 3 preds: ^bb26, ^bb30, ^bb32
    "llvm.intr.lifetime.start"(%32) : (!llvm.ptr) -> ()
    "llvm.call"(%32, %37, %109) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope14, #alias_scope15], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 120 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.call"(%124, %110, %111) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope14, #alias_scope15], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.call"(%125, %111, %109) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope14, #alias_scope15], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%38, %32, %23) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 120 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 120 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%32) : (!llvm.ptr) -> ()
    %151 = "llvm.icmp"(%131, %4) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%151)[^bb34, ^bb35] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb29:  // pred: ^bb26
    "llvm.intr.lifetime.start"(%34) : (!llvm.ptr) -> ()
    "llvm.call"(%34, %37, %109) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope16, #alias_scope17], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.call"(%118, %110, %111) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope16, #alias_scope17], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.call"(%119, %111, %109) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope16, #alias_scope17], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.call"(%120, %37, %110) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope16, #alias_scope17], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    %152 = "llvm.sext"(%145) : (i8) -> i64
    %153 = "llvm.lshr"(%152, %10) : (i64, i64) -> i64
    %154 = "llvm.icmp"(%145, %26) <{predicate = 4 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%154)[^bb32, ^bb33] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb30:  // pred: ^bb27
    %155 = "llvm.getelementptr"(%29, %149) <{elem_type = !llvm.struct<"backend::serial::curve_models::AffineNielsPoint", (struct<"backend::serial::u64::field::FieldElement51", (array<5 x i64>)>, struct<"backend::serial::u64::field::FieldElement51", (array<5 x i64>)>, struct<"backend::serial::u64::field::FieldElement51", (array<5 x i64>)>)>, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%37, %33, %155) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<160 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 120 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXse_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB5_16AffineNielsPointE3sub, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%33) : (!llvm.ptr) -> ()
    "llvm.br"()[^bb28] : () -> ()
  ^bb31:  // pred: ^bb27
    "llvm.call"(%149, %27, %28) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.noalias, llvm.nofree, llvm.noundef, llvm.readonly}], callee = @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check, fastmathFlags = #llvm.fastmath<none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, !llvm.ptr) -> ()
    "llvm.unreachable"() : () -> ()
  ^bb32:  // pred: ^bb29
    %156 = "llvm.getelementptr"(%29, %153) <{elem_type = !llvm.struct<"backend::serial::curve_models::AffineNielsPoint", (struct<"backend::serial::u64::field::FieldElement51", (array<5 x i64>)>, struct<"backend::serial::u64::field::FieldElement51", (array<5 x i64>)>, struct<"backend::serial::u64::field::FieldElement51", (array<5 x i64>)>)>, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%37, %34, %156) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<160 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 120 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXsd_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB5_16AffineNielsPointE3add, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%34) : (!llvm.ptr) -> ()
    "llvm.br"()[^bb28] : () -> ()
  ^bb33:  // pred: ^bb29
    "llvm.call"(%153, %27, %28) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.noalias, llvm.nofree, llvm.noundef, llvm.readonly}], callee = @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check, fastmathFlags = #llvm.fastmath<none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, !llvm.ptr) -> ()
    "llvm.unreachable"() : () -> ()
  ^bb34:  // pred: ^bb28
    "llvm.intr.lifetime.end"(%37) : (!llvm.ptr) -> ()
    "llvm.call"(%arg0, %38, %108) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope18, #alias_scope19], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 120 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    %157 = "llvm.getelementptr"(%arg0, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%157, %107, %108) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope18, #alias_scope19], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    %158 = "llvm.getelementptr"(%arg0, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%158, %108, %0) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope18, #alias_scope19], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noundef}], callee = @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    %159 = "llvm.getelementptr"(%arg0, %23) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%159, %38, %107) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, alias_scopes = [#alias_scope18, #alias_scope19], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 120 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%38) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%39) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%40) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%41) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  ^bb35:  // pred: ^bb28
    %160 = "llvm.add"(%131, %19) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    "llvm.intr.lifetime.end"(%37) : (!llvm.ptr) -> ()
    "llvm.br"(%160)[^bb18] : (i64) -> ()
}

def program (p : Primitives) (g : Globals) : Except String Func :=
  translate region p.resolve g.resolve

end

end Agave.Ed25519.DoubleBase.SerialCFG
