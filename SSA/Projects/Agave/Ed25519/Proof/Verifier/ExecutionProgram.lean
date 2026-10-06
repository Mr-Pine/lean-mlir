module

public import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionElab

/-! Exact pinned verifier regions. Regenerate with MLIR/import_verifier.py.

Only required symbol-name quoting changes the source spelling. `execution_def`
checks successful RIR translation, including calls and globals; it
does not supply any primitive's semantics or prove an execution result.
The original wrapper did not contain the body of `verify_dalek`; the
supplemental extraction now provides that body and its key/SHA helpers.
-/

namespace Agave.Ed25519.Verifier.Execution

open LeanMLIR.RIR
@[expose] public section

namespace Wrapper

structure Primitives where
  /-- Exact external symbol `_RNvXs8_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKeyINtNtCsgxBkk5gSRhY_4core7convert7TryFromNtB5_20VerificationKeyBytesE8try_from`. -/
  keyFromBytes : Vals [.ptr, .ptr] → EffectM (Vals [])
  /-- Exact external symbol `_RNvMCsgDXCIgPwL6d_7ed25519NtB2_9Signature10from_bytes`. -/
  signatureFromBytes : Vals [.ptr, .ptr] → EffectM (Vals [])
  /-- Exact external symbol `_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey12verify_dalek`. -/
  verifyDalek : Vals [.ptr, .ptr, .ptr, .bv 64] → EffectM (Vals [.bv 8])

def Primitives.resolve (p : Primitives) : String → Option Callee
  | "_RNvXs8_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKeyINtNtCsgxBkk5gSRhY_4core7convert7TryFromNtB5_20VerificationKeyBytesE8try_from" => some ⟨[.ptr, .ptr], [], p.keyFromBytes⟩
  | "_RNvMCsgDXCIgPwL6d_7ed25519NtB2_9Signature10from_bytes" => some ⟨[.ptr, .ptr], [], p.signatureFromBytes⟩
  | "_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey12verify_dalek" => some ⟨[.ptr, .ptr, .ptr, .bv 64], [.bv 8], p.verifyDalek⟩
  | _ => none

execution_def program (p : Primitives) :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 192 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    %4 = "llvm.mlir.constant"() <{value = false}> : () -> i1
    %5 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<64 x i8>}> : (i32) -> !llvm.ptr
    %6 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<200 x i8>}> : (i32) -> !llvm.ptr
    %7 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<192 x i8>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%6) : (!llvm.ptr) -> ()
    "llvm.call"(%6, %arg0) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 200 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<200 x i8>}, {llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs8_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKeyINtNtCsgxBkk5gSRhY_4core7convert7TryFromNtB5_20VerificationKeyBytesE8try_from, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, !llvm.ptr) -> ()
    %8 = "llvm.load"(%6) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %9 = "llvm.trunc"(%8) <{overflowFlags = 2 : i32}> : (i8) -> i1
    "llvm.cond_br"(%9)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    "llvm.intr.lifetime.end"(%6) : (!llvm.ptr) -> ()
    "llvm.br"(%4)[^bb3] : (i1) -> ()
  ^bb2:  // pred: ^bb0
    "llvm.intr.lifetime.start"(%7) : (!llvm.ptr) -> ()
    %10 = "llvm.getelementptr"(%6, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%7, %10, %2) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 192 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 192 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%6) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%5) : (!llvm.ptr) -> ()
    "llvm.call"(%5, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 64 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<64 x i8>}, {llvm.dereferenceable = 64 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvMCsgDXCIgPwL6d_7ed25519NtB2_9Signature10from_bytes, fastmathFlags = #llvm.fastmath<none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, !llvm.ptr) -> ()
    %11 = "llvm.call"(%7, %5, %arg2, %arg3) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 192 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.dereferenceable = 64 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noundef}], callee = @_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey12verify_dalek, fastmathFlags = #llvm.fastmath<none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 4, 0>, res_attrs = [{llvm.noundef}]}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, i64) -> i8
    %12 = "llvm.icmp"(%11, %3) <{predicate = 0 : i64}> : (i8, i8) -> i1
    "llvm.intr.lifetime.end"(%5) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%7) : (!llvm.ptr) -> ()
    "llvm.br"(%12)[^bb3] : (i1) -> ()
  ^bb3(%13: i1):  // 2 preds: ^bb1, ^bb2
    "llvm.return"(%13) : (i1) -> ()
}
with @_RNvXs8_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKeyINtNtCsgxBkk5gSRhY_4core7convert7TryFromNtB5_20VerificationKeyBytesE8try_from := p.keyFromBytes,
  @_RNvMCsgDXCIgPwL6d_7ed25519NtB2_9Signature10from_bytes := p.signatureFromBytes,
  @_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey12verify_dalek := p.verifyDalek

theorem block_count (p : Primitives) : (program p).n = 4 := rfl

end Wrapper

namespace Dalek

structure Primitives where
  /-- Exact external symbol `_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey16challenge_scalar`. -/
  challengeScalar : Vals [.ptr, .ptr, .ptr, .ptr, .bv 64] → EffectM (Vals [])
  /-- Exact external symbol `_RNvMsx_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint12mul_by_pow_2`. -/
  pointMulByPow2 : Vals [.ptr, .ptr, .bv 32] → EffectM (Vals [])
  /-- Exact external symbol `_RNvXsd_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPointNtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq`. -/
  pointConstantTimeEq : Vals [.ptr, .ptr] → EffectM (Vals [.bv 8])
  /-- Exact external symbol `_RNvMs2_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_18CompressedEdwardsY10decompress`. -/
  decompress : Vals [.ptr, .ptr] → EffectM (Vals [])
  /-- Exact external symbol `_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519`. -/
  blackBoxByte : Vals [.bv 8] → EffectM (Vals [.bv 8])
  /-- Exact external symbol `_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar6reduce`. -/
  scalarReduce : Vals [.ptr, .ptr] → EffectM (Vals [])
  /-- Exact external symbol `_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519`. -/
  bytesConstantTimeEq : Vals [.ptr, .ptr] → EffectM (Vals [.bv 8])
  /-- Exact external symbol `_RNvNvNtNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend10cpuid_avx28init_get10init_inner`. -/
  initializeAvx2Cache : Vals [] → EffectM (Vals [.bv 1])
  /-- Exact external symbol `_RNvNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial10scalar_mul19vartime_double_base3mul`. -/
  serialDoubleBase : Vals [.ptr, .ptr, .ptr, .ptr] → EffectM (Vals [])
  /-- Exact external symbol `_RNvNvNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector10scalar_mul19vartime_double_base9spec_avx23mul9__impl_mul`. -/
  avx2DoubleBase : Vals [.ptr, .ptr, .ptr, .ptr] → EffectM (Vals [])
  /-- Exact external symbol `_RNvMsg_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint8compress`. -/
  compressPoint : Vals [.ptr, .ptr] → EffectM (Vals [])
  /-- Exact external symbol `bcmp`. -/
  compareBytes : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [.bv 32])

def Primitives.resolve (p : Primitives) : String → Option Callee
  | "_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey16challenge_scalar" => some ⟨[.ptr, .ptr, .ptr, .ptr, .bv 64], [], p.challengeScalar⟩
  | "_RNvMsx_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint12mul_by_pow_2" => some ⟨[.ptr, .ptr, .bv 32], [], p.pointMulByPow2⟩
  | "_RNvXsd_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPointNtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq" => some ⟨[.ptr, .ptr], [.bv 8], p.pointConstantTimeEq⟩
  | "_RNvMs2_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_18CompressedEdwardsY10decompress" => some ⟨[.ptr, .ptr], [], p.decompress⟩
  | "_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519" => some ⟨[.bv 8], [.bv 8], p.blackBoxByte⟩
  | "_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar6reduce" => some ⟨[.ptr, .ptr], [], p.scalarReduce⟩
  | "_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519" => some ⟨[.ptr, .ptr], [.bv 8], p.bytesConstantTimeEq⟩
  | "_RNvNvNtNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend10cpuid_avx28init_get10init_inner" => some ⟨[], [.bv 1], p.initializeAvx2Cache⟩
  | "_RNvNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial10scalar_mul19vartime_double_base3mul" => some ⟨[.ptr, .ptr, .ptr, .ptr], [], p.serialDoubleBase⟩
  | "_RNvNvNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector10scalar_mul19vartime_double_base9spec_avx23mul9__impl_mul" => some ⟨[.ptr, .ptr, .ptr, .ptr], [], p.avx2DoubleBase⟩
  | "_RNvMsg_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint8compress" => some ⟨[.ptr, .ptr], [], p.compressPoint⟩
  | "bcmp" => some ⟨[.ptr, .ptr, .bv 64], [.bv 32], p.compareBytes⟩
  | _ => none

structure Globals where
  /-- `alloc_d6091242425a18f93aa551ed73483e0d`; initializer and mutability are separate memory obligations. -/
  address0 : Pointer
  /-- `_RNvNtNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend10cpuid_avx27STORAGE`; initializer and mutability are separate memory obligations. -/
  address1 : Pointer

def Globals.resolve (g : Globals) : String → Option Pointer
  | "alloc_d6091242425a18f93aa551ed73483e0d" => some g.address0
  | "_RNvNtNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend10cpuid_avx27STORAGE" => some g.address1
  | _ => none

execution_def program (p : Primitives) (g : Globals) :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %4 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %5 = "llvm.mlir.addressof"() <{global_name = @alloc_d6091242425a18f93aa551ed73483e0d}> : () -> !llvm.ptr
    %6 = "llvm.mlir.constant"() <{value = 80 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 120 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 2 : i8}> : () -> i8
    %9 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 160 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 63 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    %14 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %15 = "llvm.mlir.constant"() <{value = 33 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %18 = "llvm.mlir.addressof"() <{global_name = @_RNvNtNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend10cpuid_avx27STORAGE}> : () -> !llvm.ptr
    %19 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %20 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<32 x i8>}> : (i32) -> !llvm.ptr
    %21 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %22 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %23 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %24 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %25 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %26 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<32 x i8>}> : (i32) -> !llvm.ptr
    %27 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<32 x i8>}> : (i32) -> !llvm.ptr
    %28 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<168 x i8>}> : (i32) -> !llvm.ptr
    %29 = "llvm.alloca"(%0) <{alignment = 2 : i64, elem_type = !llvm.array<166 x i8>}> : (i32) -> !llvm.ptr
    %30 = "llvm.alloca"(%0) <{alignment = 2 : i64, elem_type = !llvm.array<166 x i8>}> : (i32) -> !llvm.ptr
    %31 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %32 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<32 x i8>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%32) : (!llvm.ptr) -> ()
    "llvm.call"(%32, %arg0, %arg1, %arg2, %arg3) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nofree, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 192 : i64, llvm.noalias, llvm.nofree, llvm.noundef, llvm.readonly}, {llvm.dereferenceable = 64 : i64, llvm.noalias, llvm.nofree, llvm.noundef, llvm.readonly}, {llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noundef}], callee = @_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey16challenge_scalar, fastmathFlags = #llvm.fastmath<none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 5, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, i64) -> ()
    %33 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%24) : (!llvm.ptr) -> ()
    "llvm.call"(%24, %33, %2) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<160 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noundef}], callee = @_RNvMsx_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint12mul_by_pow_2, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope, #alias_scope1], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    "llvm.intr.lifetime.start"(%23) : (!llvm.ptr) -> ()
    "llvm.intr.memset"(%23, %3, %4) <{alias_scopes = [#alias_scope2], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false, noalias_scopes = [#alias_scope3, #alias_scope4, #alias_scope5, #alias_scope, #alias_scope1]}> : (!llvm.ptr, i8, i64) -> ()
    %34 = "llvm.getelementptr"(%23, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%34, %5, %4) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope3, #alias_scope4, #alias_scope5, #alias_scope, #alias_scope1]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %35 = "llvm.getelementptr"(%23, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%35, %5, %4) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope3, #alias_scope4, #alias_scope5, #alias_scope, #alias_scope1]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %36 = "llvm.getelementptr"(%23, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memset"(%36, %3, %4) <{alias_scopes = [#alias_scope2], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false, noalias_scopes = [#alias_scope3, #alias_scope4, #alias_scope5, #alias_scope, #alias_scope1]}> : (!llvm.ptr, i8, i64) -> ()
    %37 = "llvm.call"(%24, %23) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXsd_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPointNtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = read, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope4, #alias_scope5, #alias_scope, #alias_scope1], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>, res_attrs = [{llvm.noundef}]}> : (!llvm.ptr, !llvm.ptr) -> i8
    %38 = "llvm.icmp"(%37, %3) <{predicate = 0 : i64}> : (i8, i8) -> i1
    "llvm.intr.lifetime.end"(%23) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%24) : (!llvm.ptr) -> ()
    "llvm.cond_br"(%38, %8)[^bb1, ^bb13] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i8) -> ()
  ^bb1:  // pred: ^bb0
    "llvm.intr.lifetime.start"(%31) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%30) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%29) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%28) : (!llvm.ptr) -> ()
    "llvm.call"(%28, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 168 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<168 x i8>}, {llvm.dereferenceable = 64 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_18CompressedEdwardsY10decompress, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope5, #alias_scope1], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, !llvm.ptr) -> ()
    %39 = "llvm.load"(%28) <{alignment = 8 : i64, noalias_scopes = [#alias_scope5, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %40 = "llvm.trunc"(%39) <{overflowFlags = 2 : i32}> : (i64) -> i1
    "llvm.cond_br"(%40)[^bb2, ^bb3] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb2:  // pred: ^bb1
    %41 = "llvm.getelementptr"(%28, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %42 = "llvm.getelementptr"(%29, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%42, %41, %11) <{arg_attrs = [{llvm.align = 2 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope5, #alias_scope, #alias_scope1]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%28) : (!llvm.ptr) -> ()
    %43 = "llvm.getelementptr"(%30, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%43, %42, %11) <{arg_attrs = [{llvm.align = 2 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 2 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope5, #alias_scope, #alias_scope1]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%29) : (!llvm.ptr) -> ()
    "llvm.intr.memcpy"(%31, %43, %11) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 2 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope5, #alias_scope, #alias_scope1]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%30) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%22) : (!llvm.ptr) -> ()
    "llvm.call"(%22, %31, %2) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<160 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noundef}], callee = @_RNvMsx_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint12mul_by_pow_2, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope5, #alias_scope, #alias_scope1], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    "llvm.intr.lifetime.start"(%21) : (!llvm.ptr) -> ()
    "llvm.intr.memset"(%21, %3, %4) <{alias_scopes = [#alias_scope6], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false, noalias_scopes = [#alias_scope7, #alias_scope8, #alias_scope5, #alias_scope, #alias_scope1]}> : (!llvm.ptr, i8, i64) -> ()
    %44 = "llvm.getelementptr"(%21, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%44, %5, %4) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope7, #alias_scope8, #alias_scope5, #alias_scope, #alias_scope1]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %45 = "llvm.getelementptr"(%21, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%45, %5, %4) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope7, #alias_scope8, #alias_scope5, #alias_scope, #alias_scope1]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %46 = "llvm.getelementptr"(%21, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memset"(%46, %3, %4) <{alias_scopes = [#alias_scope6], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false, noalias_scopes = [#alias_scope7, #alias_scope8, #alias_scope5, #alias_scope, #alias_scope1]}> : (!llvm.ptr, i8, i64) -> ()
    %47 = "llvm.call"(%22, %21) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXsd_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPointNtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = read, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope8, #alias_scope5, #alias_scope, #alias_scope1], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>, res_attrs = [{llvm.noundef}]}> : (!llvm.ptr, !llvm.ptr) -> i8
    %48 = "llvm.icmp"(%47, %3) <{predicate = 0 : i64}> : (i8, i8) -> i1
    "llvm.intr.lifetime.end"(%21) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%22) : (!llvm.ptr) -> ()
    "llvm.cond_br"(%48, %8)[^bb4, ^bb12] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i8) -> ()
  ^bb3:  // pred: ^bb1
    "llvm.intr.lifetime.end"(%28) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%29) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%30) : (!llvm.ptr) -> ()
    "llvm.br"(%8)[^bb12] : (i8) -> ()
  ^bb4:  // pred: ^bb2
    "llvm.intr.lifetime.start"(%27) : (!llvm.ptr) -> ()
    %49 = "llvm.getelementptr"(%arg1, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %50 = "llvm.load"(%49) <{alignment = 1 : i64, noalias_scopes = [#alias_scope5, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %51 = "llvm.getelementptr"(%arg1, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %52 = "llvm.load"(%51) <{alignment = 1 : i64, noalias_scopes = [#alias_scope5, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %53 = "llvm.icmp"(%52, %13) <{predicate = 4 : i64}> : (i8, i8) -> i1
    %54 = "llvm.zext"(%53) : (i1) -> i8
    %55 = "llvm.call"(%54) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    "llvm.intr.lifetime.start"(%20) : (!llvm.ptr) -> ()
    "llvm.call"(%20, %49) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nofree, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar6reduce, fastmathFlags = #llvm.fastmath<none>, no_unwind, noalias_scopes = [#alias_scope5, #alias_scope1], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, !llvm.ptr) -> ()
    %56 = "llvm.call"(%49, %20) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, inline_hint, memory_effects = #llvm.memory_effects<other = none, argMem = read, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>, res_attrs = [{llvm.noundef}]}> : (!llvm.ptr, !llvm.ptr) -> i8
    "llvm.intr.lifetime.end"(%20) : (!llvm.ptr) -> ()
    %57 = "llvm.and"(%56, %55) : (i8, i8) -> i8
    %58 = "llvm.call"(%57) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %59 = "llvm.icmp"(%58, %14) <{predicate = 0 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%59)[^bb5, ^bb11] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb5:  // pred: ^bb4
    %60 = "llvm.getelementptr"(%arg1, %15) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %61 = "llvm.getelementptr"(%27, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%61, %60, %17) <{arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 31 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 31 : i64, llvm.nonnull, llvm.noundef, llvm.readonly}, {}], isVolatile = false, noalias_scopes = [#alias_scope5, #alias_scope1]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.store"(%50, %27) <{alignment = 1 : i64, noalias_scopes = [#alias_scope5, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%26) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%25) : (!llvm.ptr) -> ()
    %62 = "llvm.load"(%18) <{alignment = 1 : i64, noalias_scopes = [#alias_scope9, #alias_scope10, #alias_scope11, #alias_scope12, #alias_scope13, #alias_scope14, #alias_scope15, #alias_scope16, #alias_scope5, #alias_scope, #alias_scope1], ordering = 2 : i64}> : (!llvm.ptr) -> i8
    %63 = "llvm.icmp"(%62, %13) <{predicate = 0 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%63)[^bb6, ^bb7] <{branch_weights = array<i32: 1, 2000>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb6:  // pred: ^bb5
    %64 = "llvm.call"() <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, callee = @_RNvNvNtNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend10cpuid_avx28init_get10init_inner, fastmathFlags = #llvm.fastmath<none>, no_unwind, noalias_scopes = [#alias_scope9, #alias_scope10, #alias_scope11, #alias_scope12, #alias_scope13, #alias_scope14, #alias_scope15, #alias_scope16, #alias_scope5, #alias_scope, #alias_scope1], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 0, 0>, res_attrs = [{llvm.noundef, llvm.zeroext}]}> : () -> i1
    "llvm.br"()[^bb7] : () -> ()
  ^bb7:  // 2 preds: ^bb5, ^bb6
    %65 = "llvm.load"(%18) <{alignment = 1 : i64, noalias_scopes = [#alias_scope9, #alias_scope10, #alias_scope11, #alias_scope12, #alias_scope13, #alias_scope14, #alias_scope15, #alias_scope16, #alias_scope5, #alias_scope, #alias_scope1], ordering = 2 : i64}> : (!llvm.ptr) -> i8
    %66 = "llvm.icmp"(%65, %14) <{predicate = 0 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%66)[^bb9, ^bb8] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb8:  // pred: ^bb7
    "llvm.call"(%25, %32, %33, %27) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial10scalar_mul19vartime_double_base3mul, fastmathFlags = #llvm.fastmath<none>, no_unwind, noalias_scopes = [#alias_scope], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 4, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.br"()[^bb10] : () -> ()
  ^bb9:  // pred: ^bb7
    "llvm.call"(%25, %32, %33, %27) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvNvNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector10scalar_mul19vartime_double_base9spec_avx23mul9__impl_mul, fastmathFlags = #llvm.fastmath<none>, no_unwind, noalias_scopes = [#alias_scope], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 4, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.br"()[^bb10] : () -> ()
  ^bb10:  // 2 preds: ^bb8, ^bb9
    "llvm.call"(%26, %25) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<32 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvMsg_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint8compress, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope5, #alias_scope, #alias_scope1], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%25) : (!llvm.ptr) -> ()
    %67 = "llvm.call"(%26, %arg1, %1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {llvm.dereferenceable = 64 : i64, llvm.nonnull, llvm.noundef, llvm.readonly}, {}], callee = @bcmp, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = read, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, noalias_scopes = [#alias_scope5, #alias_scope1], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i64) -> i32
    %68 = "llvm.icmp"(%67, %19) <{predicate = 0 : i64}> : (i32, i32) -> i1
    %69 = "llvm.select"(%68, %13, %8) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, i8, i8) -> i8
    "llvm.intr.lifetime.end"(%26) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%27) : (!llvm.ptr) -> ()
    "llvm.br"(%69)[^bb12] : (i8) -> ()
  ^bb11:  // pred: ^bb4
    "llvm.intr.lifetime.end"(%27) : (!llvm.ptr) -> ()
    "llvm.br"(%8)[^bb12] : (i8) -> ()
  ^bb12(%70: i8):  // 4 preds: ^bb2, ^bb3, ^bb10, ^bb11
    "llvm.intr.lifetime.end"(%31) : (!llvm.ptr) -> ()
    "llvm.br"(%70)[^bb13] : (i8) -> ()
  ^bb13(%71: i8):  // 2 preds: ^bb0, ^bb12
    "llvm.intr.lifetime.end"(%32) : (!llvm.ptr) -> ()
    "llvm.return"(%71) : (i8) -> ()
}
with @_RNvMsc_NtNtCsjK63O35OHGN_14solana_ed255197ed_sigs16verification_keyNtB5_15VerificationKey16challenge_scalar := p.challengeScalar,
  @_RNvMsx_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint12mul_by_pow_2 := p.pointMulByPow2,
  @_RNvXsd_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPointNtCsh8VEmffyqhs_6subtle14ConstantTimeEq5ct_eq := p.pointConstantTimeEq,
  @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_18CompressedEdwardsY10decompress := p.decompress,
  @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519 := p.blackBoxByte,
  @_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar6reduce := p.scalarReduce,
  @_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519 := p.bytesConstantTimeEq,
  @_RNvNvNtNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend10cpuid_avx28init_get10init_inner := p.initializeAvx2Cache,
  @_RNvNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial10scalar_mul19vartime_double_base3mul := p.serialDoubleBase,
  @_RNvNvNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector10scalar_mul19vartime_double_base9spec_avx23mul9__impl_mul := p.avx2DoubleBase,
  @_RNvMsg_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_12EdwardsPoint8compress := p.compressPoint,
  @bcmp := p.compareBytes
globals @alloc_d6091242425a18f93aa551ed73483e0d := g.address0,
  @_RNvNtNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend10cpuid_avx27STORAGE := g.address1

theorem block_count (p : Primitives) (g : Globals) : (program p g).n = 14 := rfl

end Dalek

namespace Key

structure Primitives where
  /-- Exact external symbol `_RNvMs2_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_18CompressedEdwardsY10decompress`. -/
  decompress : Vals [.ptr, .ptr] → EffectM (Vals [])

def Primitives.resolve (p : Primitives) : String → Option Callee
  | "_RNvMs2_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_18CompressedEdwardsY10decompress" => some ⟨[.ptr, .ptr], [], p.decompress⟩
  | _ => none

execution_def program (p : Primitives) :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %3 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 80 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 88 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 120 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 136 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 152 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = dense<[36028797018963664, 36028797018963952]> : vector<2xi64>}> : () -> vector<2xi64>
    %15 = "llvm.mlir.constant"() <{value = dense<36028797018963952> : vector<2xi64>}> : () -> vector<2xi64>
    %16 = "llvm.mlir.constant"() <{value = dense<51> : vector<2xi64>}> : () -> vector<2xi64>
    %17 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = dense<2251799813685247> : vector<2xi64>}> : () -> vector<2xi64>
    %20 = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 160 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 168 : i64}> : () -> i64
    %25 = "llvm.mlir.constant"() <{value = 184 : i64}> : () -> i64
    %26 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %27 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<168 x i8>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%27) : (!llvm.ptr) -> ()
    "llvm.call"(%27, %arg1) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 168 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<168 x i8>}, {llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_18CompressedEdwardsY10decompress, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, !llvm.ptr) -> ()
    %28 = "llvm.load"(%27) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %29 = "llvm.trunc"(%28) <{overflowFlags = 2 : i32}> : (i64) -> i1
    "llvm.cond_br"(%29)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    %30 = "llvm.getelementptr"(%27, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %31 = "llvm.getelementptr"(%27, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %32 = "llvm.getelementptr"(%27, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %33 = "llvm.getelementptr"(%27, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %34 = "llvm.getelementptr"(%arg0, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%34, %33, %8) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %35 = "llvm.getelementptr"(%27, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %36 = "llvm.getelementptr"(%arg0, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%36, %35, %8) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %37 = "llvm.getelementptr"(%27, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %38 = "llvm.getelementptr"(%27, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %39 = "llvm.getelementptr"(%27, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %40 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %41 = "llvm.getelementptr"(%arg0, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %42 = "llvm.getelementptr"(%arg0, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %43 = "llvm.load"(%30) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %44 = "llvm.load"(%31) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %45 = "llvm.sub"(%14, %43) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %46 = "llvm.sub"(%15, %44) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %47 = "llvm.lshr"(%45, %16) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %48 = "llvm.extractelement"(%45, %17) : (vector<2xi64>, i64) -> i64
    %49 = "llvm.and"(%48, %18) : (i64, i64) -> i64
    %50 = "llvm.and"(%46, %19) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %51 = "llvm.add"(%50, %47) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %52 = "llvm.getelementptr"(%arg0, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %53 = "llvm.load"(%32) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %54 = "llvm.sub"(%15, %53) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %55 = "llvm.extractelement"(%54, %1) : (vector<2xi64>, i64) -> i64
    %56 = "llvm.lshr"(%55, %21) : (i64, i64) -> i64
    %57 = "llvm.and"(%54, %19) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %58 = "llvm.mul"(%56, %22) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %59 = "llvm.shufflevector"(%46, %54) <{mask = array<i32: 1, 2>}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %60 = "llvm.lshr"(%59, %16) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %61 = "llvm.add"(%58, %49) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %62 = "llvm.add"(%57, %60) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %63 = "llvm.getelementptr"(%arg0, %23) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %64 = "llvm.getelementptr"(%arg0, %24) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %65 = "llvm.load"(%37) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %66 = "llvm.load"(%38) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %67 = "llvm.sub"(%14, %65) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %68 = "llvm.sub"(%15, %66) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %69 = "llvm.lshr"(%67, %16) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %70 = "llvm.extractelement"(%67, %17) : (vector<2xi64>, i64) -> i64
    %71 = "llvm.and"(%70, %18) : (i64, i64) -> i64
    %72 = "llvm.and"(%68, %19) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %73 = "llvm.add"(%72, %69) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %74 = "llvm.getelementptr"(%arg0, %25) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %75 = "llvm.load"(%39) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<2xi64>
    %76 = "llvm.sub"(%15, %75) <{overflowFlags = 0 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %77 = "llvm.extractelement"(%76, %1) : (vector<2xi64>, i64) -> i64
    %78 = "llvm.lshr"(%77, %21) : (i64, i64) -> i64
    %79 = "llvm.and"(%76, %19) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %80 = "llvm.mul"(%78, %22) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %81 = "llvm.shufflevector"(%68, %76) <{mask = array<i32: 1, 2>}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %82 = "llvm.lshr"(%81, %16) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %83 = "llvm.add"(%80, %71) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %84 = "llvm.add"(%79, %82) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.intr.lifetime.end"(%27) : (!llvm.ptr) -> ()
    "llvm.intr.memcpy"(%40, %arg1, %5) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.store"(%61, %41) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%51, %42) <{alignment = 8 : i64, ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    "llvm.store"(%62, %52) <{alignment = 8 : i64, ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    "llvm.store"(%83, %63) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%73, %64) <{alignment = 8 : i64, ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    "llvm.store"(%84, %74) <{alignment = 8 : i64, ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    "llvm.br"(%26)[^bb3] : (i8) -> ()
  ^bb2:  // pred: ^bb0
    "llvm.intr.lifetime.end"(%27) : (!llvm.ptr) -> ()
    %85 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%2, %85) <{alignment = 1 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    "llvm.br"(%2)[^bb3] : (i8) -> ()
  ^bb3(%86: i8):  // 2 preds: ^bb1, ^bb2
    "llvm.store"(%86, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
with @_RNvMs2_NtCsjK63O35OHGN_14solana_ed255197edwardsNtB5_18CompressedEdwardsY10decompress := p.decompress

theorem block_count (p : Primitives) : (program p).n = 4 := rfl

end Key

namespace Challenge

structure Primitives where
  /-- Exact external symbol `_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512`. -/
  sha512Compress : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [])
  /-- Exact external symbol `_RNvNtCsjK63O35OHGN_14solana_ed255197ed_sigs18scalar_from_sha512`. -/
  scalarFromSha512 : Vals [.ptr, .ptr] → EffectM (Vals [])

def Primitives.resolve (p : Primitives) : String → Option Callee
  | "_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512" => some ⟨[.ptr, .ptr, .bv 64], [], p.sha512Compress⟩
  | "_RNvNtCsjK63O35OHGN_14solana_ed255197ed_sigs18scalar_from_sha512" => some ⟨[.ptr, .ptr], [], p.scalarFromSha512⟩
  | _ => none

structure Globals where
  /-- `anon.2688bd6af3b9e90d4f6e608faea972d6.1`; initializer and mutability are separate memory obligations. -/
  address0 : Pointer

def Globals.resolve (g : Globals) : String → Option Pointer
  | "anon.2688bd6af3b9e90d4f6e608faea972d6.1" => some g.address0
  | _ => none

execution_def program (p : Primitives) (g : Globals) :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: !llvm.ptr, %arg4: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 127 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 64 : i8}> : () -> i8
    %4 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    %5 = "llvm.mlir.addressof"() <{global_name = @"anon.2688bd6af3b9e90d4f6e608faea972d6.1"}> : () -> !llvm.ptr
    %6 = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 192 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 0 : i128}> : () -> i128
    %9 = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    %10 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %11 = "llvm.mlir.constant"() <{value = 1 : i128}> : () -> i128
    %12 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 9223372036854775680 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 208 : i64}> : () -> i64
    %17 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<127 x i8>}> : (i32) -> !llvm.ptr
    %18 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<208 x i8>}> : (i32) -> !llvm.ptr
    %19 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<208 x i8>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%19) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%18) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%17) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope}> : () -> ()
    "llvm.intr.memcpy"(%17, %arg2, %1) <{alias_scopes = [#alias_scope1, #alias_scope, #alias_scope2], arg_attrs = [{llvm.align = 16 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = []}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope3}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope4}> : () -> ()
    %20 = "llvm.getelementptr"(%17, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%20, %arg1, %1) <{alias_scopes = [#alias_scope5, #alias_scope6, #alias_scope7, #alias_scope8, #alias_scope9, #alias_scope4], arg_attrs = [{llvm.align = 16 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope10, #alias_scope3]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.memcpy"(%18, %17, %2) <{alias_scopes = [#alias_scope3, #alias_scope9], arg_attrs = [{llvm.align = 16 : i64, llvm.dereferenceable = 127 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 16 : i64, llvm.dereferenceable = 127 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope4]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %21 = "llvm.getelementptr"(%18, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%3, %21) <{alias_scopes = [#alias_scope3, #alias_scope9], alignment = 1 : i64, noalias_scopes = [#alias_scope4], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %22 = "llvm.getelementptr"(%18, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%22, %5, %6) <{alias_scopes = [#alias_scope3, #alias_scope9], arg_attrs = [{llvm.align = 16 : i64, llvm.dereferenceable = 64 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 16 : i64, llvm.dereferenceable = 64 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope4]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %23 = "llvm.getelementptr"(%18, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %23) <{alias_scopes = [#alias_scope3, #alias_scope9], alignment = 16 : i64, noalias_scopes = [#alias_scope4], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%17) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope11}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope12}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope13}> : () -> ()
    %24 = "llvm.getelementptr"(%18, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope14}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope15}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope16}> : () -> ()
    %25 = "llvm.getelementptr"(%18, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %26 = "llvm.load"(%25) <{alias_scopes = [#alias_scope14, #alias_scope17, #alias_scope18], alignment = 1 : i64, noalias_scopes = [#alias_scope15, #alias_scope16, #alias_scope13, #alias_scope11, #alias_scope12], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %27 = "llvm.zext"(%26) <{nonNeg}> : (i8) -> i64
    %28 = "llvm.icmp"(%26, %9) <{predicate = 4 : i64}> : (i8, i8) -> i1
    "llvm.intr.assume"(%28) <{op_bundle_sizes = array<i32>, op_bundle_tags = []}> : (i1) -> ()
    %29 = "llvm.sub"(%4, %27) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %30 = "llvm.icmp"(%arg4, %29) <{predicate = 6 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%30)[^bb2, ^bb1] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    %31 = "llvm.icmp"(%26, %10) <{predicate = 0 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%31, %arg4, %arg3)[^bb3, ^bb4] <{operandSegmentSizes = array<i32: 1, 2, 0>}> : (i1, i64, !llvm.ptr) -> ()
  ^bb2:  // pred: ^bb0
    %32 = "llvm.getelementptr"(%18, %27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%32, %arg3, %arg4) <{alias_scopes = [#alias_scope14, #alias_scope15, #alias_scope17, #alias_scope13, #alias_scope18, #alias_scope12], arg_attrs = [{llvm.align = 1 : i64, llvm.nonnull}, {llvm.align = 1 : i64, llvm.nonnull, llvm.readonly}, {llvm.range = #llvm.constant_range<i64, 0, -9223372036854775808>}], isVolatile = false, noalias_scopes = [#alias_scope16, #alias_scope11]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %33 = "llvm.trunc"(%arg4) <{overflowFlags = 3 : i32}> : (i64) -> i8
    %34 = "llvm.add"(%26, %33) <{overflowFlags = 2 : i32}> : (i8, i8) -> i8
    "llvm.store"(%34, %25) <{alias_scopes = [#alias_scope19, #alias_scope14, #alias_scope17, #alias_scope18], alignment = 1 : i64, noalias_scopes = [#alias_scope15, #alias_scope16, #alias_scope13, #alias_scope11, #alias_scope12], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    "llvm.br"()[^bb7] : () -> ()
  ^bb3(%35: i64, %36: !llvm.ptr):  // 2 preds: ^bb1, ^bb4
    %37 = "llvm.lshr"(%35, %13) : (i64, i64) -> i64
    %38 = "llvm.and"(%35, %14) : (i64, i64) -> i64
    %39 = "llvm.and"(%35, %2) : (i64, i64) -> i64
    %40 = "llvm.getelementptr"(%36, %38) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %41 = "llvm.icmp"(%37, %15) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%41)[^bb6, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb4:  // pred: ^bb1
    %42 = "llvm.getelementptr"(%arg3, %29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %43 = "llvm.sub"(%arg4, %29) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %44 = "llvm.getelementptr"(%18, %27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%44, %arg3, %29) <{alias_scopes = [#alias_scope14, #alias_scope15, #alias_scope17, #alias_scope13, #alias_scope18, #alias_scope12], arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 1 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 1 : i64, llvm.nonnull, llvm.noundef, llvm.readonly}, {}], isVolatile = false, noalias_scopes = [#alias_scope16, #alias_scope11]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %45 = "llvm.getelementptr"(%18, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %46 = "llvm.load"(%45) <{alias_scopes = [#alias_scope16, #alias_scope17, #alias_scope18], alignment = 16 : i64, noalias_scopes = [#alias_scope20, #alias_scope14, #alias_scope15, #alias_scope13, #alias_scope11, #alias_scope12], ordering = 0 : i64}> : (!llvm.ptr) -> i128
    %47 = "llvm.add"(%46, %11) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    "llvm.store"(%47, %45) <{alias_scopes = [#alias_scope16, #alias_scope17, #alias_scope18], alignment = 16 : i64, noalias_scopes = [#alias_scope20, #alias_scope14, #alias_scope15, #alias_scope13, #alias_scope11, #alias_scope12], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    "llvm.call"(%24, %18, %12) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 16 : i64, llvm.dereferenceable = 80 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef}, {llvm.align = 16 : i64, llvm.dereferenceable = 208 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noundef}], callee = @_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512, fastmathFlags = #llvm.fastmath<none>, no_unwind, noalias_scopes = [#alias_scope15, #alias_scope13, #alias_scope11, #alias_scope12], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.br"(%43, %42)[^bb3] : (i64, !llvm.ptr) -> ()
  ^bb5:  // pred: ^bb3
    %48 = "llvm.zext"(%37) <{nonNeg}> : (i64) -> i128
    %49 = "llvm.getelementptr"(%18, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %50 = "llvm.load"(%49) <{alias_scopes = [#alias_scope16, #alias_scope17, #alias_scope18], alignment = 16 : i64, noalias_scopes = [#alias_scope21, #alias_scope14, #alias_scope15, #alias_scope13, #alias_scope11, #alias_scope12], ordering = 0 : i64}> : (!llvm.ptr) -> i128
    %51 = "llvm.add"(%50, %48) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    "llvm.store"(%51, %49) <{alias_scopes = [#alias_scope16, #alias_scope17, #alias_scope18], alignment = 16 : i64, noalias_scopes = [#alias_scope21, #alias_scope14, #alias_scope15, #alias_scope13, #alias_scope11, #alias_scope12], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    "llvm.call"(%24, %36, %37) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 16 : i64, llvm.dereferenceable = 80 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef}, {llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noundef, llvm.range = #llvm.constant_range<i64, 1, 72057594037927936>}], callee = @_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512, fastmathFlags = #llvm.fastmath<none>, no_unwind, noalias_scopes = [#alias_scope11], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.br"()[^bb6] : () -> ()
  ^bb6:  // 2 preds: ^bb3, ^bb5
    %52 = "llvm.trunc"(%39) <{overflowFlags = 3 : i32}> : (i64) -> i8
    "llvm.store"(%52, %25) <{alias_scopes = [#alias_scope22, #alias_scope14, #alias_scope17, #alias_scope18], alignment = 1 : i64, noalias_scopes = [#alias_scope15, #alias_scope16, #alias_scope13, #alias_scope11, #alias_scope12], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%18, %40, %39) <{alias_scopes = [#alias_scope14, #alias_scope15, #alias_scope17, #alias_scope13, #alias_scope18, #alias_scope12], arg_attrs = [{llvm.align = 16 : i64, llvm.dereferenceable = 208 : i64, llvm.nonnull}, {llvm.align = 1 : i64, llvm.nonnull}, {}], isVolatile = false, noalias_scopes = [#alias_scope16, #alias_scope11]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.br"()[^bb7] : () -> ()
  ^bb7:  // 2 preds: ^bb2, ^bb6
    "llvm.intr.memcpy"(%19, %18, %16) <{alias_scopes = [#alias_scope11, #alias_scope18], arg_attrs = [{llvm.align = 16 : i64, llvm.dereferenceable = 208 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 16 : i64, llvm.dereferenceable = 208 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope12]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%18) : (!llvm.ptr) -> ()
    "llvm.call"(%arg0, %19) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<32 x i8>}, {llvm.align = 16 : i64, llvm.dereferenceable = 208 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvNtCsjK63O35OHGN_14solana_ed255197ed_sigs18scalar_from_sha512, fastmathFlags = #llvm.fastmath<none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%19) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
with @_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512 := p.sha512Compress,
  @_RNvNtCsjK63O35OHGN_14solana_ed255197ed_sigs18scalar_from_sha512 := p.scalarFromSha512
globals @"anon.2688bd6af3b9e90d4f6e608faea972d6.1" := g.address0

theorem block_count (p : Primitives) (g : Globals) : (program p g).n = 8 := rfl

end Challenge

end
end Agave.Ed25519.Verifier.Execution
