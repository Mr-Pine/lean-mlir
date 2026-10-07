module

public import SSA.Projects.Agave.Ed25519.Proof.Avx2Cache.InitializerProgram

/-! Exact SHA-specific cache initializer quoted from the pinned SHA dependency.
The source symbol is sha2::sha512::avx2_cpuid::init_get::init_inner, distinct from
the Dalek cache initializer. Only the three CPUID assemblies and monotonic
store become explicit instruction bindings, exactly as in the checked Dalek
import. Resolving the different cache global yields equal RIR functions.

Pinned crate LLVM SHA-256: 425819f700b76e8f02b1e36fb5e2e9cdfa8bcf291c29362992abb2eba15e3136
SHA initializer original LLVM SHA-256: ff87024c7dba2f5e78540ca43ca97e0cc9e00c5ff05a52c43c1265135f5ccabb
SHA initializer extracted MLIR SHA-256: 9c392eaf0946b98c5c025d29a5a3cb43b6dfea5b731d3ca3ec813e348890586e
-/

namespace Agave.Ed25519.SHA512.Execution.Dispatch.Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions
@[expose] public section

execution_def shaInitializer (p : Primitives) (cache : Pointer) :=
{
  ^bb0:
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = 201326592 : i32}> : () -> i32
    %4 = "llvm.mlir.constant"() <{value = false}> : () -> i1
    %5 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 32 : i32}> : () -> i32
    %7 = "llvm.mlir.constant"() <{value = 268435456 : i32}> : () -> i32
    %8 = "llvm.mlir.addressof"() <{global_name = @"_RNvNtNtCs7dqAOVfn11v_4sha26sha51210avx2_cpuid7STORAGE.0"}> : () -> !llvm.ptr
    %9 = "llvm.call"(%0, %1) <{callee = @cache_instruction_cpuid}> : (i32, i32) -> !llvm.struct<(i32, i32, i32, i32)>
    %10 = "llvm.extractvalue"(%9) <{position = array<i64: 2>}> : (!llvm.struct<(i32, i32, i32, i32)>) -> i32
    %11 = "llvm.call"(%2, %1) <{callee = @cache_instruction_cpuid}> : (i32, i32) -> !llvm.struct<(i32, i32, i32, i32)>
    %12 = "llvm.call"(%2, %0) <{callee = @cache_instruction_cpuid}> : (i32, i32) -> !llvm.struct<(i32, i32, i32, i32)>
    %13 = "llvm.and"(%10, %3) : (i32, i32) -> i32
    %14 = "llvm.icmp"(%13, %3) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%14, %4)[^bb2, ^bb1] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i1) -> ()
  ^bb1(%15: i1):  // 2 preds: ^bb0, ^bb2
    %16 = "llvm.extractvalue"(%11) <{position = array<i64: 0>}> : (!llvm.struct<(i32, i32, i32, i32)>) -> i32
    %17 = "llvm.and"(%16, %6) : (i32, i32) -> i32
    %18 = "llvm.icmp"(%17, %1) <{predicate = 1 : i64}> : (i32, i32) -> i1
    %19 = "llvm.and"(%18, %15) : (i1, i1) -> i1
    %20 = "llvm.and"(%10, %7) : (i32, i32) -> i32
    %21 = "llvm.icmp"(%20, %1) <{predicate = 1 : i64}> : (i32, i32) -> i1
    %22 = "llvm.and"(%21, %19) : (i1, i1) -> i1
    %23 = "llvm.zext"(%22) : (i1) -> i8
    "llvm.call"(%23, %8) <{callee = @cache_instruction_store_monotonic}> : (i8, !llvm.ptr) -> ()
    "llvm.return"(%22) : (i1) -> ()
  ^bb2:  // pred: ^bb0
    %24 = "llvm.call"() <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<tail>, callee = @_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x865xsave7__xgetbv, fastmathFlags = #llvm.fastmath<none>, inline_hint, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 0, 0>, res_attrs = [{llvm.noundef}]}> : () -> i64
    %25 = "llvm.and"(%24, %5) : (i64, i64) -> i64
    %26 = "llvm.icmp"(%25, %5) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.br"(%26)[^bb1] : (i1) -> ()
}
with @cache_instruction_cpuid := p.cpuid,
  @_RNvNtNtNtCsgxBkk5gSRhY_4core9core_arch3x865xsave7__xgetbv := p.xgetbv,
  @cache_instruction_store_monotonic := p.storeMonotonic
globals @"_RNvNtNtCs7dqAOVfn11v_4sha26sha51210avx2_cpuid7STORAGE.0" := cache

/-- Both separately extracted CFGs have identical RIR semantics after linking
their own cache address. This is kernel equality of functions, not an assumed
hardware-dependent execution result. -/
theorem shaInitializer_eq (p : Primitives) (cache : Pointer) :
    shaInitializer p cache = initializer p cache := rfl

end
end Agave.Ed25519.SHA512.Execution.Dispatch.Finalization
