module

public import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionElab

/-!
The exact region of `_RNvMCsgDXCIgPwL6d_7ed25519NtB2_9Signature10from_bytes`.
This symbol is supplied by the pinned `ed25519` 2.2.3 dependency, rather than
by the complete solana-ed25519 crate IR. Its two 32-byte copies are retained.

Reproduction: in the existing extraction build, run
`cargo +1.98.1 rustc --manifest-path /tmp/ed25519-rir-extract/final/build/Cargo.toml
 --release --offline -p ed25519 -- --emit=llvm-ir`, select the exact symbol with
LLVM 22 `llvm-extract --func=... -S`, then `mlir-translate --import-llvm
--mlir-print-op-generic`. No LLVM optimization or instruction rewriting follows.

Dependency archive SHA256:
115531babc129696a58c64a4fef0a8bf9e9698629fb97e9e40767d235cfbcd53
Complete emitted dependency LLVM SHA256:
d062c0d9d10da48ad13152f086b3316c31f2ccd46b967b8c4b8bafd85f2ce637
Selected LLVM SHA256:
016df2bf66b9d0bb5436d97cbbc51a552710bef223fbe33f07f850c147cf4141
Imported MLIR SHA256:
f25dfdcfef285d2a66c95871d6e8ffc310383126ed40bf726d3965d3ca3ae98c
As an additional provenance check, the 34-byte machine-code section of this
symbol in the original pinned dependency rlib and the re-emitted rlib is
byte-identical, SHA256:
3435ca07404f316e2492ea62aa12d2347e680b6fc87c009e8eae7b9a30d3ab3b

Compilation/import remains the same trusted boundary as the other extracted
programs. The execution theorem is in `SignatureExecution`.
-/

namespace Agave.Ed25519.Verifier.Execution.Signature
open LeanMLIR.RIR
@[expose] public section

execution_def program :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %1 = "llvm.getelementptr"(%arg1, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%arg0, %arg1, %0) <{arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef, llvm.readonly}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %2 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%2, %1, %0) <{arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef, llvm.readonly}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
}

end
end Agave.Ed25519.Verifier.Execution.Signature
