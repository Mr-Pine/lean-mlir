# Allocation inventory

This is the source-hashed conservative CFG snapshot from `static-report.json`, not a proof that every read candidate is feasible or safe. Each allocation-bearing region below is in the selected roots' import closure. `Covered` means local preceding-write coverage; `Residual` means unresolved local read range or missing write; `Calls` means unresolved helper effects; `Unknown` means pointer provenance was not resolved. Lifetimes clear coverage. Counts include memcpy source reads.

| Imported region | Allocations | Covered | Residual | Calls | Unknown | Source |
|---|---:|---:|---:|---:|---:|---|
| `Bridge.FiredancerSHAExecution.Core.program` | 1 | 0 | 4 | 0 | 1 | [Program.lean](../../Bridge/FiredancerSHAExecution/Program.lean) |
| `DoubleBase.RIR.avx2Kernel` | 30 | 0 | 67 | 11 | 0 | [Avx2Program.lean](../DoubleBase/Avx2Program.lean) |
| `DoubleBase.RIR.serialKernel` | 12 | 0 | 9 | 29 | 0 | [SerialProgram.lean](../DoubleBase/SerialProgram.lean) |
| `Encoding.Compress.Execution.program` | 6 | 0 | 12 | 5 | 0 | [Program.lean](../Encoding/CompressExecution/Program.lean) |
| `Encoding.Decompress.Execution.BlackBox.program` | 1 | 1 | 0 | 0 | 0 | [BlackBoxProgram.lean](../Encoding/DecompressExecution/BlackBoxProgram.lean) |
| `Encoding.Decompress.Execution.Pow22501.program` | 20 | 0 | 1 | 21 | 0 | [Pow22501Program.lean](../Encoding/DecompressExecution/Pow22501Program.lean) |
| `Encoding.Decompress.Execution.Decode.program` | 10 | 1 | 17 | 4 | 0 | [Program.lean](../Encoding/DecompressExecution/Program.lean) |
| `Encoding.Decompress.Execution.SqrtRatio.program` | 22 | 1 | 22 | 18 | 0 | [SqrtRatioProgram.lean](../Encoding/DecompressExecution/SqrtRatioProgram.lean) |
| `NAF.RIR.kernel5` | 1 | 0 | 2 | 0 | 0 | [Program.lean](../NAF/Program.lean) |
| `NAF.RIR.kernel8` | 1 | 0 | 2 | 0 | 0 | [Program.lean](../NAF/Program.lean) |
| `SHA512.Execution.Avx2.program` | 3 | 0 | 7 | 0 | 0 | [Avx2Program.lean](../SHA512/Compression/Avx2Program.lean) |
| `Verifier.Execution.SHA512Finalization.program` | 70 | 5 | 9 | 4 | 0 | [ExecutionProgram.lean](../SHA512/ExecutionProgram.lean) |
| `ScalarReduce32.Execution.program` | 33 | 10 | 0 | 0 | 0 | [Program.lean](../ScalarReduce32/Program.lean) |
| `Verifier.Execution.ScalarWide.program` | 24 | 12 | 12 | 2 | 0 | [ExecutionProgram.lean](../ScalarWide/ExecutionProgram.lean) |
| `Verifier.Execution.ScalarMontgomeryMul.program` | 9 | 0 | 0 | 0 | 0 | [ExecutionProgram.lean](../ScalarWide/ExecutionProgram.lean) |
| `SerialPoint.affine_add` | 5 | 0 | 15 | 3 | 0 | [AffineAddProgram.lean](../SerialPoint/AffineAddProgram.lean) |
| `SerialPoint.affine_sub` | 5 | 0 | 15 | 3 | 0 | [AffineSubProgram.lean](../SerialPoint/AffineSubProgram.lean) |
| `SerialPoint.cached_add` | 6 | 0 | 20 | 4 | 0 | [CachedAddProgram.lean](../SerialPoint/CachedAddProgram.lean) |
| `SerialPoint.cached_sub` | 6 | 0 | 20 | 4 | 0 | [CachedSubProgram.lean](../SerialPoint/CachedSubProgram.lean) |
| `SerialPoint.double` | 5 | 0 | 20 | 4 | 0 | [DoubleProgram.lean](../SerialPoint/DoubleProgram.lean) |
| `Verifier.Execution.PointConstantTimeEq.program` | 8 | 0 | 20 | 6 | 0 | [PointConstantTimeEqProgram.lean](../SmallOrder/PointConstantTimeEqProgram.lean) |
| `Verifier.Execution.PointMulByPow2.program` | 4 | 0 | 1 | 9 | 0 | [PointMulByPow2Program.lean](../SmallOrder/PointMulByPow2Program.lean) |
| `Verifier.Execution.SmallOrderProjectiveDouble.program` | 5 | 0 | 20 | 4 | 0 | [SmallOrderProjectiveDoubleProgram.lean](../SmallOrder/SmallOrderProjectiveDoubleProgram.lean) |
| `Tables.Avx2Constructor.kernel` | 9 | 0 | 23 | 4 | 0 | [Avx2Constructor.lean](../Tables/Avx2Constructor.lean) |
| `Tables.SerialConstructor.kernel` | 8 | 0 | 21 | 12 | 0 | [SerialConstructor.lean](../Tables/SerialConstructor.lean) |
| `Verifier.Execution.Wrapper.program` | 3 | 0 | 2 | 3 | 0 | [ExecutionProgram.lean](../Verifier/ExecutionProgram.lean) |
| `Verifier.Execution.Dalek.program` | 13 | 0 | 4 | 12 | 0 | [ExecutionProgram.lean](../Verifier/ExecutionProgram.lean) |
| `Verifier.Execution.Key.program` | 1 | 0 | 9 | 1 | 0 | [ExecutionProgram.lean](../Verifier/ExecutionProgram.lean) |
| `Verifier.Execution.Challenge.program` | 3 | 2 | 3 | 3 | 1 | [ExecutionProgram.lean](../Verifier/ExecutionProgram.lean) |

The JSON also includes every allocation register and size, all candidate source lines and byte intervals, exact callee names, CFG blocks and convergence counts. Call footprints are deliberately not inferred from ABI attributes. A residual call does not mean that the callee is an unproved mathematical primitive; even a checked concrete RIR callee needs its byte-mask/source relation connected here.

Selected import roots:

- `SSA/Projects/Agave/Ed25519/Bridge/CrossClientReadyUnderAudit.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/CrossClientGuardedCaller.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/CrossClientCanonicalRAudit.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/CrossClientConcreteLeavesAudit.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/CrossClientPointwiseDigestAudit.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/CrossClientSHACompleteAudit.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/PointwiseVerifier.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/CrossClientBackendReadyAudit.lean`
- `SSA/Projects/Agave/Ed25519/Proof/SHA512/Compression/FinalizationDispatchCompleteAudit.lean`
- `SSA/Projects/Agave/Ed25519/Proof/Encoding/DecompressExecution/DecoderSemanticAudit.lean`
- `SSA/Projects/Agave/Ed25519/Proof/Encoding/DecompressExecution/DecoderSemanticReadyAudit.lean`
- `SSA/Projects/Agave/Ed25519/Proof/Encoding/DecompressExecution/DecoderSqrtPrefixBridgeAudit.lean`
- `SSA/Projects/Agave/Ed25519/Proof/Encoding/DecompressValidPointAudit.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/AppendAudit.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/Audit.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/CoreBulkCallAudit.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/CoreCallAudit.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/CoreInductionAudit.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/CoreMultiAudit.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/FinishCompositionAudit.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/FinishMemoryAudit.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/SemanticAdapterAudit.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/SourceAudit.lean`
- `SSA/Projects/Agave/Ed25519/Bridge/FiredancerSHAExecution/StreamSpecAudit.lean`

No requested root was missing at this snapshot. All 324 allocation sites occur in allocation-bearing regions above. The remaining literal regions have no private allocations; caller/input definedness and any external helper effects still matter.
