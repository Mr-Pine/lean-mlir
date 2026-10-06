/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.GProof
import SSA.Projects.Agave.LatticeHash.MLIR.ReductionProof
import SSA.Projects.Agave.LatticeHash.MLIR.GlobalsProof
import SSA.Projects.Agave.LatticeHash.MLIR.TransposeProof
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionExit
import SSA.Projects.Agave.LatticeHash.MLIR.PortableOutputRead
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG
import SSA.Projects.Agave.LatticeHash.MLIR.BatchOutputRead16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchEntry
import SSA.Projects.Agave.LatticeHash.MLIR.BatchEntry16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchLoads
import SSA.Projects.Agave.LatticeHash.MLIR.BatchHeader
import SSA.Projects.Agave.LatticeHash.MLIR.BatchFirstTranspose
import SSA.Projects.Agave.LatticeHash.MLIR.BatchTranspose
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRootCopy
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXof
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionProof
import SSA.Projects.Agave.LatticeHash.MLIR.CallerBatch8
import SSA.Projects.Agave.LatticeHash.MLIR.CallerBatch16
import SSA.Projects.Agave.LatticeHash.MLIR.Execution
import SSA.Projects.Agave.LatticeHash.MLIR.Integration
import SSA.Projects.Agave.LatticeHash.MLIR.PortableObservation
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofReference
import SSA.Projects.Agave.LatticeHash.MLIR.PortableShortRun
import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlaceReadback
import SSA.Projects.Agave.LatticeHash.MLIR.CallerReference
import SSA.Projects.Agave.LatticeHash.MLIR.Lifecycle8
import SSA.Projects.Agave.LatticeHash.MLIR.Reachable8
import SSA.Projects.Agave.LatticeHash.MLIR.Reachable16
import SSA.Projects.Agave.LatticeHash.MLIR.AxiomAudit

/-!
Checked compiler-emitted Agave LtHash kernels. This module includes actual
portable/AVX2/AVX512 G execution, complete portable and SIMD compress_pre
helpers (pre-feed-forward state), and matching-input three-way word readback.
For every message of at most 1024 bytes, PortableShort.short_run_exists
constructs caller memory, executes the actual portable compress_in_place and
compress_xof bodies continuously, and reads all 2048 bytes / 1024 LtHash limbs.
It derives the root descriptor. Lean supplies padded staging, call scheduling,
and flags; Rust Hasher control flow and call-frame ABI are not extracted.

Both AVX2 and AVX512 batch theorems execute their complete CFGs from retained
caller bytes and prove all 1024 accumulator u16 cells equal the independent
portable LtHash reference fold. Full-width invocation existence and refinement
are both proved.

Both SIMD lifecycle theorems cover accepted ordinary finish-or-drop traces.
Full-width calls execute MLIR; outer staging transitions remain source-shaped.
General traces require explicit serial correctness and execution-existence
premises for partial tails and long messages. Runs with no serial calls require
no serial correctness premise; explicit eight- and sixteen-message traces
construct compiled full-width flushes followed by drains. Forgotten-builder transitions are excluded.
-/
