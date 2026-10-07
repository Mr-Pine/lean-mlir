import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGPrepare
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGNegate
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGDifference
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGFactors
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGStores
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGCalls
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGLoads
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGCopy
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGNoops
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGTable
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseMemory

/-! Small phase boundaries for the four add/sub blocks of the actual AVX2
double-base CFG. The generated slices cover all point-vector arithmetic,
fourteen five-vector store groups, the eight field-helper calls, the interleaved
product/output loads, each first-product memcpy, lifetime instructions, the
table-row address operations and the initial cached-object reads.

`CFGBlocks` composes these intervals under explicit incoming register, memory,
table and limb invariants. The resulting block lemmas still require kernel
validation; neither umbrella claims a whole-backend proof. -/
