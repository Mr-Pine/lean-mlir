/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.Conformance
import SSA.Projects.Agave.LatticeHash.SerialStreaming
import SSA.Projects.Agave.LatticeHash.ForgottenOutput

/-!
Axiom-dependency regression checks for the exported conformance boundaries.
Keeping these checks together makes axiom changes explicit while proof modules
elaborate without diagnostic output.
-/

/--
info: 'AgaveConcrete.reference_eq_avx2_eq_avx512' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveConcrete.reference_eq_avx2_eq_avx512

/--
info: 'AgaveMixed.reference_eq_avx2_eq_avx512' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveMixed.reference_eq_avx2_eq_avx512

/--
info: 'AgaveMixed.returned_observable_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveMixed.returned_observable_equivalence

/--
info: 'AgavePhysicalStaging.physical_reference_eq_avx2_eq_avx512' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgavePhysicalStaging.physical_reference_eq_avx2_eq_avx512

/--
info: 'AgavePhysicalMixed.physical_reference_eq_avx2_eq_avx512' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgavePhysicalMixed.physical_reference_eq_avx2_eq_avx512

/--
info: 'AgavePhysicalMixed.returned_observable_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgavePhysicalMixed.returned_observable_equivalence

/--
info: 'AgaveOutputLog.reference_eq_avx2_eq_avx512' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveOutputLog.reference_eq_avx2_eq_avx512

/--
info: 'AgaveOutputLog.every_legal_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveOutputLog.every_legal_trace

/--
info: 'AgaveBlake3Reference.portableLtHash_eq_oneChunk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveBlake3Reference.portableLtHash_eq_oneChunk

/--
info: 'AgaveBlake3Reference.referenceHash_eq_scalarHash' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveBlake3Reference.referenceHash_eq_scalarHash

/--
info: 'AgaveBlake3Reference.publicHash_eq_portableReference' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveBlake3Reference.publicHash_eq_portableReference

/--
info: 'AgaveBlake3Reference.simdUpdate_eq_portableReference' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveBlake3Reference.simdUpdate_eq_portableReference

/--
info: 'AgaveBlake3Reference.every_legal_portable_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveBlake3Reference.every_legal_portable_trace

/--
info: 'AgaveSerialStreaming.reference_eq_avx2_eq_avx512' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveSerialStreaming.reference_eq_avx2_eq_avx512

/--
info: 'AgaveForgotten.final_outputs_pairwise_different' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveForgotten.final_outputs_pairwise_different

/--
info: 'Blake3Compression.Executable.vectorChunkBlock_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Blake3Compression.Executable.vectorChunkBlock_eq
