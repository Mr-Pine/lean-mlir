import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorTightPrefix
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorPackingArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheExecution
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCachePreparation
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorLoopTail

/-! Audit of the constructor-local results. These do not yet instantiate the
whole-constructor TableContract: initial stack/load execution, the cache
scale/carry instruction bridge, arithmetic body composition, and seven-step
loop induction remain separate obligations. -/

#print axioms Agave.Ed25519.Tables.Avx2Constructor.Packing.run_slice
#print axioms Agave.Ed25519.Tables.Avx2Constructor.Packing.reads_result
#print axioms Agave.Ed25519.Tables.Avx2Constructor.Packing.pack_value
#print axioms Agave.Ed25519.Tables.Avx2Constructor.Packing.limbs_reduced
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheArithmetic.cache_reduced
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CacheArithmetic.cache_value
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CachePhases.normalize_continue
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CachePhases.initialCache_continue
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CachePhases.successorCache_continue
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CachePreparation.initial_point
#print axioms Agave.Ed25519.Tables.Avx2Constructor.CachePreparation.successor_point
#print axioms Agave.Ed25519.Tables.Avx2Constructor.LoopTail.body
#print axioms Agave.Ed25519.Tables.Avx2Constructor.LoopTail.exit
#print axioms Agave.Ed25519.Tables.Avx2Constructor.LoopTail.frame
#print axioms Agave.Ed25519.Tables.Avx2Constructor.LoopTail.read_frame
#print axioms Agave.Ed25519.Tables.Avx2Constructor.LoopTail.readback

#print axioms Agave.Ed25519.Tables.Avx2Constructor.Packing.pack_value_of_lt58
#print axioms Agave.Ed25519.Tables.Avx2Constructor.Normalization.normalized_reduced
#print axioms Agave.Ed25519.Tables.Avx2Constructor.Normalization.normalized_value
#print axioms Agave.Ed25519.Tables.Avx2Constructor.Normalization.normalized_cache
#print axioms Agave.Ed25519.Tables.Avx2Constructor.Normalization.step_value
#print axioms Agave.Ed25519.Tables.Avx2Constructor.Normalization.fold_value
#print axioms Agave.Ed25519.Tables.Avx2Constructor.Normalization.first_value
#print axioms Agave.Ed25519.Tables.Avx2Constructor.Normalization.network_point
#print axioms Agave.Ed25519.Tables.Avx2Constructor.Normalization.tight_normalization
#print axioms Agave.Ed25519.Tables.Avx2Constructor.TightPrefix.packed_ready
#print axioms Agave.Ed25519.Tables.Avx2Constructor.TightPrefix.run_slice
#print axioms Agave.Ed25519.Tables.Avx2Constructor.TightPrefix.tight_run
#print axioms Agave.Ed25519.Tables.Avx2Constructor.TightPrefix.tight_continue
