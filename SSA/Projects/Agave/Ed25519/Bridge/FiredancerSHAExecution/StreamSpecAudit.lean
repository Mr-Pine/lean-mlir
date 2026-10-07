import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpecMachine
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpecFinish

/-! Kernel-axiom audit for the pure Firedancer streaming invariant. -/
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.partition
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.complete_length
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.complete_whole
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.pending_length
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.pending_bound
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.initial_represents
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.append_represents
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.counterBytes_length
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.counterBytes_ofNat
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.finishBlocks_eq
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.finishBlocks_whole
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.finish_eq_digest
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.appendChunks_represents
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.finish_appendChunks
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.chunking_invariant
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.transcript_represents
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.finish_transcript
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.complete_append_aligned
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.pending_append_aligned
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.append_short
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.filledBlock_length
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.filledBlock_partition
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.append_filled
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.append_empty_buffer
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.observe_represents
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.finish_observe
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.machine_chunk_bits
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.machine_counter_append
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.size_represents_iff
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.transcript_counter_no_overflow
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.transcript_counter_toNat
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.transcript_size_boundary
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.represents_buffer_length
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.finishBlocks_flatten
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.finish_short
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.finish_long
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.transcript_prefix
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.transcript_pending_length
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.StreamSpec.transcript_long_padding_iff
