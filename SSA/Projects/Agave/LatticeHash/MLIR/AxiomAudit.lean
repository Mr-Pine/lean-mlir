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

/-!
Axiom guards for the compiler-emitted kernel execution boundaries and their
word-level refinement lemmas. Only kernel-checked modules are imported here.
The allow-list is Lean's three standard axioms; adding a custom/native axiom
changes these messages and fails this module.
-/

/--
info: 'AgaveLatticeHash.MLIR.agave_g_8_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.agave_g_8_run

/--
info: 'AgaveLatticeHash.MLIR.agave_g_16_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.agave_g_16_run

/--
info: 'AgaveLatticeHash.MLIR.agave_portable_g_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.agave_portable_g_run

/--
info: 'AgaveLatticeHash.MLIR.agave_g_8_conforms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.agave_g_8_conforms

/--
info: 'AgaveLatticeHash.MLIR.agave_g_16_conforms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.agave_g_16_conforms

/--
info: 'AgaveLatticeHash.MLIR.agave_portable_g_conforms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.agave_portable_g_conforms

/--
info: 'AgaveLatticeHash.MLIR.gVectors_lane' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.gVectors_lane

/--
info: 'AgaveLatticeHash.MLIR.g_threeway_lane' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.g_threeway_lane

/--
info: 'AgaveLatticeHash.MLIR.gMemory_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.gMemory_frame

/--
info: 'AgaveLatticeHash.MLIR.scalarGMemory_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.scalarGMemory_frame

/--
info: 'AgaveLatticeHash.MLIR.agave_add_u16_8_conforms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.agave_add_u16_8_conforms

/--
info: 'AgaveLatticeHash.MLIR.agave_add_u16_16_conforms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.agave_add_u16_16_conforms

/--
info: 'AgaveLatticeHash.MLIR.addResult_lane' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.addResult_lane

/--
info: 'AgaveLatticeHash.MLIR.scheduleGlobalWords_lookup' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.scheduleGlobalWords_lookup

/--
info: 'AgaveLatticeHash.MLIR.scheduleGlobalBits_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.scheduleGlobalBits_lookup

/--
info: 'AgaveLatticeHash.MLIR.scheduleGlobal_load' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.scheduleGlobal_load

/--
info: 'AgaveLatticeHash.MLIR.scheduleGlobal_withGlobal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.scheduleGlobal_withGlobal

/--
info: 'AgaveLatticeHash.MLIR.transpose8_denote' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.transpose8_denote

/--
info: 'AgaveLatticeHash.MLIR.transpose16_denote' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.transpose16_denote

/--
info: 'AgaveLatticeHash.MLIR.CompressionExit.exit8_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.CompressionExit.exit8_run

/--
info: 'AgaveLatticeHash.MLIR.CompressionExit.exit16_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.CompressionExit.exit16_run

/--
info: 'AgaveLatticeHash.MLIR.outputMem_read_lane' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.outputMem_read_lane

/--
info: 'AgaveLatticeHash.MLIR.portableCompressionMemory_read_word' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.portableCompressionMemory_read_word

/--
info: 'AgaveLatticeHash.MLIR.BatchEntry.entry8_denote' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchEntry.entry8_denote

/--
info: 'AgaveLatticeHash.MLIR.BatchEntry16.entry16_denote' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchEntry16.entry16_denote

/--
info: 'AgaveLatticeHash.MLIR.BatchLoads.block2_continue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchLoads.block2_continue

/--
info: 'AgaveLatticeHash.MLIR.BatchLoads.block8_continue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchLoads.block8_continue

/--
info: 'AgaveLatticeHash.MLIR.BatchLoads.block10_continue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchLoads.block10_continue

/--
info: 'AgaveLatticeHash.MLIR.BatchLoads.block15_continue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchLoads.block15_continue

/--
info: 'AgaveLatticeHash.MLIR.BatchHeader.continue8' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchHeader.continue8

/--
info: 'AgaveLatticeHash.MLIR.BatchHeader.active_lane' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchHeader.active_lane

/--
info: 'AgaveLatticeHash.MLIR.BatchHeader.run8' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchHeader.run8

/--
info: 'AgaveLatticeHash.MLIR.BatchFirstTranspose.first8_denote' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchFirstTranspose.first8_denote

/--
info: 'AgaveLatticeHash.MLIR.BatchFirstTranspose.first8_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchFirstTranspose.first8_run

/--
info: 'AgaveLatticeHash.MLIR.BatchTranspose.transpose8_denote' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchTranspose.transpose8_denote

/--
info: 'AgaveLatticeHash.MLIR.BatchTranspose.transpose8_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchTranspose.transpose8_run

/--
info: 'AgaveLatticeHash.MLIR.BatchTranspose.transpose8_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchTranspose.transpose8_frame

/--
info: 'AgaveLatticeHash.MLIR.BatchRootCopy.block18_continue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchRootCopy.block18_continue

/--
info: 'AgaveLatticeHash.MLIR.agave_compress_pre_8_readback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.agave_compress_pre_8_readback

/--
info: 'AgaveLatticeHash.MLIR.agave_compress_pre_16_readback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.agave_compress_pre_16_readback

/--
info: 'AgaveLatticeHash.MLIR.CallerMemory.materialization_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.CallerMemory.materialization_exists

/--
info: 'AgaveLatticeHash.MLIR.CallerMemory.pack_wordsLE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.CallerMemory.pack_wordsLE

/--
info: 'AgaveLatticeHash.MLIR.CallerMemory.represented_messages' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.CallerMemory.represented_messages

/--
info: 'AgaveLatticeHash.MLIR.CallerMemory.represented_loads8' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.CallerMemory.represented_loads8

/--
info: 'AgaveLatticeHash.MLIR.CallerMemory.columns8_scalarBlock' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.CallerMemory.columns8_scalarBlock

/--
info: 'AgaveLatticeHash.MLIR.CallerMemory.columns16_scalarBlock' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.CallerMemory.columns16_scalarBlock

/--
info: 'AgaveLatticeHash.MLIR.portable_compression_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.portable_compression_run

/--
info: 'AgaveLatticeHash.MLIR.portable_reference_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.portable_reference_run

/--
info: 'AgaveLatticeHash.MLIR.portable_reference_conforms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.portable_reference_conforms

/--
info: 'AgaveLatticeHash.MLIR.portable_reference_readback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.portable_reference_readback

/--
info: 'AgaveLatticeHash.MLIR.vector8_reference_readback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.vector8_reference_readback

/--
info: 'AgaveLatticeHash.MLIR.vector16_reference_readback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.vector16_reference_readback

/--
info: 'AgaveLatticeHash.MLIR.compression_three_way_readback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.compression_three_way_readback

/--
info: 'AgaveLatticeHash.MLIR.portable_call_xof_observation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.portable_call_xof_observation

/--
info: 'AgaveLatticeHash.MLIR.portable_root_output_observation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.portable_root_output_observation

/--
info: 'AgaveLatticeHash.MLIR.CallerMemory.physicalUpdate_eq_portableLtHash' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.CallerMemory.physicalUpdate_eq_portableLtHash

/--
info: 'AgaveLatticeHash.MLIR.BatchExecution8.terminates_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchExecution8.terminates_eval

/--
info: 'AgaveLatticeHash.MLIR.BatchConformance8.run_readback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchConformance8.run_readback

/--
info: 'AgaveLatticeHash.MLIR.BatchConformance8.run_portableLtHash' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchConformance8.run_portableLtHash

/--
info: 'AgaveLatticeHash.MLIR.BatchConformance8.fullWidth_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchConformance8.fullWidth_total

/--
info: 'AgaveLatticeHash.MLIR.BatchConformance8.fullWidth_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchConformance8.fullWidth_refines

/--
info: 'AgaveLatticeHash.MLIR.Execution.Avx2.run_refines_log' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.Execution.Avx2.run_refines_log

/--
info: 'AgaveLatticeHash.MLIR.Execution.Avx2.every_legal_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.Execution.Avx2.every_legal_trace

/--
info: 'AgaveLatticeHash.MLIR.Execution.Avx2.noSerial_run_refines_log' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.Execution.Avx2.noSerial_run_refines_log

/--
info: 'AgaveLatticeHash.MLIR.Execution.Avx2.eight_empty_compiled_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.Execution.Avx2.eight_empty_compiled_witness

/--
info: 'AgaveLatticeHash.MLIR.BatchExecution16.terminates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchExecution16.terminates

/--
info: 'AgaveLatticeHash.MLIR.BatchExecution16.terminates_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchExecution16.terminates_eval

/--
info: 'AgaveLatticeHash.MLIR.BatchReadback16.finish_read' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchReadback16.finish_read

/--
info: 'AgaveLatticeHash.MLIR.BatchConformance16.run_readback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchConformance16.run_readback

/--
info: 'AgaveLatticeHash.MLIR.BatchConformance16.run_portableLtHash' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchConformance16.run_portableLtHash

/--
info: 'AgaveLatticeHash.MLIR.BatchConformance16.fullWidth_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchConformance16.fullWidth_total

/--
info: 'AgaveLatticeHash.MLIR.BatchConformance16.fullWidth_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.BatchConformance16.fullWidth_refines

/--
info: 'AgaveLatticeHash.MLIR.Execution.Avx512.run_refines_log' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.Execution.Avx512.run_refines_log

/--
info: 'AgaveLatticeHash.MLIR.Execution.Avx512.every_legal_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.Execution.Avx512.every_legal_trace

/--
info: 'AgaveLatticeHash.MLIR.Execution.Avx512.noSerial_run_refines_log' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.Execution.Avx512.noSerial_run_refines_log

/--
info: 'AgaveLatticeHash.MLIR.Execution.Avx512.sixteen_empty_compiled_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.Execution.Avx512.sixteen_empty_compiled_witness

/--
info: 'AgaveLatticeHash.MLIR.portable_xof_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.portable_xof_run

/--
info: 'AgaveLatticeHash.MLIR.portable_xof_reference_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.portable_xof_reference_run

/--
info: 'AgaveLatticeHash.MLIR.portable_xof_reference_conforms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.portable_xof_reference_conforms

/--
info: 'AgaveLatticeHash.MLIR.portableCompressionMemory_read_byte' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.portableCompressionMemory_read_byte

/--
info: 'AgaveLatticeHash.MLIR.portable_xof_call_readback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.portable_xof_call_readback

/--
info: 'AgaveLatticeHash.MLIR.portable_xof_root_output_readback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.portable_xof_root_output_readback

/--
info: 'AgaveLatticeHash.MLIR.PortableShort.image_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.PortableShort.image_inputs

/--
info: 'AgaveLatticeHash.MLIR.PortableShort.xof_calls_all_bytes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.PortableShort.xof_calls_all_bytes

/--
info: 'AgaveLatticeHash.MLIR.PortableShort.nonroot_calls' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.PortableShort.nonroot_calls

/--
info: 'AgaveLatticeHash.MLIR.PortableShort.short_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.PortableShort.short_run

/--
info: 'AgaveLatticeHash.MLIR.PortableShort.short_run_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.PortableShort.short_run_exists

/--
info: 'AgaveLatticeHash.MLIR.portable_in_place_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.portable_in_place_run

/--
info: 'AgaveLatticeHash.MLIR.portable_in_place_readback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.portable_in_place_readback

/--
info: 'AgaveLatticeHash.MLIR.PortableInPlace.cvMemory_read' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.PortableInPlace.cvMemory_read

/--
info: 'AgaveLatticeHash.MLIR.PortableInPlace.cvMemory_fits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.PortableInPlace.cvMemory_fits

/--
info: 'AgaveLatticeHash.MLIR.PortableInPlace.cvMemory_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AgaveLatticeHash.MLIR.PortableInPlace.cvMemory_frame
