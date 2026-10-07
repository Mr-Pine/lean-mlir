import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.ExecutionRefinement
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SquareExecution
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointWord

import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CachedAddWord
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.DoubleTrace
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.DoubleSquareCall
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.FieldCall
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointMemory
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CachedAddExecution
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SquareContractsLink

/-! Guard the logical dependency boundary of the checked helper execution and
word-refinement endpoints, including exact cached-add execution and the square contract link. -/

/-- info: 'Agave.Ed25519.SerialPoint.Execution.storeLimbs_readAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.storeLimbs_readAt

/-- info: 'Agave.Ed25519.SerialPoint.Execution.readLimbs_storeLimbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.readLimbs_storeLimbs

/-- info: 'Agave.Ed25519.SerialPoint.Execution.cached_add_pp_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.cached_add_pp_call

/-- info: 'Agave.Ed25519.SerialPoint.Execution.cached_add_pp_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.cached_add_pp_readback

/-- info: 'Agave.Ed25519.SerialPoint.Execution.square_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.square_call

/-- info: 'Agave.Ed25519.SerialPoint.Execution.square_call_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.square_call_correct

/-- info: 'Agave.Ed25519.SerialPoint.Execution.square_call_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.square_call_readback

/-- info: 'Agave.Ed25519.SerialPoint.addWord_unsigned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.addWord_unsigned

/-- info: 'Agave.Ed25519.SerialPoint.biasedSubWord_unsigned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.biasedSubWord_unsigned

/-- info: 'Agave.Ed25519.SerialPoint.subWord_unsigned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.subWord_unsigned

/-- info: 'Agave.Ed25519.SerialPoint.Execution.cachedAddWordTrace_unsigned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.cachedAddWordTrace_unsigned

/-- info: 'Agave.Ed25519.SerialPoint.Execution.doubleWordTrace_projective_unsigned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.doubleWordTrace_projective_unsigned

/-- info: 'Agave.Ed25519.SerialPoint.Execution.double_square_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.double_square_call

/-- info: 'Agave.Ed25519.SerialPoint.Execution.pointPost_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.pointPost_readback

/-- info: 'Agave.Ed25519.SerialPoint.Execution.readAt_storePointWords_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.readAt_storePointWords_frame

/-- info: 'Agave.Ed25519.SerialPoint.Execution.mulPost_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.mulPost_correct

/-- info: 'Agave.Ed25519.SerialPoint.Execution.cached_add_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.cached_add_call

/-- info: 'Agave.Ed25519.SerialPoint.Execution.cached_add_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.cached_add_readback

/-- info: 'Agave.Ed25519.SerialPoint.Execution.square_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.SerialPoint.Execution.square_contract
