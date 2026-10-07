import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGRegisterFrame
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGNoops
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGStores
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGCopy
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhasePipeline

/-! Local phase and memory-frame audit. This does not certify the composed
CFG blocks, whose separate audit requires the actual multiplication helper. -/

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.prepare22_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.prepare22_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.difference22_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.difference22_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.adda22_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.adda22_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.cbcb22_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.cbcb22_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.prepare22_store_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.prepare22_store_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.load22_result_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.load22_result_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.copy22_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.copy22_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.row22_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.row22_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.prepare25_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.prepare25_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.difference25_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.difference25_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.adda25_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.adda25_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.cbcb25_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.cbcb25_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.prepare25_store_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.prepare25_store_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.load25_result_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.load25_result_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.copy25_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.copy25_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.row25_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.row25_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.prepare29_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.prepare29_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.difference29_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.difference29_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.adda29_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.adda29_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.cbcb29_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.cbcb29_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.prepare29_store_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.prepare29_store_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.load29_result_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.load29_result_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.copy29_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.copy29_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.row29_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.row29_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.prepare33_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.prepare33_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.difference33_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.difference33_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.adda33_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.adda33_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.cbcb33_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.cbcb33_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.prepare33_store_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.prepare33_store_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.load33_result_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.load33_result_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.copy33_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.copy33_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.row33_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.row33_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.negate22_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.negate22_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.cached22_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.cached22_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.negate29_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.negate29_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.CFG.cached29_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.CFG.cached29_slice

/-- info: 'Agave.Ed25519.Avx2PointAdd.Phases.pipelineState_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.Phases.pipelineState_frame

/-- info: 'Agave.Ed25519.Avx2PointAdd.Phases.result_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.Phases.result_read
