import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Group
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ByteControl
import SSA.Projects.Agave.Ed25519.Proof.NAF.OperationWindow

/-- info: 'Agave.Ed25519.DoubleBase.counterScan_eq_startIndex' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.counterScan_eq_startIndex
/-- info: 'Agave.Ed25519.DoubleBase.schedule_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.schedule_congr
/-- info: 'Agave.Ed25519.DoubleBase.signed_compare_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.signed_compare_byte
/-- info: 'Agave.Ed25519.DoubleBase.compiledLookup_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.compiledLookup_correct
/-- info: 'Agave.Ed25519.DoubleBase.double_base_math_affine_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.double_base_math_affine_eq
/-- info: 'Agave.Ed25519.DoubleBase.serialMath_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.serialMath_represents
/-- info: 'Agave.Ed25519.DoubleBase.avx2Math_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.DoubleBase.avx2Math_represents
/-- info: 'Agave.Ed25519.NAF.WordWindow.compiled_window_eq_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.NAF.WordWindow.compiled_window_eq_tail
/-- info: 'Agave.Ed25519.NAF.WordWindow.capturedWindow_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.NAF.WordWindow.capturedWindow_toNat
