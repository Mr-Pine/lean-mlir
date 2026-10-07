import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionRefinement

/-! A focused audit target that does not import the standalone Reduce64 kernel.
These guards become validation evidence only after this module builds. -/

/-- info: 'Agave.Ed25519.Avx2SquareNegateD.Execution.Suffix.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2SquareNegateD.Execution.Suffix.run

/-- info: 'Agave.Ed25519.Avx2SquareNegateD.Execution.kernel_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2SquareNegateD.Execution.kernel_call

/-- info: 'Agave.Ed25519.Avx2SquareNegateD.Execution.kernel_call_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2SquareNegateD.Execution.kernel_call_words

/-- info: 'Agave.Ed25519.Avx2SquareNegateD.Execution.kernel_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2SquareNegateD.Execution.kernel_correct
