import SSA.Projects.Agave.Ed25519.Proof.Verifier.Acceptance

/-!
Conditional composition is audited independently from concrete execution.
These theorems have standard axiom closures but retain `SharedCorrect`,
bounded double-scalar correctness, and compression correctness as hypotheses.
They therefore do not establish these contracts for compiler-produced code.
The shared challenge is a parameter; no SHA-512 oracle is accepted here.
-/

/-- info: 'Agave.Ed25519.Verifier.verify_iff_strict_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Verifier.verify_iff_strict_accept

/-- info: 'Agave.Ed25519.Verifier.verify_iff_firedancer_and_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Verifier.verify_iff_firedancer_and_canonical
