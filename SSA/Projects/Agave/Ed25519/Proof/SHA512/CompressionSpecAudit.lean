import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionFold
import SSA.Projects.Agave.Ed25519.Proof.SHA512.ScheduleSpec
import SSA.Projects.Agave.Ed25519.Proof.SHA512.ScheduleArithmetic
import SSA.Projects.Agave.Ed25519.Proof.SHA512.RotationArithmetic
import SSA.Projects.Agave.Ed25519.Proof.SHA512.WindowSchedule
import SSA.Projects.Agave.Ed25519.Proof.SHA512.RoundComposition
import SSA.Projects.Agave.Ed25519.Proof.SHA512.InputByteOrder

/-! Guard the axiom closure of the concrete specification's structural facts.
This does not stand in for either backend's MLIR execution theorem. -/

/-- info: Concrete SHA-512 specification lemmas use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SHA512.Spec.schedulePrefix_length,
    ``Agave.Ed25519.SHA512.Spec.schedule_length,
    ``Agave.Ed25519.SHA512.Spec.schedule_initial,
    ``Agave.Ed25519.SHA512.Spec.schedule_recurrence,
    ``Agave.Ed25519.SHA512.Spec.avxSmallSigma0_eq,
    ``Agave.Ed25519.SHA512.Spec.avxSmallSigma1_eq,
    ``Agave.Ed25519.SHA512.Spec.avxScheduleWord_eq,
    ``Agave.Ed25519.SHA512.Spec.avxWindowPair_spec,
    ``Agave.Ed25519.SHA512.Spec.avxWindowStep_spec,
    ``Agave.Ed25519.SHA512.Spec.avxWindows_eq,
    ``Agave.Ed25519.SHA512.Spec.softRoundsFrom_eq,
    ``Agave.Ed25519.SHA512.Spec.avxRoundsFrom_eq,
    ``Agave.Ed25519.SHA512.Spec.avxPair_eq,
    ``Agave.Ed25519.SHA512.Spec.softCompression_eq,
    ``Agave.Ed25519.SHA512.Spec.avxCompression_eq,
    ``Agave.Ed25519.SHA512.Spec.backend_choice_eq,
    ``Agave.Ed25519.SHA512.Spec.readWordBE_concat,
    ``Agave.Ed25519.SHA512.Spec.bswap_native_readWordBE,
    ``Agave.Ed25519.SHA512.Spec.rotateRight1_fshl,
    ``Agave.Ed25519.SHA512.Spec.rotateRight8_fshl,
    ``Agave.Ed25519.SHA512.Spec.rotateRight14_fshl,
    ``Agave.Ed25519.SHA512.Spec.rotateRight18_fshl,
    ``Agave.Ed25519.SHA512.Spec.rotateRight19_fshl,
    ``Agave.Ed25519.SHA512.Spec.rotateRight28_fshl,
    ``Agave.Ed25519.SHA512.Spec.rotateRight34_fshl,
    ``Agave.Ed25519.SHA512.Spec.rotateRight39_fshl,
    ``Agave.Ed25519.SHA512.Spec.rotateRight41_fshl,
    ``Agave.Ed25519.SHA512.Spec.rotateRight61_fshl,
    ``Agave.Ed25519.SHA512.Spec.roundsFrom_add,
    ``Agave.Ed25519.SHA512.Spec.choose_xor_form,
    ``Agave.Ed25519.SHA512.Spec.avxRound_eq_round,
    ``Agave.Ed25519.SHA512.Spec.softRound_eq_round,
    ``Agave.Ed25519.SHA512.Spec.pack_unpack,
    ``Agave.Ed25519.SHA512.Spec.unpack_pack,
    ``Agave.Ed25519.SHA512.Spec.extracted_initial_eq,
    ``Agave.Ed25519.SHA512.Spec.completeBlocks_append,
    ``Agave.Ed25519.SHA512.Spec.run_append,
    ``Agave.Ed25519.SHA512.Spec.run_one_block,
    ``Agave.Ed25519.SHA512.Spec.run_two_blocks,
    ``Agave.Ed25519.SHA512.Spec.run_pair_prefix,
    ``Agave.Ed25519.SHA512.Spec.compression]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Concrete SHA-512 specification lemmas use only standard Lean axioms."
