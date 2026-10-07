import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialSetupReady
import Lean

open Lean in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    `Agave.Ed25519.DoubleBase.RIR.serial_setup_block,
    `Agave.Ed25519.DoubleBase.RIR.serialIdentity_frame,
    `Agave.Ed25519.DoubleBase.RIR.serialIdentity_readProjective,
    `Agave.Ed25519.DoubleBase.RIR.serial_setup_run,
    `Agave.Ed25519.DoubleBase.RIR.serialIdentity_represents,
    `Agave.Ed25519.DoubleBase.RIR.serialNAFState8_global,
    `Agave.Ed25519.DoubleBase.RIR.serial_prepare_setup,
    `Agave.Ed25519.DoubleBase.RIR.serialBaseWord_bounded,
    `Agave.Ed25519.DoubleBase.RIR.serialBase_cache_ready,
    `Agave.Ed25519.DoubleBase.RIR.serialSetup_ladderRegisters,
    `Agave.Ed25519.DoubleBase.RIR.serialSetup_ladderMemory,
    `Agave.Ed25519.DoubleBase.RIR.serial_prepare_ladder]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "{endpoint} depends on forbidden axiom {dependency}"

#print axioms Agave.Ed25519.DoubleBase.RIR.serial_setup_block
#print axioms Agave.Ed25519.DoubleBase.RIR.serialIdentity_frame
#print axioms Agave.Ed25519.DoubleBase.RIR.serialIdentity_readProjective
#print axioms Agave.Ed25519.DoubleBase.RIR.serial_setup_run
#print axioms Agave.Ed25519.DoubleBase.RIR.serialIdentity_represents
#print axioms Agave.Ed25519.DoubleBase.RIR.serialNAFState8_global
#print axioms Agave.Ed25519.DoubleBase.RIR.serial_prepare_setup
#print axioms Agave.Ed25519.DoubleBase.RIR.serialBaseWord_bounded
#print axioms Agave.Ed25519.DoubleBase.RIR.serialBase_cache_ready
#print axioms Agave.Ed25519.DoubleBase.RIR.serialSetup_ladderRegisters
#print axioms Agave.Ed25519.DoubleBase.RIR.serialSetup_ladderMemory
#print axioms Agave.Ed25519.DoubleBase.RIR.serial_prepare_ladder
