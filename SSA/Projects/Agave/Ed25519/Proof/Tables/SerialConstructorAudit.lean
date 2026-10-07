import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialCacheBody
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorReturn

/-! Kernel audits for the closed serial constructor sub-obligations. No theorem
below claims the still-open entry/loop/frame composition of the full function. -/

#print axioms Agave.Ed25519.Tables.SerialConstructorArithmetic.width5_words
#print axioms Agave.Ed25519.Tables.SerialConstructorContext.GlobalsReady.writesOnly
#print axioms Agave.Ed25519.Tables.SerialCacheExecution.phase_run
#print axioms Agave.Ed25519.Tables.SerialCacheExecution.loopPhase_run
#print axioms Agave.Ed25519.Tables.SerialCacheExecution.phase_contract
#print axioms Agave.Ed25519.Tables.SerialCacheExecution.loopPhase_contract
#print axioms Agave.Ed25519.Tables.SerialCacheExecution.phase_body
#print axioms Agave.Ed25519.Tables.SerialCacheExecution.loopPhase_body

#print axioms Agave.Ed25519.Tables.SerialConstructorReturn.return_contract
