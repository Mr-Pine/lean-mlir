import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.StartupMemory
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.UnpackRegisters

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The real initial environment and allocation prefix supply all unpack registers. -/
theorem startup_unpackReady (out input : Pointer) (s : GlobalState) :
    UnpackReady
      (allocationSchedule (constantsEnv
        (Env.init (program.args (.value out) (.value input)).get)) s).1
      input (fun i => startupScratch s ⟨10 + i.val, by omega⟩) := by
  constructor <;> rfl

end Agave.Ed25519.ScalarReduce32.Execution
