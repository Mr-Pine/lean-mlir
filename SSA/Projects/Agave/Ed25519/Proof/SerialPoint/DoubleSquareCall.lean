import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.DoubleProgram
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SquareExecution
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CallMemory

namespace Agave.Ed25519.SerialPoint.Execution
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)
open Encoding.Decompress.Execution.Pow2k (program)

/-- The exact callee binding used by the imported point-doubling body executes
the proved square function. The adapter's call frame introduces no allocation. -/
theorem double_square_call (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40) :
    (pow2kFunc program.call).call
      (.cons (.value r) (.cons (.value a) (.cons (.value 1#32) .nil))) s =
      .value (.nil, { s with mem := storeLimbs s.mem r (squareMachine (readLimbs s a)) }) := by
  refine Func.call_eq_of_run_eq ?_ (wf_storeLimbs hwf r _) rfl
  rw [Func.run_runFrom_eq]
  extract_state
  extract_env
  block_init
  step_call using square_call
  finish_block
  rw [hS]

end Agave.Ed25519.SerialPoint.Execution
