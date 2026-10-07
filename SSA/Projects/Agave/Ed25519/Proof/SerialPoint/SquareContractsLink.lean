import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SquareExecution
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.FieldCall
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialContracts

namespace Agave.Ed25519.SerialPoint.Execution
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)
open DoubleBase.SerialContracts
open Encoding.Decompress.Execution.Pow2k (program)

/-- Exact one-square helper contract, including shape and disjoint-read framing. -/
theorem square_contract : SquareContract program.call := by
  intro s out input hwf hout hin _ hA
  let output := squareMachine (readLimbs s input)
  let final : GlobalState := { s with mem := storeLimbs s.mem out output }
  have hread : readLimbs final out = output := readLimbs_storeLimbs s out output hout
  refine ⟨final, square_call out input s hwf hout hin, ?_, ?_, ?_⟩
  · refine ⟨wf_storeLimbs hwf out output, le_refl _, ?_, ?_⟩
    · intro id
      exact storeLimbs_allocationShape s.mem out output id
    · intro q bits hd
      exact readAt_storeLimbs_frame s.mem out q output bits hout hd
  · change unsigned (readLimbs final out) = _
    rw [hread]
    exact squareMachine_unsigned _ hA
  · change Tight (unsigned (readLimbs final out))
    rw [hread]
    exact squareMachine_tight _ hA


end Agave.Ed25519.SerialPoint.Execution
