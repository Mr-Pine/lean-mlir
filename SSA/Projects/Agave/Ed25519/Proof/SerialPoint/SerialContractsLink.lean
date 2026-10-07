import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CachedAddContractsLink
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointContractMemory
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SquareContractsLink
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CachedAddExecution
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.DoubleExecution
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.FieldCall
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialContracts

namespace Agave.Ed25519.SerialPoint.Execution
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)
open DoubleBase.SerialContracts
open Encoding.Decompress.Execution.Pow2k (program)

/-- Only X,Y,Z occur in the completed doubling formula. -/
theorem doubleCompleted_readProjective (s : GlobalState) (p : Pointer) :
    doubleCompleted (unsignedPoint (pointFromWords (readPointWords s p))) =
      doubleCompleted (readProjective s p) := by
  rw [← readPoint_words]
  rfl

theorem projectiveTight_words (s : GlobalState) (p : Pointer)
    (hp : PointTight (readProjective s p)) :
    ProjectiveTight (unsignedPoint (pointFromWords (readPointWords s p))) := by
  rw [← readPoint_words]
  exact ⟨hp.1, hp.2.1, hp.2.2.1⟩

/-- Discharge the serial CFG's 120-byte projective double helper contract.
All four squares resolve to the imported pow2k body with exponent exactly one. -/
theorem double_contract :
    UnaryPointContract (double program.call).call 120 readProjective doubleCompleted := by
  intro s out input hwf hout hin _ hP
  let output := doubleWordTrace (readPointWords s input)
  let final := pointPost s out output 5
  have hp := projectiveTight_words s input hP
  have hread : readPoint final out = doubleCompleted (readProjective s input) := by
    rw [readPoint_words, pointPost_readback s out output 5 hout]
    exact (doubleWordTrace_projective_unsigned _ hp).trans
      (doubleCompleted_readProjective s input)
  refine ⟨final, double_call out input s hwf hout hin,
    pointPost_writesOnly s out output 5 hwf hout, hread, ?_⟩
  rw [hread]
  exact doubleCompleted_bounded _ hP


end Agave.Ed25519.SerialPoint.Execution
