import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2Constructor
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhasePipeline
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGSlice
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2NAFFrame
import SSA.Projects.RIR.Run.Memory

/-! Exact positive-add intervals of the unchanged AVX2 table constructor. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Add
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases
open Avx2PointAdd.CFG (runSlice runBodyFrom_slice prepareConstants differenceConstants abdcVec)
open DoubleBase.ExecutionAvx2 (RegisterFrame)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
attribute [local implicit_reducible] Ty.width

structure Constants (E : ⟪kernel.Γ⟫) : Prop where
  poison : E.read (%31) = Ty.poisoned (.vec 8 32)
  prepare0 : E.read (%52) = prepareConstants 0
  prepareN : E.read (%70) = prepareConstants 1
  difference0 : E.read (%332) = differenceConstants 0
  differenceN : E.read (%349) = differenceConstants 1


end Agave.Ed25519.Tables.Avx2Constructor.Add
