import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.InitializerData
import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionSpec

/-! The actual independently extracted Firedancer table matches the Agave/FIPS
round constants. A concrete RIR loader discharges table readiness. No claim
about a native dynamic loader, or core-loop correctness, is made here. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem constants_eq_standard : constantsBytes =
    BitVec.packLanes (we := 64) (n := 80) Agave.Ed25519.SHA512.Spec.constants := by
  decide +kernel

theorem constants_install_wf (s : GlobalState) (hwf : s.WF) :
    (constantsGlobal.install s).WF := constantsGlobal.wf_install hwf

theorem constants_install_read (s : GlobalState) :
    (constantsGlobal.install s).mem.readAt ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ 5120 =
      BitVec.packLanes (we := 64) (n := 80) Agave.Ed25519.SHA512.Spec.constants := by
  rw [← constants_eq_standard]
  exact (constantsGlobal.present_install s).readAt

end Agave.Ed25519.Bridge.FiredancerSHAExecution
