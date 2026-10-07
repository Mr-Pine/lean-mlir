import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreCall
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.InitializerLink

/-! Concrete imported K-table readiness for the proved scalar core call. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem constants_present_range (state : GlobalState) (id : BlockId)
    (h : constantsGlobal.Present id state.mem) :
    SmallRange state.mem (constantsGlobal.address id) 640 := by
  refine ⟨⟨640, constantsBytes⟩, h, by decide, ?_⟩
  simp [ByteGlobal.address]

theorem constants_present_word (state : GlobalState) (id : BlockId)
    (h : constantsGlobal.Present id state.mem) (r : Nat) (hr : r < 80) :
    state.mem.readAt ((constantsGlobal.address id).add (BitVec.ofNat 64 (8 * r))) 64 =
      constants.toList.getD r 0 := by
  have hc := constants_present_range state id h
  have hn : 8 * r < 2 ^ 64 := by omega
  have hx := MemoryState.readAt_add_of_readAt (off := BitVec.ofNat 64 (8 * r))
    (w := 64) hc.fits (hc.no_wrap (by omega)) (by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
      omega) rfl
  have hread : state.mem.readAt (constantsGlobal.address id) 5120 = BitVec.packLanes constants := by
    rw [← constants_eq_standard]
    exact h.readAt
  rw [hread] at hx
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    show 8 * r * 8 = 64 * r by omega] at hx
  rw [hx, Nat.mul_comm 64 r, BitVec.extractLsb'_packLanes constants r hr]
  simp [Vector.getElem?_eq_getElem hr]

/-- Ready-to-call endpoint using the actual imported global's exact initializer,
with every round's numerical K read derived from that initializer. -/
theorem core_call_one_source (id : BlockId) (chain data : Pointer) (state : GlobalState)
    (initial : State) (hwf : state.WF) (hc : SmallRange state.mem chain 64)
    (hd : SmallRange state.mem data 128) (hk : constantsGlobal.Present id state.mem)
    (hm : state.mem.readAt chain 512 = pack initial) :
    (program (constantsGlobal.address id)).call
      (program.args (.value chain) (.value data) (.value 1#64)) state =
      .value (.nil, coreCallState state chain data initial) :=
  core_call_one_packed _ chain data state initial hwf hc hd
    (constants_present_range state id hk) hm (constants_present_word state id hk)

/-- A caller's chaining-state store preserves a separate installed global. -/
theorem coreCallState_constants (id : BlockId) (chain data : Pointer) (state : GlobalState)
    (initial : State) (hk : constantsGlobal.Present id state.mem) (hne : id ≠ chain.id) :
    constantsGlobal.Present id (coreCallState state chain data initial).mem :=
  hk.storeAt hne

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
