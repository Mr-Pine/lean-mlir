import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullBase

/-! Every volatile scalar K64 load follows from explicit global readiness. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.SHA512Finalization
open Spec

theorem constants_read (g : CompressionGlobals) (state : GlobalState)
    (h : CompressionReady g state) : KRead state.mem g.constantsPtr := by
  intro r
  have hr := h.constants_range
  have hlo : 8 * r.val + 8 ≤ 640 := by have := r.isLt; omega
  refine ⟨hr.fits_add (k := 8 * r.val) (count := 8) hlo, ?_⟩
  have hn : 8 * r.val < 2 ^ 64 := by have := r.isLt; omega
  have hk := MemoryState.readAt_add_of_readAt (off := BitVec.ofNat 64 (8 * r.val))
    (w := 64) hr.fits (hr.no_wrap (by omega)) (by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
      omega) rfl
  have hread : state.mem.readAt g.constantsPtr 5120 = BitVec.packLanes constants :=
    h.constants.readAt
  rw [hread] at hk
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    show 8 * r.val * 8 = 64 * r.val by omega] at hk
  rw [hk, Nat.mul_comm 64 r.val, BitVec.extractLsb'_packLanes constants r.val r.isLt]
  simp [List.getD_eq_getElem constants.toList 0 (n := r.val) (by simpa using r.isLt)]

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
