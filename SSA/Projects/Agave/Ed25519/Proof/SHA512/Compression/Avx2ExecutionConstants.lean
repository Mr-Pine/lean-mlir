import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.InitializerLink
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairMemory

/-! The exact source-initialized K64 allocation supplies every imported AVX2
constant pair. No separate correctness assumption about loaded constants is needed. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.SHA512Finalization
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

private theorem packed_constants_pair (r : Nat) (hr : r+1<64) :
    (BitVec.packLanes (we := 64) (n := 80) constants).extractLsb' (64*(r+16)) 128 =
      constants.toList.getD (r+17) 0 ++ constants.toList.getD (r+16) 0 := by
  have hr' : r ≤ 62 := by omega
  interval_cases r <;> decide

theorem pairConstants_of_ready (g : CompressionGlobals) (mem : GlobalState)
    (h : CompressionReady g mem) : PairConstants mem.mem g.constantsPtr := by
  refine ⟨h.constants_range, ?_⟩
  intro r hr
  have hn : 8*(r+16)<2^64 := by omega
  have hk := h.constants_range
  have hx := MemoryState.readAt_add_of_readAt
    (off := BitVec.ofNat 64 (8*(r+16))) (w := 128) hk.fits
    (hk.no_wrap (by omega)) (by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
      omega) h.constants.readAt
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hx
  rw [hx]
  simpa only [k64Memory, show 8*(r+16)*8=64*(r+16) by omega] using
    packed_constants_pair r hr

/-- The explicit source loader discharges the same readiness premise. -/
theorem pairConstants_of_source (g : ShaSourceGlobals) (mem : GlobalState)
    (h : ShaSourceReady g mem) : PairConstants mem.mem g.compression.constantsPtr :=
  pairConstants_of_ready g.compression mem h.compression

end Agave.Ed25519.SHA512.Execution.Avx2
