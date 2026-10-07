import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreFirst
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullInputMemory

/-! Input byte order and the first loop's partial-ring memory invariant. The
reused native-load lemma concerns byte observations only, not an Agave program. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization (swapBytes)
open Agave.Ed25519.Bridge.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem input_swap_eq (m : MemoryState) (data : Pointer) (r : Nat)
    (hd : SmallRange m data 128) (hr : r < 16) :
    swapBytes (m.readAt (data.add (BitVec.ofNat 64 (8 * r))) 64) =
      readWordBE (readBytes m data 128) r := by
  have h := Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull.load_bswap_readWordBE m data hd r hr
  change LeanMLIR.RIR.PoisonOr.value (swapBytes (m.readAt (data.add (BitVec.ofNat 64 (8 * r))) 64)) =
    LeanMLIR.RIR.PoisonOr.value (readWordBE (readBytes m data 128) r) at h
  exact LeanMLIR.RIR.PoisonOr.value_inj.mp h

def InitialRingMemory (m : MemoryState) (stack : Pointer) (block : Bytes) (r : Nat) : Prop :=
  ∀ j, j < r → m.readAt (stack.add (BitVec.ofNat 64 (8 * j))) 64 = readWordBE block j

theorem initialRingMemory_zero (m : MemoryState) (stack : Pointer) (block : Bytes) :
    InitialRingMemory m stack block 0 := by
  intro j hj
  omega

theorem inputMemory_initial_step (m : MemoryState) (stack : Pointer) (block : Bytes)
    (r : Nat) (native : Word) (hr : r < 16) (hs : SmallRange m stack 128)
    (h : InitialRingMemory m stack block r) (hword : swapBytes native = readWordBE block r) :
    InitialRingMemory (inputMemory m stack r native) stack block (r + 1) := by
  intro j hj
  by_cases heq : j = r
  · subst j
    rw [inputMemory, MemoryState.readAt_storeAt_self
      (hs.fits_add (k := 8 * r) (count := 8) (by omega)), hword]
  · have hlt : j < r := by omega
    have hdis := smallRange_disjoint_offsets hs (i := 8 * r) (countI := 8)
      (j := 8 * j) (countJ := 8) (by omega) (by omega) (Or.inr (by omega))
    rw [inputMemory, MemoryState.readAt_storeAt_disjoint hdis]
    exact h j hlt

theorem initialRingMemory_full (m : MemoryState) (stack : Pointer) (block : Bytes)
    (h : InitialRingMemory m stack block 16) :
    ∀ j, j < 16 → m.readAt (stack.add (BitVec.ofNat 64 (8 * j))) 64 = initialRing block j := h

theorem inputMemory_preserves_data (m : MemoryState) (stack data : Pointer)
    (r : Nat) (native : Word) (hd : SmallRange m data 128) (hne : stack.id ≠ data.id) :
    readBytes (inputMemory m stack r native) data 128 = readBytes m data 128 := by
  apply readBytes_storeAt_disjoint _ _ _ _ _ hd
  exact Or.inl hne

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
