import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionEntryMemory

/-! Existing K64 and caller bytes survive the three actual entry allocations,
and the initial scratch stores preserve the independently proved K64 table. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

theorem PairConstants.alloca {mem : GlobalState} {k : Pointer}
    (h : PairConstants mem.mem k) (hwf : mem.WF) (bytes : Nat) :
    PairConstants (mem.alloca bytes).mem k := by
  refine ⟨smallRange_alloca hwf h.live, ?_⟩
  intro r hr
  rw [MemoryState.readAt_alloca hwf
    (h.live.fits_add (k := 8*(r+16)) (count := 16) (by omega))]
  exact h.pairs r hr

theorem PairConstants.entryState {mem : GlobalState} {k : Pointer}
    (h : PairConstants mem.mem k) (hwf : mem.WF) :
    PairConstants (entryState mem).mem k :=
  ((h.alloca hwf 128).alloca hwf.alloca 640).alloca hwf.alloca.alloca 128

theorem PairConstants.initialScratchStores {mem : GlobalState} {k scratch : Pointer}
    (h : PairConstants mem.mem k) (block : Bytes) (n : Nat) (hn : n ≤ 8)
    (hs : SmallRange mem.mem scratch 128)
    (hd : (Range.of scratch 1024).Disjoint (Range.of k 5120)) :
    PairConstants (initialScratchStores mem scratch block n).mem k := by
  induction n with
  | zero => exact h
  | succ n ih =>
    exact (ih (by omega)).store
      ((initialScratchStores_frame mem scratch block n (by omega) hs).live hs)
      n (by omega) _ _ hd

theorem entryState_readBytes {mem : GlobalState} {p : Pointer} {bytes : Nat}
    (hwf : mem.WF) (h : SmallRange mem.mem p bytes) :
    readBytes (entryState mem).mem p bytes = readBytes mem.mem p bytes := by
  unfold entryState
  rw [readBytes_alloca _ _ _ _ hwf.alloca.alloca
      (smallRange_alloca hwf.alloca (smallRange_alloca hwf h)),
    readBytes_alloca _ _ _ _ hwf.alloca (smallRange_alloca hwf h),
    readBytes_alloca _ _ _ _ hwf h]

end Agave.Ed25519.SHA512.Execution.Avx2
