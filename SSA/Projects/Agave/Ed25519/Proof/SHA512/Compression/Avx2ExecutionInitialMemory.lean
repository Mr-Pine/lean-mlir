import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionScratchFrame
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullInputMemory

/-! Concrete message-pair loads and the eight initial scratch stores in bb2. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
open Spec

private theorem append_halves128 (x : BitVec 128) :
    x = x.extractLsb' 64 64 ++ x.extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  grind

/-- A native vector load contains exactly the two address-order native words. -/
theorem load_initial_pair_native (mem : MemoryState) (data : Pointer)
    (hd : SmallRange mem data 128) (j : Nat) (hj : j < 8) :
    mem.readAt (data.add (BitVec.ofNat 64 (16*j))) 128 =
      readWordNative (readBytes mem data 128) (2*j+1) ++
        readWordNative (readBytes mem data 128) (2*j) := by
  let p := data.add (BitVec.ofNat 64 (16*j))
  have hp : SmallRange mem p 16 := pair_slot_live hd j hj
  have hlo := MemoryState.readAt_add_of_readAt (off := 0#64) (w := 64)
    hp.fits (hp.no_wrap (k := 0) (by decide)) (by decide) rfl
  have hhi := MemoryState.readAt_add_of_readAt (off := 8#64) (w := 64)
    hp.fits (hp.no_wrap (k := 8) (by decide)) (by decide) rfl
  simp only [Pointer.add_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.reduceMul] at hlo hhi
  have hp0 : p = data.add (BitVec.ofNat 64 (8*(2*j))) := by
    dsimp [p]
    congr 2
    omega
  have hp1 : p.add 8#64 = data.add (BitVec.ofNat 64 (8*(2*j+1))) := by
    dsimp [p]
    rw [Pointer.add_add, ← BitVec.ofNat_add]
    congr 2
    omega
  change mem.readAt p 128 = _
  rw [append_halves128 (mem.readAt p 128), ← hlo, ← hhi, hp1, hp0]
  rw [Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull.load_readWordNative mem data hd
    (2*j) (by omega),
    Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull.load_readWordNative mem data hd
    (2*j+1) (by omega)]

/-- The emitted initial pair adds each decoded word to its literal constant. -/
def initialPairLow (block : Bytes) (j : Nat) : Word :=
  readWordBE block (2*j) + constants.toList.getD (2*j) 0

def initialPairHigh (block : Bytes) (j : Nat) : Word :=
  readWordBE block (2*j+1) + constants.toList.getD (2*j+1) 0

/-- Exact store order in bb2, retaining the unchanged allocation counter. -/
def initialScratchStores (mem : GlobalState) (scratch : Pointer) (block : Bytes) : Nat → GlobalState
  | 0 => mem
  | n + 1 => pairStoreState (initialScratchStores mem scratch block n) scratch n
      (initialPairLow block n) (initialPairHigh block n)

theorem initialPairLow_eq (block : Bytes) (j : Nat) (hj : j < 8) :
    initialPairLow block j = scheduleKW (schedule block) (2*j) := by
  simp only [initialPairLow, scheduleKW, schedule_initial block (2*j) (by omega),
    BitVec.add_comm]

theorem initialPairHigh_eq (block : Bytes) (j : Nat) (hj : j < 8) :
    initialPairHigh block j = scheduleKW (schedule block) (2*j+1) := by
  simp only [initialPairHigh, scheduleKW, schedule_initial block (2*j+1) (by omega),
    BitVec.add_comm]

/-- Every partial initialization preserves all ranges and disjoint reads. -/
theorem initialScratchStores_frame (mem : GlobalState) (scratch : Pointer) (block : Bytes)
    (n : Nat) (hn : n ≤ 8) (hs : SmallRange mem.mem scratch 128) :
    ScratchFrame scratch mem (initialScratchStores mem scratch block n) := by
  induction n with
  | zero => exact ScratchFrame.refl _ _
  | succ n ih =>
    have hf := ih (by omega)
    exact hf.trans (pairStoreState_frame _ scratch n _ _ (hf.live hs) (by omega))

/-- Each initialized slot contains its concrete initial K+W word. -/
theorem initialScratchStores_read (mem : GlobalState) (scratch : Pointer) (block : Bytes)
    (n : Nat) (hn : n ≤ 8) (hs : SmallRange mem.mem scratch 128) :
    ∀ t, t < 2*n →
      (initialScratchStores mem scratch block n).mem.readAt
        (scratch.add (BitVec.ofNat 64 (8*t))) 64 = scheduleKW (schedule block) t := by
  induction n with
  | zero => intro t ht; omega
  | succ n ih =>
    intro t ht
    have hn8 : n < 8 := by omega
    have hslive := (initialScratchStores_frame mem scratch block n (by omega) hs).live hs
    simp only [initialScratchStores, pairStoreState]
    rw [pairScratchStore_read _ scratch hslive n t hn8 (by omega),
      initialPairLow_eq block n hn8, initialPairHigh_eq block n hn8]
    by_cases h0 : t = 2*n
    · simp only [h0, ite_true]
    · by_cases h1 : t = 2*n+1
      · rw [ite_eq_right h0, ite_eq_left h1, h1]
      · rw [ite_eq_right h0, ite_eq_right h1]
        exact ih (by omega) t (by omega)

/-- Eight stores establish the first group's complete scratch invariant. -/
theorem initialScratchStores_ready (mem : GlobalState) (scratch : Pointer) (block : Bytes)
    (hs : SmallRange mem.mem scratch 128) :
    PairScratch (initialScratchStores mem scratch block 8).mem scratch (schedule block) 0 0 := by
  refine ⟨(initialScratchStores_frame mem scratch block 8 (by decide) hs).live hs, ?_⟩
  intro t ht
  simpa only [Nat.mul_zero, Nat.not_lt_zero, ite_false, Nat.zero_add] using
    initialScratchStores_read mem scratch block 8 (by decide) hs t ht

/-- Input reads remain available after every earlier scratch-pair store. -/
theorem initialScratchStores_read_disjoint (mem : GlobalState) (scratch : Pointer)
    (block : Bytes) (n : Nat) (hn : n ≤ 8) (hs : SmallRange mem.mem scratch 128)
    (p : Pointer) (w : Nat) (hd : (Range.of scratch 1024).Disjoint (Range.of p w)) :
    (initialScratchStores mem scratch block n).mem.readAt p w = mem.mem.readAt p w :=
  (initialScratchStores_frame mem scratch block n hn hs).read p w hd

/-- Full input/scratch separation also separates every 16-byte message pair. -/
theorem initial_pair_disjoint {mem : MemoryState} {scratch data : Pointer}
    (hd : SmallRange mem data 128) (j : Nat) (hj : j < 8)
    (hsep : (Range.of scratch 1024).Disjoint (Range.of data 1024)) :
    (Range.of scratch 1024).Disjoint
      (Range.of (data.add (BitVec.ofNat 64 (16*j))) 128) := by
  have hoff := Pointer.offsetInBits_add (hd.no_wrap (k := 16*j) (by omega))
  have hsmall : 16*j < 2^64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall] at hoff
  simp only [Range.Disjoint, Range.of, Pointer.add_id, hoff] at hsep ⊢
  rcases hsep with hid | hbefore | hafter
  · exact Or.inl hid
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

/-- Earlier initial stores leave each raw message-pair load equal to the
original message bytes, without requiring separate allocation identities. -/
theorem initialScratchStores_load_pair (mem : GlobalState) (scratch data : Pointer)
    (block : Bytes) (n j : Nat) (hn : n ≤ 8) (hj : j < 8)
    (hs : SmallRange mem.mem scratch 128) (hd : SmallRange mem.mem data 128)
    (hsep : (Range.of scratch 1024).Disjoint (Range.of data 1024)) :
    (initialScratchStores mem scratch block n).mem.readAt
      (data.add (BitVec.ofNat 64 (16*j))) 128 =
        readWordNative (readBytes mem.mem data 128) (2*j+1) ++
          readWordNative (readBytes mem.mem data 128) (2*j) := by
  rw [initialScratchStores_read_disjoint mem scratch block n hn hs _ _
    (initial_pair_disjoint hd j hj hsep)]
  exact load_initial_pair_native mem.mem data hd j hj

end Agave.Ed25519.SHA512.Execution.Avx2
