import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishPadding
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.PaddingMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.ByteOrder

/-! Byte observations of the actual Firedancer padding stores. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization (swapBytes bytesOf_zero)
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000

/-- A suffix store preserves the preceding bytes, including an empty prefix. -/
theorem storeSuffix_bytes (mem : MemoryState) (p : Pointer) (n k : Nat)
    (hr : SmallRange mem p (n + k)) (v : BitVec (k * 8)) :
    readBytes (mem.storeAt (p.add (BitVec.ofNat 64 n)) v) p (n + k) =
      readBytes mem p n ++ bytesOf v := by
  rw [readBytes_append, readBytes_storeAt_self _ _ k (smallRange_add hr (by omega))]
  congr 1
  apply readBytes_storeAt_disjoint _ _ _ _ _ (smallRange_mono hr (by omega))
  simpa [Nat.mul_comm] using smallRange_disjoint_offsets hr
    (i := n) (countI := k) (j := 0) (countJ := n)
    (by omega) (by omega) (Or.inr (by omega))

theorem markerMemory_bytes (mem : MemoryState) (p : Pointer) (used : Nat)
    (hr : SmallRange mem p 128) (hu : used < 128) :
    readBytes (markerMemory mem p used) p (used + 1) =
      readBytes mem p used ++ [128] := by
  exact (storeSuffix_bytes mem p used 1 (smallRange_mono hr (by omega)) 128#8).trans
    (by simp [bytesOf])

private theorem zero_heq {n m : Nat} (h : n = m) :
    HEq (0 : BitVec n) (0 : BitVec m) := by
  subst m
  rfl

private theorem replicatedZero (n : Nat) : (0#8).replicate n = (0 : BitVec (8 * n)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BitVec.replicate, ih]

theorem longMemory_bytes (mem : MemoryState) (p : Pointer) (used : Nat)
    (hr : SmallRange mem p 128) (hu : used < 128) :
    readBytes (longMemory mem p used) p 128 =
      readBytes mem p (used + 1) ++ List.replicate (127 - used) 0 := by
  have hn : used + 1 + (127 - used) = 128 := by omega
  unfold longMemory
  rw [replicatedZero]
  have h := storeSuffix_bytes mem p (used + 1) (127 - used) (by simpa [hn] using hr) 0
  rw [hn, bytesOf_zero] at h
  convert h using 1
  all_goals congr 2
  all_goals first | omega | exact zero_heq (Nat.mul_comm _ _)

theorem longPadding_bytes (mem : MemoryState) (p : Pointer) (used : Nat)
    (hr : SmallRange mem p 128) (hu : used < 128) :
    readBytes (longMemory (markerMemory mem p used) p used) p 128 =
      readBytes mem p used ++ [128] ++ List.replicate (127 - used) 0 := by
  have hm : SmallRange (markerMemory mem p used) p 128 := hr.storeAt _ _
  rw [longMemory_bytes _ _ _ hm hu, markerMemory_bytes _ _ _ hr hu]


theorem lastMemory_bytes (mem : MemoryState) (p : Pointer) (n : Nat) (lo hi : Word)
    (hr : SmallRange mem p 128) (hn : n ≤ 112) :
    readBytes (lastMemory mem p n lo hi) p 128 =
      readBytes mem p n ++ List.replicate (112 - n) 0 ++
        bytesOf (n := 8) (swapBytes hi) ++ bytesOf (n := 8) (swapBytes lo) := by
  let cleared := mem.storeAt (p.add (BitVec.ofNat 64 n)) ((0#8).replicate (112 - n))
  let high := cleared.storeAt (p.add 112#64) (swapBytes hi)
  have hc : SmallRange cleared p 128 := hr.storeAt _ _
  have hh : SmallRange high p 128 := hc.storeAt _ _
  have hzero : readBytes cleared p 112 =
      readBytes mem p n ++ List.replicate (112 - n) 0 := by
    have heq : n + (112 - n) = 112 := by omega
    have h := storeSuffix_bytes mem p n (112 - n)
      (smallRange_mono hr (by omega)) 0
    rw [heq, bytesOf_zero] at h
    dsimp only [cleared]
    rw [replicatedZero]
    convert h using 1
    all_goals congr 2
    all_goals first | omega | exact zero_heq (Nat.mul_comm _ _)
  have hhigh := storeSuffix_bytes cleared p 112 8 (smallRange_mono hc (by decide)) (swapBytes hi)
  have hlow := storeSuffix_bytes high p 120 8 hh (swapBytes lo)
  change readBytes (high.storeAt (p.add 120#64) (swapBytes lo)) p 128 = _
  rw [hlow, hhigh, hzero]


/-- Two source u64 stores have the same byte order as one big-endian u128. -/
theorem splitLength_bytes (hi lo : Word) :
    bytesOf (n := 8) (swapBytes hi) ++ bytesOf (n := 8) (swapBytes lo) =
      bytesOf (n := 16) (swapBytes (hi ++ lo)) := by
  unfold bytesOf
  change _ = List.ofFn (fun i : Fin (8 + 8) =>
    (swapBytes (hi ++ lo)).extractLsb' (i.val * 8) 8)
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext i
    simp only [Fin.val_castLE, Nat.mul_comm _ 8]
    rw [swapBytes64_byte hi i.val i.isLt, swapBytes128_byte (hi ++ lo) i.val (by omega)]
    fin_cases i <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;>
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] <;> grind
  · congr 1
    funext i
    simp only [Fin.val_natAdd, Nat.mul_comm _ 8]
    rw [swapBytes64_byte lo i.val i.isLt,
      swapBytes128_byte (hi ++ lo) (8 + i.val) (by omega)]
    fin_cases i <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;>
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] <;> grind

theorem lastMemory_lengthField (mem : MemoryState) (p : Pointer) (n total : Nat)
    (lo hi : Word) (hr : SmallRange mem p 128) (hn : n ≤ 112)
    (hcount : hi ++ lo = BitVec.ofNat 128 (8 * total)) :
    readBytes (lastMemory mem p n lo hi) p 128 =
      readBytes mem p n ++ List.replicate (112 - n) 0 ++ lengthField total := by
  rw [lastMemory_bytes _ _ _ _ _ hr hn, List.append_assoc,
    splitLength_bytes, hcount, swapBytes128_lengthField]


theorem firstPaddingBlock_bytes (mem : MemoryState) (p : Pointer) (pending : Bytes)
    (hr : SmallRange mem p 128) (hu : pending.length < 128)
    (hp : readBytes mem p pending.length = pending) :
    readBytes (longMemory (markerMemory mem p pending.length) p pending.length) p 128 =
      firstPaddingBlock pending := by
  rw [longPadding_bytes _ _ _ hr hu, hp]
  rfl

theorem onlyPaddingBlock_bytes (mem : MemoryState) (p : Pointer) (pending : Bytes)
    (total : Nat) (lo hi : Word) (hr : SmallRange mem p 128)
    (hu : pending.length < 112) (hp : readBytes mem p pending.length = pending)
    (hcount : hi ++ lo = BitVec.ofNat 128 (8 * total)) :
    readBytes (lastMemory (markerMemory mem p pending.length) p (pending.length + 1) lo hi)
      p 128 = onlyPaddingBlock pending total := by
  have hm : SmallRange (markerMemory mem p pending.length) p 128 := hr.storeAt _ _
  rw [lastMemory_lengthField _ _ _ _ _ _ hm (by omega) hcount,
    markerMemory_bytes _ _ _ hr (by omega), hp]
  simp only [onlyPaddingBlock, show 112 - (pending.length + 1) = 111 - pending.length by omega]

theorem lastPaddingBlock_bytes (mem : MemoryState) (p : Pointer) (total : Nat)
    (lo hi : Word) (hr : SmallRange mem p 128)
    (hcount : hi ++ lo = BitVec.ofNat 128 (8 * total)) :
    readBytes (lastMemory mem p 0 lo hi) p 128 = lastPaddingBlock total := by
  rw [lastMemory_lengthField _ _ _ _ _ _ hr (by decide) hcount]
  simp [readBytes, lastPaddingBlock]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
