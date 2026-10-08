import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendObservation
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerReachableCalls
import SSA.Projects.Agave.Ed25519.Proof.SHA512.ByteOrder

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer Firedancer.Common
attribute [local irreducible] append core append32Memory append32BufferedMemory append32Block
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem fits_of_block {m : MemoryState} {p : Pointer} {b : LiveBlock} {n : Nat}
    (hb : m.live? p.id = some b) (hl : p.offsetInBits + n ≤ b.lengthInBits) : Fits m p n := by
  cases hm : m[p.id]? with
  | none => simp [MemoryState.live?, hm] at hb
  | some v => cases v with
    | dead => simp [MemoryState.live?, hm] at hb
    | live b' =>
      have he : b' = b := by simpa [MemoryState.live?, hm] using hb
      subst b'
      exact ⟨b, hm, hl⟩

private theorem common_bytes_injective {n : Nat} {x y : BitVec (n*8)}
    (h : bytesOf x = bytesOf y) : x = y := by
  apply Agave.Ed25519.SHA512.bytesOf_injective
  exact h

/-- The first reachable append contract, with the actual input word determining
its complete context allocation. -/
theorem append32_reachable (k : BitVec (80*64)) (b : LiveBlock) (off : BitVec 64)
    (input : BitVec 256) (hfit : 8 * off.toNat + 224*8 ≤ b.lengthInBits)
    (hcount : readBlock (some b) (off + 200#64) 64 = 0#64) :
    FiredancerReachableAppend programs k (some b)
      (append32Block (some b) off input 0#64 32#64) off (bytesOf (n := 32) input) := by
  intro p data sz s hwf _ hne _ hd _ _ hoff hblock hbytes
  have hlen : sz.toNat = 32 := by simpa only [bytesOf, List.length_ofFn] using congrArg List.length hbytes
  have hsz : sz = 32#64 := BitVec.eq_of_toNat_eq hlen
  subst sz
  change Fits s.mem data 256 at hd
  have hinput : sourceRead s.mem data 256 = input := by
    rw [sourceRead_eq_readWord hd]
    exact common_bytes_injective hbytes
  have hp : Fits s.mem p (224*8) := fits_of_block hblock (by
    simpa only [Pointer.offsetInBits, hoff] using hfit)
  have hc : sourceRead s.mem (p.withOffset 200#64) 64 = 0#64 := by
    simpa only [sourceRead, Pointer.withOffset, Pointer.offsetInBits, hblock, hoff, readBlock] using hcount
  obtain ⟨after, he, hw, ha, hg, hf, hb⟩ := append32_frame p data s hwf hp hd hc
  refine ⟨after, ?_, hw, ha, hg, hf, ?_⟩
  · simpa only [programs_append] using he
  · rw [hb, append32Memory_block _ _ _ hne, hinput, hblock, hoff]

/-- The second reachable append contract, from the 32-byte pending state. -/
theorem append32_buffered_reachable (k : BitVec (80*64)) (b : LiveBlock) (off : BitVec 64)
    (input : BitVec 256) (hfit : 8 * off.toNat + 224*8 ≤ b.lengthInBits)
    (hcount : readBlock (some b) (off + 200#64) 64 = 32#64) :
    FiredancerReachableAppend programs k (some b)
      (append32Block (some b) off input 32#64 64#64) off (bytesOf (n := 32) input) := by
  intro p data sz s hwf _ hne _ hd _ _ hoff hblock hbytes
  have hlen : sz.toNat = 32 := by simpa only [bytesOf, List.length_ofFn] using congrArg List.length hbytes
  have hsz : sz = 32#64 := BitVec.eq_of_toNat_eq hlen
  subst sz
  change Fits s.mem data 256 at hd
  have hinput : sourceRead s.mem data 256 = input := by
    rw [sourceRead_eq_readWord hd]
    exact common_bytes_injective hbytes
  have hp : Fits s.mem p (224*8) := fits_of_block hblock (by
    simpa only [Pointer.offsetInBits, hoff] using hfit)
  have hc : sourceRead s.mem (p.withOffset 200#64) 64 = 32#64 := by
    simpa only [sourceRead, Pointer.withOffset, Pointer.offsetInBits, hblock, hoff, readBlock] using hcount
  obtain ⟨after, he, hw, ha, hg, hf, hb⟩ := append32_buffered_frame p data s hwf hp hd hc
  refine ⟨after, ?_, hw, ha, hg, hf, ?_⟩
  · simpa only [programs_append] using he
  · rw [hb, append32BufferedMemory_block _ _ _ hne, hinput, hblock, hoff]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
