import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendBuffered

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
attribute [local irreducible] append core append32Memory append32BufferedMemory
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option autoImplicit false

def readBlock (b : Option LiveBlock) (off : BitVec 64) (width : Nat) : BitVec width :=
  match b with
  | some b => b.bytes.extractLsb' (8 * off.toNat) width
  | none => 0

/-- The visible block update of either 32-byte verifier append. -/
def append32Block (b : Option LiveBlock) (off : BitVec 64) (input : BitVec 256)
    (bufferOffset count : BitVec 64) : Option LiveBlock :=
  let lo := readBlock b (off + 208#64) 64
  let hi := readBlock b (off + 216#64) 64
  let nextLo := lo + 256#64
  let nextHi := hi + (if nextLo <ᵤ lo then 1#64 else 0#64)
  let b := storeBlock b (off + 208#64) nextLo
  let b := storeBlock b (off + 216#64) nextHi
  let b := storeBlock b (off + bufferOffset) input
  storeBlock b (off + 200#64) count

theorem sourceRead_splice_ne {m : MemoryState} {p q : Pointer} {w v : Nat}
    (x : BitVec v) (h : q.id ≠ p.id) :
    sourceRead (m.splice q x) p w = sourceRead m p w :=
  sourceRead_of_live_eq (live?_splice_ne h)

theorem sourceRead_eq_readWord {m : MemoryState} {p : Pointer} {w : Nat}
    (h : Fits m p w) : sourceRead m p w = readWord h := by
  have hread : readWord? p w m = some (readWord h) := readWord?_eq_some h rfl
  have heq : sourceRead m p w = (readWord? p w m).getD 0 := by
    cases hb : m.live? p.id <;> simp [sourceRead, readWord?, hb]
  rw [heq, hread]
  rfl

theorem append32Memory_block (m : MemoryState) (p data : Pointer) (hne : p.id ≠ data.id) :
    (append32Memory m p data).live? p.id =
      append32Block (m.live? p.id) p.offset (sourceRead m data 256) 0#64 32#64 := by
  unfold append32Memory
  simp only [sourceRead_splice_ne _ (show (p.withOffset 216#64).id ≠ data.id from hne),
    sourceRead_splice_ne _ (show (p.withOffset 208#64).id ≠ data.id from hne)]
  simp only [live_splice_storeBlock, Pointer.withOffset, append32Block, sourceRead, readBlock,
    Pointer.offsetInBits, BitVec.add_zero]
  rfl

theorem append32BufferedMemory_block (m : MemoryState) (p data : Pointer) (hne : p.id ≠ data.id) :
    (append32BufferedMemory m p data).live? p.id =
      append32Block (m.live? p.id) p.offset (sourceRead m data 256) 32#64 64#64 := by
  unfold append32BufferedMemory
  simp only [sourceRead_splice_ne _ (show (p.withOffset 216#64).id ≠ data.id from hne),
    sourceRead_splice_ne _ (show (p.withOffset 208#64).id ≠ data.id from hne)]
  simp only [live_splice_storeBlock, Pointer.withOffset, append32Block, sourceRead, readBlock,
    Pointer.offsetInBits]
  rfl

theorem append32Block_live (b : LiveBlock) (off : BitVec 64) (input : BitVec 256)
    (bufferOffset count : BitVec 64) :
    ∃ after : LiveBlock, append32Block (some b) off input bufferOffset count = some after ∧
      after.length = b.length := by
  unfold append32Block storeBlock
  simp only [Option.map_some]
  exact ⟨_, rfl, rfl⟩

theorem append32Block_count (b : LiveBlock) (off : BitVec 64) (input : BitVec 256)
    (bufferOffset count : BitVec 64) (hfit : 8 * off.toNat + 224*8 ≤ b.lengthInBits) :
    readBlock (append32Block (some b) off input bufferOffset count) (off + 200#64) 64 = count := by
  have hadd : (off + 200#64).toNat ≤ off.toNat + 200 := by
    change (off.toNat + 200) % 2^64 ≤ off.toNat + 200
    exact Nat.mod_le _ _
  have hbound : 8 * (off + 200#64).toNat + 64 ≤ b.lengthInBits := by
    omega
  unfold append32Block storeBlock readBlock
  simp only [Option.map_some]
  apply extractLsb'_spliceBits
  exact hbound

theorem initBlock_live (b : LiveBlock) (off : BitVec 64) :
    ∃ after : LiveBlock, initBlock (some b) off = some after ∧ after.length = b.length := by
  unfold initBlock storeBlock
  simp only [Option.map_some]
  exact ⟨_, rfl, rfl⟩

theorem initBlock_count (b : LiveBlock) (off : BitVec 64)
    (hfit : 8 * off.toNat + 224*8 ≤ b.lengthInBits) :
    readBlock (initBlock (some b) off) (off + 200#64) 64 = 0#64 := by
  have hadd : (off + 200#64).toNat ≤ off.toNat + 200 := by
    change (off.toNat + 200) % 2^64 ≤ off.toNat + 200
    exact Nat.mod_le _ _
  have hbound : 8 * (off + 200#64).toNat + 192 ≤ b.lengthInBits := by omega
  unfold initBlock storeBlock readBlock
  simp only [Option.map_some]
  rw [extractLsb'_spliceBits_of_subrange _ _ _ _ (by omega) (by omega) hbound]
  simp

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
