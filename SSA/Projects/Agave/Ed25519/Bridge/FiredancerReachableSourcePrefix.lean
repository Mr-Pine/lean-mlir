import SSA.Projects.Agave.Ed25519.Bridge.FiredancerReachableSourceInit
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendReachable

/-! The first two source append contracts are theorems, with their exact
context blocks determined by the signature and public-key bytes.  These
adapters do not assume execution, compression, or digest equality. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer Firedancer.Common

set_option maxRecDepth 24000
set_option maxHeartbeats 2000000
attribute [local irreducible] init append core finish initBlock append32Block

def verifierInitialBlock : Option LiveBlock :=
  initBlock (some { length := 256, bytes := 0#_ }) 0

def verifierAfterR (r : BitVec 256) : Option LiveBlock :=
  append32Block verifierInitialBlock 0 r 0#64 32#64

def verifierAfterA (r a : BitVec 256) : Option LiveBlock :=
  append32Block (verifierAfterR r) 0 a 32#64 64#64

theorem verifierInitialBlock_live :
    ∃ b : LiveBlock, verifierInitialBlock = some b ∧ b.length = 256 :=
  initBlock_live ⟨256, 0#_⟩ 0

theorem verifierInitialBlock_count :
    readBlock verifierInitialBlock (0 + 200#64) 64 = 0#64 :=
  initBlock_count ⟨256, 0#_⟩ 0 (by decide)

theorem verifierAfterR_live (r : BitVec 256) :
    ∃ b : LiveBlock, verifierAfterR r = some b ∧ b.length = 256 := by
  obtain ⟨before, hb, hlen⟩ := verifierInitialBlock_live
  obtain ⟨after, ha, hal⟩ := append32Block_live before 0 r 0#64 32#64
  exact ⟨after, by simpa only [verifierAfterR, hb] using ha, hal.trans hlen⟩

theorem verifierAfterA_live (r a : BitVec 256) :
    ∃ b : LiveBlock, verifierAfterA r a = some b ∧ b.length = 256 := by
  obtain ⟨before, hb, hlen⟩ := verifierAfterR_live r
  obtain ⟨after, ha, hal⟩ := append32Block_live before 0 a 32#64 64#64
  exact ⟨after, by simpa only [verifierAfterA, hb] using ha, hal.trans hlen⟩

theorem verifierAfterR_count (r : BitVec 256) :
    readBlock (verifierAfterR r) (0 + 200#64) 64 = 32#64 := by
  obtain ⟨before, hb, hlen⟩ := verifierInitialBlock_live
  have hf : 8 * (0#64).toNat + 224*8 ≤ before.lengthInBits := by
    simp only [LiveBlock.lengthInBits, hlen]
    decide
  simpa only [verifierAfterR, hb] using append32Block_count before 0 r 0#64 32#64 hf

theorem verifierAfterA_count (r a : BitVec 256) :
    readBlock (verifierAfterA r a) (0 + 200#64) 64 = 64#64 := by
  obtain ⟨before, hb, hlen⟩ := verifierAfterR_live r
  have hf : 8 * (0#64).toNat + 224*8 ≤ before.lengthInBits := by
    simp only [LiveBlock.lengthInBits, hlen]
    decide
  simpa only [verifierAfterA, hb] using append32Block_count before 0 a 32#64 64#64 hf

/-- The actual first append, from the verifier's initialized private block. -/
theorem verifierAppendR (k : BitVec (80*64)) (r : BitVec 256) :
    FiredancerReachableAppend programs k verifierInitialBlock (verifierAfterR r) 0
      (bytesOf (n := 32) r) := by
  obtain ⟨before, hb, hlen⟩ := verifierInitialBlock_live
  have hf : 8 * (0#64).toNat + 224*8 ≤ before.lengthInBits := by
    simp only [LiveBlock.lengthInBits, hlen]
    decide
  have hc : readBlock (some before) (0 + 200#64) 64 = 0#64 := by
    simpa only [hb] using verifierInitialBlock_count
  simpa only [verifierAfterR, hb] using append32_reachable k before 0 r hf hc

/-- The actual second append, from the first append's exact output block. -/
theorem verifierAppendA (k : BitVec (80*64)) (r a : BitVec 256) :
    FiredancerReachableAppend programs k (verifierAfterR r) (verifierAfterA r a) 0
      (bytesOf (n := 32) a) := by
  obtain ⟨before, hb, hlen⟩ := verifierAfterR_live r
  have hf : 8 * (0#64).toNat + 224*8 ≤ before.lengthInBits := by
    simp only [LiveBlock.lengthInBits, hlen]
    decide
  have hc : readBlock (some before) (0 + 200#64) 64 = 32#64 := by
    simpa only [hb] using verifierAfterR_count r
  simpa only [verifierAfterA, hb] using append32_buffered_reachable k before 0 a hf hc

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
