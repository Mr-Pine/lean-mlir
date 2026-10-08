import SSA.Projects.Agave.Ed25519.Bridge.FiredancerReachableSourcePrefix
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendInitSemantic
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMFinishAdapter

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer Firedancer.Common
open FinishCorrect
set_option maxRecDepth 24000
set_option maxHeartbeats 2000000
attribute [local irreducible] init append core finish initBlock append32Block

namespace VerifierPrefix

def context : Pointer := ⟨⟨0⟩, 0⟩
def data : Pointer := ⟨⟨1⟩, 0⟩
def memory (b : LiveBlock) (input : BitVec 256) : MemoryState :=
  ⟨((∅ : Std.HashMap BlockId Block).insert ⟨0⟩ (.live b)).insert ⟨1⟩ (.live ⟨32, input⟩)⟩

theorem context_live (b : LiveBlock) (input : BitVec 256) :
    (memory b input).live? context.id = some b := by
  simp only [memory, context, MemoryState.live?, MemoryState.getElem?_eq,
    Std.HashMap.getElem?_insert,
    show ((⟨1⟩ : BlockId) == ⟨0⟩) = false by decide,
    beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]

theorem data_live (b : LiveBlock) (input : BitVec 256) :
    (memory b input).live? data.id = some ⟨32, input⟩ := by
  simp only [memory, data, MemoryState.live?, MemoryState.getElem?_eq,
    Std.HashMap.getElem?_insert, beq_self_eq_true, ↓reduceIte]

theorem data_fits (b : LiveBlock) (input : BitVec 256) :
    Fits (memory b input) data (8*32) :=
  ⟨⟨32, input⟩, getElem?_of_live? (data_live b input), by change 256 ≤ 256; decide⟩

theorem context_small (b : LiveBlock) (input : BitVec 256) (hlen : b.length = 256) :
    ∀ c, (memory b input).live? context.id = some c → c.length < 2^63 := by
  intro c hc
  have he : c = b := Option.some.inj (hc.symm.trans (context_live b input))
  simp only [he, hlen]
  decide

theorem data_small (b : LiveBlock) (input : BitVec 256) :
    ∀ c, (memory b input).live? data.id = some c → c.length < 2^63 := by
  intro c hc
  have he : c = ⟨32, input⟩ := Option.some.inj (hc.symm.trans (data_live b input))
  subst c
  change (32 : Nat) < 2^63
  decide

theorem data_word (b : LiveBlock) (input : BitVec 256) :
    sourceRead (memory b input) data 256 = input := by
  unfold sourceRead
  rw [data_live]
  change input.extractLsb' 0 256 = input
  simp

theorem data_bytes (b : LiveBlock) (input : BitVec 256) :
    sourceReadBytes (memory b input) data 32 = bytesOf (n := 32) input := by
  unfold sourceReadBytes bytesOf
  congr 1
  funext i
  have hi : i.val < 2^64 := by omega
  unfold sourceRead
  rw [show (data.withOffset (BitVec.ofNat 64 i.val)).id = data.id from rfl, data_live]
  simp only [Pointer.offsetInBits, Pointer.withOffset, data,
    show (0 : BitVec 64) = 0#64 by decide, BitVec.zero_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mul_comm]


end VerifierPrefix

/-- The concrete initialized block represents the empty stream, independently
of the allocation identifier or other caller memory. -/
theorem verifierInitialBlock_represents (b : LiveBlock)
    (hb : verifierInitialBlock = some b) (hlen : b.length = 256) :
    BlockRepresents b 0 [] [] := by
  let fresh : LiveBlock := ⟨256, 0#_⟩
  let m := VerifierPrefix.memory fresh 0
  let p := VerifierPrefix.context
  have hf : Fits m p (224*8) :=
    ⟨fresh, getElem?_of_live? (VerifierPrefix.context_live fresh 0), by decide⟩
  have hr := init_memory_represents_source m p hf (VerifierPrefix.context_small fresh 0 rfl)
  have hl : (initMemory m p).live? p.id = some b := by
    rw [initMemory_block, VerifierPrefix.context_live]
    exact hb
  exact BlockRepresents.of_context hr hl rfl (by rw [hlen]; decide)

/-- The first concrete output block represents exactly the signature's original
R bytes; bytes are never obtained by reencoding the decoded curve point. -/
theorem verifierAfterR_represents (r : BitVec 256) (b : LiveBlock)
    (hb : verifierAfterR r = some b) (hlen : b.length = 256) :
    BlockRepresents b 0 [] (bytesOf (n := 32) r) := by
  obtain ⟨before, hbefore, hbeforelen⟩ := verifierInitialBlock_live
  let m := VerifierPrefix.memory before r
  let p := VerifierPrefix.context
  let d := VerifierPrefix.data
  have hp := verifierInitialBlock_represents before hbefore hbeforelen m p
    (VerifierPrefix.context_live before r) rfl
  have hc : sourceRead m (p.withOffset 200#64) 64 = 0#64 := hp.pendingCount
  have hr := append32_represents_source m p d [] [] hp (VerifierPrefix.data_fits before r)
    (by decide) (VerifierPrefix.context_small before r hbeforelen)
    (VerifierPrefix.data_small before r) hc
  have hshort : (bytesOf (n := 32) r).length < 128 := by simp [bytesOf]
  have hr' : ContextRepresents (append32Memory m p d) p [] (bytesOf (n := 32) r) := by
    simpa only [m, d, VerifierPrefix.data_bytes, List.nil_append, StreamSpec.complete,
      StreamSpec.pending, Nat.div_eq_of_lt hshort, Nat.mul_zero, List.take_zero,
      List.drop_zero] using hr
  have hl : (append32Memory m p d).live? p.id = some b := by
    rw [append32Memory_block m p d (by decide), VerifierPrefix.context_live,
      VerifierPrefix.data_word]
    simpa only [verifierAfterR, hbefore, p, VerifierPrefix.context] using hb
  exact BlockRepresents.of_context hr' hl rfl (by rw [hlen]; decide)

/-- The second concrete output block represents the original R ++ A bytes. -/
theorem verifierAfterA_represents (r a : BitVec 256) (b : LiveBlock)
    (hb : verifierAfterA r a = some b) (hlen : b.length = 256) :
    BlockRepresents b 0 [] (bytesOf (n := 32) r ++ bytesOf (n := 32) a) := by
  obtain ⟨before, hbefore, hbeforelen⟩ := verifierAfterR_live r
  let m := VerifierPrefix.memory before a
  let p := VerifierPrefix.context
  let d := VerifierPrefix.data
  have hp := verifierAfterR_represents r before hbefore hbeforelen m p
    (VerifierPrefix.context_live before a) rfl
  have hc : sourceRead m (p.withOffset 200#64) 64 = 32#64 := by
    simpa only [bytesOf, List.length_ofFn] using hp.pendingCount
  have hr := append32_buffered_represents_source m p d [] (bytesOf (n := 32) r) hp
    (VerifierPrefix.data_fits before a) (by decide)
    (VerifierPrefix.context_small before a hbeforelen) (VerifierPrefix.data_small before a) hc
  have hshort : (bytesOf (n := 32) r ++ bytesOf (n := 32) a).length < 128 := by simp [bytesOf]
  have hr' : ContextRepresents (append32BufferedMemory m p d) p []
      (bytesOf (n := 32) r ++ bytesOf (n := 32) a) := by
    simpa only [m, d, VerifierPrefix.data_bytes, List.nil_append, StreamSpec.complete,
      StreamSpec.pending, Nat.div_eq_of_lt hshort, Nat.mul_zero, List.take_zero,
      List.drop_zero] using hr
  have hl : (append32BufferedMemory m p d).live? p.id = some b := by
    rw [append32BufferedMemory_block m p d (by decide), VerifierPrefix.context_live,
      VerifierPrefix.data_word]
    simpa only [verifierAfterA, hbefore, p, VerifierPrefix.context] using hb
  exact BlockRepresents.of_context hr' hl rfl (by rw [hlen]; decide)

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
