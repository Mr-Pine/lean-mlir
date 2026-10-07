import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceInitialize
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourcePrograms
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerParameterizedSource

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer Firedancer.Common
attribute [local irreducible] init append core finish initMemory
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- The block projection of one concrete store. Invalid input blocks remain
invalid; the call contract only invokes this model on a live context. -/
def storeBlock (blk : Option LiveBlock) (off : BitVec 64) (value : BitVec w) : Option LiveBlock :=
  blk.map fun b => { b with bytes := spliceBits b.bytes (8 * off.toNat) value }

theorem live_splice_storeBlock (m : MemoryState) (p : Pointer) (value : BitVec w) :
    (m.splice p value).live? p.id = storeBlock (m.live? p.id) p.offset value := by
  cases h : m.live? p.id with
  | none => simp only [splicedDead h, storeBlock, Option.map_none]
  | some b => rw [splicedLive _ _ _ h]; rfl

/-- Exact initialized block, including unchanged buffer/magic/padding bytes. -/
def initBlock (b : Option LiveBlock) (off : BitVec 64) : Option LiveBlock :=
  let b := storeBlock b (off + 128#64) (7640891576956012808#64)
  let b := storeBlock b (off + 136#64) (13503953896175478587#64)
  let b := storeBlock b (off + 144#64) (4354685564936845355#64)
  let b := storeBlock b (off + 152#64) (11912009170470909681#64)
  let b := storeBlock b (off + 160#64) (5840696475078001361#64)
  let b := storeBlock b (off + 168#64) (11170449401992604703#64)
  let b := storeBlock b (off + 176#64) (2270897969802886507#64)
  let b := storeBlock b (off + 184#64) (6620516959819538809#64)
  storeBlock b (off + 200#64) (0#192)

def initModel (b : Option LiveBlock) (off : BitVec 64) : Option (Option LiveBlock) :=
  some (initBlock b off)

theorem initMemory_block (m : MemoryState) (p : Pointer) :
    (initMemory m p).live? p.id = initBlock (m.live? p.id) p.offset := by
  simp only [initMemory, initBlock, live_splice_storeBlock, Pointer.withOffset]

theorem initMemory_other (m : MemoryState) (p : Pointer) (q : BlockId) (hne : q ≠ p.id) :
    (initMemory m p).live? q = m.live? q := by
  simp only [initMemory, live?_splice_ne (show (p.withOffset _).id ≠ q from Ne.symm hne)]

attribute [local irreducible] initBlock storeBlock

theorem init_call (p : Pointer) (s : GlobalState) (hr : Fits s.mem p (224 * 8)) :
    StateT.run (runFunction (init.denote (Ctxt.Valuation.singleton (.value p)))) s =
      .value ([.value p]ₕ, s.popFrame (initMemory s.mem p)) :=
  @run_runFunction _ (init.denote (Ctxt.Valuation.singleton (.value p))) s
    {s with mem := initMemory s.mem p} ([.value p]ₕ) (init_body p s hr)

/-- The source-corresponding initializer supplies the existing verifier's
whole local call contract. No RIR/SLLVM state equality or SHA axiom is used. -/
theorem init_contract : FiredancerShaInitBy programs initModel := by
  unfold FiredancerShaInitBy ParameterizedSource.Firedancer.Common.Sha512InitBy
  simp only [programs_init]
  intro p s hwf hr
  constructor
  · intro b hb
    have heq : initBlock (s.mem.live? p.id) p.offset = b := Option.some.inj hb
    have hc := init_call p s (Fits.mono hr (by decide : 224 * 8 ≤ 256 * 8))
    refine ⟨s.popFrame (initMemory s.mem p), hc, ?_, rfl, rfl, ?_, ?_⟩
    · intro q hq
      exact live?_killFrom_of_le hq
    · intro q hq
      change ((initMemory s.mem p).killFrom s.alloc.nextFreeBlock).live? q = s.mem.live? q
      by_cases hlt : q.id < s.alloc.nextFreeBlock
      · rw [live?_killFrom_of_lt hlt, initMemory_other _ _ _ hq]
      · rw [live?_killFrom_of_le (by omega), hwf q (by omega)]
    · change ((initMemory s.mem p).killFrom s.alloc.nextFreeBlock).live? p.id = b
      rw [live?_killFrom_of_lt (lt_nextFreeBlock_of_fits hwf hr), initMemory_block, heq]
  · intro h
    cases h

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
