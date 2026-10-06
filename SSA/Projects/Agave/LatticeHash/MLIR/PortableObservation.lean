/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.Integration

/-! Explicit XOF observations of the actual portable compression's stored
pre-feed-forward state. Feed-forward and byte serialization below are observers,
not claims that additional portable MLIR instructions have been extracted. -/
namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open Blake3Compression

/-- Read the real stored words, then apply the explicit BLAKE3 XOF observation. -/
def observeXofWord (cv : AgaveBlake3Reference.CV) (out : Pointer) (mem : MemoryState)
    (i : Fin 16) : Option Word := do
  let x ← readWord? (out.withOffset (BitVec.ofNat 64 (4*i.val))) 32 mem
  if h : i.val < 8 then
    let y ← readWord? (out.withOffset (BitVec.ofNat 64 (4*(i.val+8)))) 32 mem
    pure (x ^^^ y)
  else pure (x ^^^ cv ⟨i.val-8, by omega⟩)

theorem observeXofWord_reference (mem : MemoryState) (out : Pointer)
    (cv : AgaveBlake3Reference.CV) (b : AgaveBlake3Reference.Block)
    (len : Word) (counter : BitVec 64) (flags : Word)
    (hread : ∀ i : Fin 16, readWord? (out.withOffset (BitVec.ofNat 64 (4*i.val))) 32 mem =
      some (AgaveBlake3Reference.compressPre cv b len counter flags i)) (i : Fin 16) :
    observeXofWord cv out mem i = some (AgaveBlake3Reference.compressXofWords cv b len counter flags i) := by
  have hspec : AgaveBlake3Reference.compressXofWords cv b len counter flags =
      feedForward (· ^^^ ·) cv (AgaveBlake3Reference.compressPre cv b len counter flags) := by
    rw [AgaveBlake3Reference.compressXofWords_eq, AgaveBlake3Reference.compressPre_eq]
    rfl
  rw [hspec]
  unfold observeXofWord feedForward
  rw [hread i]
  split
  next hi =>
    rw [hread ⟨i.val+8, by omega⟩]
    rfl
  next hi => rfl

/-- The actual portable call supplies every word needed by XOF feed-forward.
This theorem applies to each output counter independently. -/
theorem portable_call_xof_observation (p : PortableCompressionCall) (hp : p.Valid) :
    ∃ after : GlobalState, p.Returns after ∧ ∀ i : Fin 16,
      observeXofWord p.cv p.out after.mem i =
        some (AgaveBlake3Reference.compressXofWords p.cv p.block (p.len.zeroExtend 32)
          p.counter (p.flags.zeroExtend 32) i) := by
  rcases hp with ⟨ho, hc, hm, hw, hcv, hmsg⟩
  obtain ⟨after, hrun, hread⟩ := portable_reference_readback p.state p.out p.cvp p.msg
    p.cv p.block p.counter p.len p.flags ho hc hm hw hcv hmsg
  exact ⟨after, hrun, fun i => observeXofWord_reference after.mem p.out p.cv p.block
    (p.len.zeroExtend 32) p.counter (p.flags.zeroExtend 32) hread i⟩

def rootFlags8 (blocks : Nat) : BitVec 8 := if blocks = 0 then 11 else 10

theorem rootFlags8_extend (blocks : Nat) :
    (rootFlags8 blocks).zeroExtend 32 = ((AgaveBlake3Reference.startFlag blocks ||| 2) ||| 8) := by
  by_cases h : blocks = 0 <;> simp [rootFlags8, AgaveBlake3Reference.startFlag, h]

/-- For any of the 32 output-block counters, observing the actual portable
pre-compression memory produces the independent reference's 64 output bytes.
The root descriptor is supplied as input; execution of portable chunk-state
construction and of feed-forward/serialization is outside this theorem. -/
theorem portable_root_output_observation (m : AgaveBlake3Reference.Message) (counter : Fin 32)
    (p : PortableCompressionCall) (hp : p.Valid)
    (hcv : p.cv = (AgaveBlake3Reference.finalChunk m).cv)
    (hblock : p.block = (AgaveBlake3Reference.finalChunk m).buf)
    (hcounter : p.counter = BitVec.ofNat 64 counter.val)
    (hlen : p.len = BitVec.ofNat 8 (AgaveBlake3Reference.finalChunk m).bufLen)
    (hflags : p.flags = rootFlags8 (AgaveBlake3Reference.finalChunk m).blocksCompressed) :
    ∃ after : GlobalState, p.Returns after ∧ ∀ i : Fin 64,
      (observeXofWord p.cv p.out after.mem ⟨i.val/4, by omega⟩).map
        (fun w => w.extractLsb' (8*(i.val%4)) 8) =
      some (AgaveBlake3Reference.rootOutput (AgaveBlake3Reference.finalChunk m) counter.val i) := by
  obtain ⟨after, hrun, hread⟩ := portable_call_xof_observation p hp
  have hsize : (AgaveBlake3Reference.finalChunk m).bufLen ≤ 64 :=
    (AgaveBatchControl.root_size_bounds m.length).1
  have hext : p.len.zeroExtend 32 = BitVec.ofNat 32 (AgaveBlake3Reference.finalChunk m).bufLen := by
    rw [hlen]
    exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)
  refine ⟨after, hrun, ?_⟩
  intro i
  rw [hread, Option.map_some, hcv, hblock, hcounter, hext, hflags, rootFlags8_extend]
  rfl

end AgaveLatticeHash.MLIR
