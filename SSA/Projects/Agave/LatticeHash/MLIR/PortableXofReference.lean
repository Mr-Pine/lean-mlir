/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofProof
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofReadback
import SSA.Projects.Agave.LatticeHash.MLIR.PortableObservation

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer Blake3Compression

attribute [local irreducible] agave_portable_compress_xof portableCompressionMemory
  AgaveBlake3Reference.compressXofWords

/-- Execute the actual upstream XOF helper and retain its byte-backed memory
    result as the independent portable reference's sixteen output words. -/
theorem portable_xof_reference_run (s : GlobalState) (out cvp msg : Pointer)
    (cv : AgaveBlake3Reference.CV) (b : AgaveBlake3Reference.Block)
    (counter : BitVec 64) (len flags : BitVec 8)
    (hout : Fits s.mem out 512) (hcvp : Fits s.mem cvp 256) (hmsg : Fits s.mem msg 512)
    (hwrap : out.offset.toNat + 64 ≤ 2^64)
    (rcv : ∀ i : Fin 8, readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (cv i))
    (rmsg : ∀ i : Fin 16, readWord? (msg.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem =
      some (AgaveBlake3Reference.load32 b i)) :
    StateT.run (agave_portable_compress_xof.denote (Ctxt.Valuation.ofHVector
      [.value flags, .value counter, .value len, .value msg, .value cvp, .value out]ₕ)) s =
    .value ([]ₕ, {s with mem := portableCompressionMemory s.mem out (AgaveBlake3Reference.compressXofWords cv b (len.zeroExtend 32) counter (flags.zeroExtend 32))}) := by
  simpa only [AgaveBlake3Reference.compressXofWords_eq] using
    portable_xof_run s out cvp msg cv (AgaveConcrete.decodeBlock b) counter len flags
      hout hcvp hmsg hwrap rcv rmsg

/-- Actual function entry/return preserves caller allocation ownership while
    producing the independent reference XOF words. -/
theorem portable_xof_reference_conforms (s : GlobalState) (hs : s.WF) (out cvp msg : Pointer)
    (cv : AgaveBlake3Reference.CV) (b : AgaveBlake3Reference.Block)
    (counter : BitVec 64) (len flags : BitVec 8)
    (hout : Fits s.mem out 512) (hcvp : Fits s.mem cvp 256) (hmsg : Fits s.mem msg 512)
    (hwrap : out.offset.toNat + 64 ≤ 2^64)
    (rcv : ∀ i : Fin 8, readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (cv i))
    (rmsg : ∀ i : Fin 16, readWord? (msg.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem =
      some (AgaveBlake3Reference.load32 b i)) :
    ∃ s' : GlobalState,
      StateT.run (runFunction (agave_portable_compress_xof.denote (Ctxt.Valuation.ofHVector
        [.value flags, .value counter, .value len, .value msg, .value cvp, .value out]ₕ))) s = .value ([]ₕ,s') ∧
      s' ≈ ({s with mem := portableCompressionMemory s.mem out (AgaveBlake3Reference.compressXofWords cv b (len.zeroExtend 32) counter (flags.zeroExtend 32))} : GlobalState) := by
  have hrun := portable_xof_reference_run s out cvp msg cv b counter len flags hout hcvp hmsg hwrap rcv rmsg
  have hcall := run_runFunction hrun
  with_reducible exact ⟨_, hcall, portableCompressionMemory_popFrame s hs out
    (AgaveBlake3Reference.compressXofWords cv b (len.zeroExtend 32) counter (flags.zeroExtend 32))⟩

/-- Actual XOF execution at the same concrete six-argument caller interface. -/
def PortableCompressionCall.XofReturns (p : PortableCompressionCall) (s : GlobalState) : Prop :=
  StateT.run (agave_portable_compress_xof.denote (Ctxt.Valuation.ofHVector
    [.value p.flags, .value p.counter, .value p.len, .value p.msg, .value p.cvp, .value p.out]ₕ))
    p.state = .value ([]ₕ, s)

/-- The compiled XOF helper returns all 64 bytes through actual output-memory reads. -/
theorem portable_xof_call_readback (p : PortableCompressionCall) (hp : p.Valid) :
    ∃ after : GlobalState, p.XofReturns after ∧ ∀ i : Fin 64,
      readWord? (p.out.withOffset (BitVec.ofNat 64 i.val)) 8 after.mem =
        some (AgaveBlake3Reference.serialize (AgaveBlake3Reference.compressXofWords
          p.cv p.block (p.len.zeroExtend 32) p.counter (p.flags.zeroExtend 32)) i) := by
  rcases hp with ⟨ho, hc, hm, hw, hcv, hmsg⟩
  let words := AgaveBlake3Reference.compressXofWords p.cv p.block (p.len.zeroExtend 32)
    p.counter (p.flags.zeroExtend 32)
  let after : GlobalState := {p.state with mem := portableCompressionMemory p.state.mem p.out words}
  refine ⟨after, portable_xof_reference_run p.state p.out p.cvp p.msg p.cv p.block
    p.counter p.len p.flags ho hc hm hw hcv hmsg, ?_⟩
  intro i
  exact portableCompressionMemory_read_byte p.state.mem p.out words ho hw i

/-- For every LtHash output-block counter, actual portable XOF execution stores
    the reference root-output bytes. The supplied root descriptor remains an
    input premise; this does not execute portable chunk-state construction. -/
theorem portable_xof_root_output_readback (m : AgaveBlake3Reference.Message) (counter : Fin 32)
    (p : PortableCompressionCall) (hp : p.Valid)
    (hcv : p.cv = (AgaveBlake3Reference.finalChunk m).cv)
    (hblock : p.block = (AgaveBlake3Reference.finalChunk m).buf)
    (hcounter : p.counter = BitVec.ofNat 64 counter.val)
    (hlen : p.len = BitVec.ofNat 8 (AgaveBlake3Reference.finalChunk m).bufLen)
    (hflags : p.flags = rootFlags8 (AgaveBlake3Reference.finalChunk m).blocksCompressed) :
    ∃ after : GlobalState, p.XofReturns after ∧ ∀ i : Fin 64,
      readWord? (p.out.withOffset (BitVec.ofNat 64 i.val)) 8 after.mem =
        some (AgaveBlake3Reference.rootOutput (AgaveBlake3Reference.finalChunk m) counter.val i) := by
  obtain ⟨after, hrun, hread⟩ := portable_xof_call_readback p hp
  have hsize : (AgaveBlake3Reference.finalChunk m).bufLen ≤ 64 :=
    (AgaveBatchControl.root_size_bounds m.length).1
  have hext : p.len.zeroExtend 32 = BitVec.ofNat 32 (AgaveBlake3Reference.finalChunk m).bufLen := by
    rw [hlen]
    exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)
  refine ⟨after, hrun, ?_⟩
  intro i
  rw [hread, hcv, hblock, hcounter, hext, hflags, rootFlags8_extend]
  rfl

end AgaveLatticeHash.MLIR
