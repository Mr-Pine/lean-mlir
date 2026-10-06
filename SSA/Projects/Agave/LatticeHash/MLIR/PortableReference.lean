import SSA.Projects.Agave.LatticeHash.MLIR.PortableCompressionProof
import SSA.Projects.Agave.LatticeHash.Blake3Reference

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open Blake3Compression

/-- The independently compiled portable helper returns the existing source-shaped
portable BLAKE3 compression result, with arbitrary input and caller memory. -/
theorem portable_reference_run (s : GlobalState) (out cvp msg : Pointer)
    (cv : AgaveBlake3Reference.CV) (b : AgaveBlake3Reference.Block)
    (counter : BitVec 64) (len flags : BitVec 8)
    (hout : Fits s.mem out 512) (hcvp : Fits s.mem cvp 256) (hmsg : Fits s.mem msg 512)
    (rcv : ∀ i : Fin 8, readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (cv i))
    (rmsg : ∀ i : Fin 16, readWord? (msg.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem =
      some (AgaveBlake3Reference.load32 b i)) :
    StateT.run (agave_portable_compress_pre.denote (Ctxt.Valuation.ofHVector
      [.value flags, .value counter, .value len, .value msg, .value cvp, .value out]ₕ)) s =
    .value ([]ₕ, {s with mem := portableCompressionMemory s.mem out (AgaveBlake3Reference.compressPre cv b (len.zeroExtend 32) counter (flags.zeroExtend 32))}) := by
  simpa only [AgaveBlake3Reference.compressPre_eq] using
    portable_compression_run s out cvp msg cv (AgaveConcrete.decodeBlock b) counter len flags
      hout hcvp hmsg rcv rmsg

/-- Call/return refines the portable model and preserves the caller's allocations. -/
theorem portable_reference_conforms (s : GlobalState) (hs : s.WF) (out cvp msg : Pointer)
    (cv : AgaveBlake3Reference.CV) (b : AgaveBlake3Reference.Block)
    (counter : BitVec 64) (len flags : BitVec 8)
    (hout : Fits s.mem out 512) (hcvp : Fits s.mem cvp 256) (hmsg : Fits s.mem msg 512)
    (rcv : ∀ i : Fin 8, readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (cv i))
    (rmsg : ∀ i : Fin 16, readWord? (msg.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem =
      some (AgaveBlake3Reference.load32 b i)) :
    ∃ s' : GlobalState,
      StateT.run (runFunction (agave_portable_compress_pre.denote (Ctxt.Valuation.ofHVector
        [.value flags, .value counter, .value len, .value msg, .value cvp, .value out]ₕ))) s = .value ([]ₕ,s') ∧
      s' ≈ ({s with mem := portableCompressionMemory s.mem out (AgaveBlake3Reference.compressPre cv b (len.zeroExtend 32) counter (flags.zeroExtend 32))} : GlobalState) := by
  have hrun := portable_reference_run s out cvp msg cv b counter len flags hout hcvp hmsg rcv rmsg
  have hcall := run_runFunction hrun
  with_reducible exact ⟨_, hcall, portableCompressionMemory_popFrame s hs out
    (AgaveBlake3Reference.compressPre cv b (len.zeroExtend 32) counter (flags.zeroExtend 32))⟩

end AgaveLatticeHash.MLIR
