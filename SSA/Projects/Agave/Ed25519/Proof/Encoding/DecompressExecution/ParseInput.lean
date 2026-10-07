import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Cutpoint
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Input
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.LimbMemory

/-! The actual overlapping unaligned input loads and five parsed-Y stores.
All loads precede all stores, so the sequential RIR lemma needs no input/output
nonalias premise. The original LLVM metadata remains in the imported program. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)

/-- Registers produced by original bb0 instructions 45--72. -/
def parsedEnv (E : ⟪program.Γ⟫) (s : GlobalState) (input dst : Pointer) : ⟪program.Γ⟫ :=
  E[%40 := .value (s.mem.readAt input 64),
    %41 := .value (inputWords s input 0),
    %42 := .value (input.add 6#64),
    %43 := .value (s.mem.readAt (input.add 6#64) 64),
    %44 := .value (s.mem.readAt (input.add 6#64) 64 >>> 3),
    %45 := .value (inputWords s input 1),
    %46 := .value (input.add 12#64),
    %47 := .value (s.mem.readAt (input.add 12#64) 64),
    %48 := .value (s.mem.readAt (input.add 12#64) 64 >>> 6),
    %49 := .value (inputWords s input 2),
    %50 := .value (input.add 19#64),
    %51 := .value (s.mem.readAt (input.add 19#64) 64),
    %52 := .value (s.mem.readAt (input.add 19#64) 64 >>> 1),
    %53 := .value (inputWords s input 3),
    %54 := .value (input.add 24#64),
    %55 := .value (s.mem.readAt (input.add 24#64) 64),
    %56 := .value (s.mem.readAt (input.add 24#64) 64 >>> 12),
    %57 := .value (inputWords s input 4),
    %58 := .value (dst.add 8#64),
    %59 := .value (dst.add 16#64),
    %60 := .value (dst.add 24#64),
    %61 := .value (dst.add 32#64)]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
theorem parsed_segment (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (input dst : Pointer)
    (hinput : E.read (%arg1) = .value input) (hdst : E.read (%35) = .value dst)
    (h1 : E.read (%1) = .value 2251799813685247#64)
    (h2 : E.read (%2) = .value 6#64) (h3 : E.read (%3) = .value 3#64)
    (h4 : E.read (%4) = .value 12#64) (h5 : E.read (%5) = .value 19#64)
    (h6 : E.read (%6) = .value 1#64) (h7 : E.read (%7) = .value 24#64)
    (h8 : E.read (%8) = .value 8#64) (h9 : E.read (%9) = .value 16#64)
    (h10 : E.read (%10) = .value 32#64)
    (hi : SmallRange s.mem input 32) (hd : SmallRange s.mem dst 40) :
    Cutpoint.segment (program p g) 0 45 28 E s =
      .value (parsedEnv E s input dst,
        {s with mem := storeLimbs s.mem dst (inputWords s input)}) := by
  change List.foldlM Instr.run E (((program.bb0 p g).body.drop 45).take 28) s = _
  dsimp only [program.bb0, List.drop, List.take]
  change E.args 1 = .value input at hinput
  have hif0 := hi.fits_add (k := 0) (count := 8) (by decide)
  have hif6 := hi.fits_add (k := 6) (count := 8) (by decide)
  have hif12 := hi.fits_add (k := 12) (count := 8) (by decide)
  have hif19 := hi.fits_add (k := 19) (count := 8) (by decide)
  have hif24 := hi.fits_add (k := 24) (count := 8) (by decide)
  have hig6 := hi.gep (k := 6) (by decide)
  have hig12 := hi.gep (k := 12) (by decide)
  have hig19 := hi.gep (k := 19) (by decide)
  have hig24 := hi.gep (k := 24) (by decide)
  have hd0 := hd.fits_add (k := 0) (count := 8) (by decide)
  have hdg8 := (hd.storeAt dst (inputWords s input 0)).gep (k := 8) (by decide)
  have hdf8 := (hd.storeAt dst (inputWords s input 0)).fits_add (k := 8) (count := 8) (by decide)
  have hdg16 := ((hd.storeAt dst (inputWords s input 0)).storeAt (dst.add 8#64) (inputWords s input 1)).gep (k := 16) (by decide)
  have hdf16 := ((hd.storeAt dst (inputWords s input 0)).storeAt (dst.add 8#64) (inputWords s input 1)).fits_add (k := 16) (count := 8) (by decide)
  have hdg24 := (((hd.storeAt dst (inputWords s input 0)).storeAt (dst.add 8#64) (inputWords s input 1)).storeAt (dst.add 16#64) (inputWords s input 2)).gep (k := 24) (by decide)
  have hdf24 := (((hd.storeAt dst (inputWords s input 0)).storeAt (dst.add 8#64) (inputWords s input 1)).storeAt (dst.add 16#64) (inputWords s input 2)).fits_add (k := 24) (count := 8) (by decide)
  have hdg32 := ((((hd.storeAt dst (inputWords s input 0)).storeAt (dst.add 8#64) (inputWords s input 1)).storeAt (dst.add 16#64) (inputWords s input 2)).storeAt (dst.add 24#64) (inputWords s input 3)).gep (k := 32) (by decide)
  have hdf32 := ((((hd.storeAt dst (inputWords s input 0)).storeAt (dst.add 8#64) (inputWords s input 1)).storeAt (dst.add 16#64) (inputWords s input 2)).storeAt (dst.add 24#64) (inputWords s input 3)).fits_add (k := 32) (count := 8) (by decide)
  simp only [Pointer.add_zero] at hif0 hd0
  norm_num only [Nat.cast_ofNat] at hig6 hig12 hig19 hig24 hdg8 hdg16 hdg24 hdg32
  simp [inputWords] at hdg8 hdg16 hdg24 hdg32 hdf8 hdf16 hdf24 hdf32
  simp only [List.foldlM_cons, List.foldlM_nil, EffectM.bind_eq, EffectM.pure_eq]
  simp (config := {maxSteps := 200000}) (disch := decide) [List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, Operation.load, Operation.store, Operation.and,
    Operation.lshr, Ty.flatten, Ty.unflatten, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, mlir_env, mlir_effect, GepIndex.inboundsOffset,
    Operation.gepInboundsIndex, Operation.GepSignedRange,
    hinput, hdst, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    hif0, hif6, hif12, hif19, hif24, hig6, hig12, hig19, hig24,
    hd0, hdg8, hdg16, hdg24, hdg32, hdf8, hdf16, hdf24, hdf32,
    throwUBIf, parsedEnv, storeLimbs, inputWords]

/-- The actual entry parsing slice reaches the first field call with parsed Y. -/
theorem parsed_resume (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (input dst : Pointer)
    (hinput : E.read (%arg1) = .value input) (hdst : E.read (%35) = .value dst)
    (h1 : E.read (%1) = .value 2251799813685247#64)
    (h2 : E.read (%2) = .value 6#64) (h3 : E.read (%3) = .value 3#64)
    (h4 : E.read (%4) = .value 12#64) (h5 : E.read (%5) = .value 19#64)
    (h6 : E.read (%6) = .value 1#64) (h7 : E.read (%7) = .value 24#64)
    (h8 : E.read (%8) = .value 8#64) (h9 : E.read (%9) = .value 16#64)
    (h10 : E.read (%10) = .value 32#64)
    (hi : SmallRange s.mem input 32) (hd : SmallRange s.mem dst 40) :
    resume p g 0 45 E s = resume p g 0 73 (parsedEnv E s input dst)
      {s with mem := storeLimbs s.mem dst (inputWords s input)} := by
  exact Cutpoint.after_segment (program p g) 0 45 28 E _ s _
    (parsed_segment p g E s input dst hinput hdst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hi hd)

/-- Exact limb bytes for every 256-bit input, including noncanonical field encodings. -/
theorem parsed_readback (s : GlobalState) (input dst : Pointer) (bytes : BitVec 256)
    (hi : SmallRange s.mem input 32) (hd : SmallRange s.mem dst 40)
    (hbytes : s.mem.readAt input 256 = bytes) :
    Verifier.Execution.Dalek.ReadBytes
      {s with mem := storeLimbs s.mem dst (inputWords s input)} dst 40
      (limbBytes (fromBytesWord bytes)) := by
  rw [inputWords_eq s input bytes hi hbytes]
  exact storeLimbs_readBytes s dst (fromBytesWord bytes) hd

end Agave.Ed25519.Encoding.Decompress.Execution.Decode
