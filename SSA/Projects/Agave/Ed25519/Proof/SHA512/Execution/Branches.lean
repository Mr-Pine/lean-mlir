import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Contracts

/-! Execution of the actual short- and long-padding blocks. Each external
call is kept as an explicit cutpoint with its exact arguments and input state.
The local primitive contracts in `Contracts` can discharge these cutpoints. -/

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution

@[simp] theorem blockParams_1 : program.blockParams 1 = .nil := rfl
@[simp] theorem blockParams_2 : program.blockParams 2 = .nil := rfl
@[simp] theorem blockParams_3 : program.blockParams 3 = .nil := rfl

/-- Write the big-endian bit-count at the final sixteen bytes. -/
def writeLength (s : GlobalState) (buffer : Pointer) (length : BitVec 128) : GlobalState :=
  {s with mem := s.mem.storeAt (buffer.add 112#64) length}

/-- The imported memcpy reads the full source block before writing scratch. -/
def copyBlock (s : GlobalState) (buffer scratch : Pointer) : GlobalState :=
  {s with mem := s.mem.storeAt scratch (s.mem.readAt buffer 1024)}

/-- The second long-path block has 112 zero bytes followed by the length. -/
def clearPrefix (s : GlobalState) (buffer : Pointer) : GlobalState :=
  {s with mem := s.mem.storeAt buffer 0#896}

set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

/-- Exact execution of imported bb2, including the inbounds address, length
store, full-block copy, one-block compression call, and transition to bb3. -/
theorem short_block (p : Primitives) (E : Env program.Γ)
    (s after : GlobalState) (buffer scratch chain : Pointer) (length : BitVec 128)
    (hbuffer : E.read (%84) = .value buffer)
    (hscratch : E.read (%81) = .value scratch)
    (hchain : E.read (%151) = .value chain)
    (hlength : E.read (%161) = .value length)
    (h112 : E.read (%10) = .value 112#64)
    (h128 : E.read (%2) = .value 128#64)
    (h1 : E.read (%12) = .value 1#64)
    (hb : SmallRange s.mem buffer 128) (ht : SmallRange s.mem scratch 128)
    (hne : scratch.id ≠ buffer.id)
    (hcall : p.sha512Compress (.cons (.value chain) (.cons (.value scratch)
      (.cons (.value 1#64) .nil))) (copyBlock (writeLength s buffer length) buffer scratch) =
        .value (.nil, after)) :
    (program p).runFrom E 2 s =
      (program p).runFrom (E[%167 := .value (buffer.add 112#64)]) 3 after := by
  have hg : Operation.gepInboundsLive s.mem (.value buffer) [.value (112 : Int)] =
      .value (buffer.add 112#64) := hb.gep (k := 112) (by decide)
  have hf : Fits s.mem (buffer.add 112#64) 128 :=
    hb.fits_add (k := 112) (count := 16) (by decide)
  have hsrc : Fits (writeLength s buffer length).mem buffer 1024 := hb.fits.storeAt
  have hdst : Fits (writeLength s buffer length).mem scratch 1024 := ht.fits.storeAt
  have hd : (Range.of scratch 1024).Disjoint (Range.of buffer 1024) := Or.inl hne
  dsimp only [copyBlock, writeLength] at hcall hsrc hdst
  have hrun : (program.bb2 p).run program.blockParams E s =
      .value ((E[%167 := .value (buffer.add 112#64)], .inr 3), after) := by
    simp [BasicBlock.run, program.bb2,
      List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.memcpy, Operation.store,
      EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
      GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
      hbuffer, hscratch, hchain, hlength, h112, h128, h1,
      hg, hf, hsrc, hdst, hd, hcall, throwUBIf]
  rw [Func.runFrom_eq]
  change ((program.bb2 p).run program.blockParams E s >>= fun x =>
    (program p).continue x.1.1 x.1.2 x.2) = _
  rw [hrun]
  rfl

/-- Exact execution of imported bb1. Both calls have count one; the second
input is formed only after the first compression has completed. -/
theorem long_block (p : Primitives) (E : Env program.Γ)
    (s middle after : GlobalState) (buffer first last chain : Pointer)
    (length : BitVec 128)
    (hbuffer : E.read (%84) = .value buffer)
    (hfirst : E.read (%83) = .value first)
    (hlast : E.read (%82) = .value last)
    (hchain : E.read (%151) = .value chain)
    (hlength : E.read (%161) = .value length)
    (h112 : E.read (%10) = .value 112#64)
    (h128 : E.read (%2) = .value 128#64)
    (h1 : E.read (%12) = .value 1#64)
    (h0 : E.read (%8) = .value 0#8)
    (hb : SmallRange s.mem buffer 128) (ht : SmallRange s.mem first 128)
    (hbm : SmallRange middle.mem buffer 128) (hlm : SmallRange middle.mem last 128)
    (hne : first.id ≠ buffer.id) (hneLast : last.id ≠ buffer.id)
    (hcallFirst : p.sha512Compress (.cons (.value chain) (.cons (.value first)
      (.cons (.value 1#64) .nil))) (copyBlock s buffer first) = .value (.nil, middle))
    (hcallLast : p.sha512Compress (.cons (.value chain) (.cons (.value last)
      (.cons (.value 1#64) .nil)))
        (copyBlock (writeLength (clearPrefix middle buffer) buffer length) buffer last) =
          .value (.nil, after)) :
    (program p).runFrom E 1 s =
      (program p).runFrom (E[%166 := .value (buffer.add 112#64)]) 3 after := by
  have hf : Fits middle.mem buffer 896 := by
    simpa only [Pointer.add_zero] using
      hbm.fits_add (k := 0) (count := 112) (by decide)
  have hg : Operation.gepInboundsLive (clearPrefix middle buffer).mem
      (.value buffer) [.value (112 : Int)] = .value (buffer.add 112#64) :=
    (hbm.storeAt _ _).gep (k := 112) (by decide)
  have hlen : Fits (clearPrefix middle buffer).mem (buffer.add 112#64) 128 :=
    (hbm.storeAt _ _).fits_add (k := 112) (count := 16) (by decide)
  have hsrc : Fits (writeLength (clearPrefix middle buffer) buffer length).mem buffer 1024 :=
    (hbm.storeAt _ _).fits.storeAt
  have hdst : Fits (writeLength (clearPrefix middle buffer) buffer length).mem last 1024 :=
    (hlm.storeAt _ _).fits.storeAt
  have hdFirst : (Range.of first 1024).Disjoint (Range.of buffer 1024) := Or.inl hne
  have hdLast : (Range.of last 1024).Disjoint (Range.of buffer 1024) := Or.inl hneLast
  dsimp only [copyBlock, writeLength, clearPrefix] at hcallFirst hcallLast hg hlen hsrc hdst
  have hrun : (program.bb1 p).run program.blockParams E s =
      .value ((E[%166 := .value (buffer.add 112#64)], .inr 3), after) := by
    simp [BasicBlock.run, program.bb1,
      List.foldlM_cons, List.foldlM_nil, Instr.run,
      Operation.memcpy, Operation.memset, Operation.store,
      EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
      GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
      hbuffer, hfirst, hlast, hchain, hlength, h112, h128, h1, h0,
      hb.fits, ht.fits, hf, hg, hlen, hsrc, hdst, hdFirst, hdLast,
      hcallFirst, hcallLast, throwUBIf]
  rw [Func.runFrom_eq]
  change ((program.bb1 p).run program.blockParams E s >>= fun x =>
    (program p).continue x.1.1 x.1.2 x.2) = _
  rw [hrun]
  rfl

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
