import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionBlocks
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionEntryMemory

namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution

def entryEnv (E : Env program.Γ) (g : Globals) (s : GlobalState) (n : BitVec 64) :
    Env program.Γ :=
  E[%0 := .value 1, %1 := .value 32, %2 := .value 127, %3 := .value 64,
    %4 := .value 128, %5 := .value g.address0, %6 := .value 64, %7 := .value 192,
    %8 := .value 0, %9 := .value (-1), %10 := .value 0, %11 := .value 1,
    %12 := .value 1, %13 := .value 7, %14 := .value 9223372036854775680,
    %15 := .value 0, %16 := .value 208,
    %17 := .value (scratchSlot s), %18 := .value (contextSlot s),
    %19 := .value (finalSlot s), %20 := .value ((scratchSlot s).add 32#64),
    %21 := .value ((contextSlot s).add 127#64),
    %22 := .value ((contextSlot s).add 128#64),
    %23 := .value ((contextSlot s).add 192#64),
    %24 := .value ((contextSlot s).add 128#64),
    %25 := .value ((contextSlot s).add 127#64),
    %26 := .value 64, %27 := .value 64, %28 := .value 1, %29 := .value 64,
    %30 := .value (BitVec.ofBool (n.ult 64#64))]

set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

private theorem modifyGet_apply (f : GlobalState → α × GlobalState) (s : GlobalState) :
    (modifyGet f : EffectM α) s = .value (f s) := rfl

/-- Exact execution of all three allocations, the R/A copies, the SHA IV and
context fields, and the first length test in the imported entry block. -/
theorem entry_block (p : Primitives) (g : Globals) (sha : Sha512Model)
    (E : Env program.Γ) (s : GlobalState) (rptr aptr : Pointer)
    (r a : BitVec 256) (n : BitVec 64)
    (hR : E.read (%arg2) = .value rptr) (hA : E.read (%arg1) = .value aptr)
    (hn : E.read (%arg4) = .value n) (hwf : s.WF)
    (hr : SmallRange s.mem rptr 32) (ha : SmallRange s.mem aptr 32)
    (hrbytes : s.mem.readAt rptr 256 = r) (habytes : s.mem.readAt aptr 256 = a)
    (hiv : SmallRange s.mem g.address0 64)
    (hivbytes : s.mem.readAt g.address0 512 = initialWords) :
    (program p g).runFrom E 0 s =
      (program p g).runFrom (entryEnv E g s n) (if n.toNat < 64 then 2 else 1)
        (entryState s r a) := by
  change E.args 2 = .value rptr at hR
  change E.args 1 = .value aptr at hA
  change E.args 4 = .value n at hn
  have hsl := scratch_live hwf
  have hcl := context_live hwf
  have hr0 : Fits (allocated s).mem rptr 256 := (allocated_live hwf hr).fits
  have hs0 : Fits (allocated s).mem (scratchSlot s) 256 :=
    (smallRange_mono hsl (k := 32) (by decide)).fits
  have ha1 : Fits (scratchR s r) aptr 256 := (allocated_live hwf ha).fits.storeAt
  have hs1 : Fits (scratchR s r) ((scratchSlot s).add 32#64) 256 :=
    (hsl.storeAt _ _).fits_add (k := 32) (count := 32) (by decide)
  have hs2 : Fits (scratchRA s r a) (scratchSlot s) 1016 :=
    ((hsl.storeAt _ _).storeAt _ _).fits
  have hc2 : Fits (scratchRA s r a) (contextSlot s) 1016 :=
    (smallRange_mono ((hcl.storeAt _ _).storeAt _ _) (k := 127) (by decide)).fits
  have hc3 : Fits (copiedRA s r a) ((contextSlot s).add 127#64) 8 :=
    context_count_fits (((hcl.storeAt _ _).storeAt _ _).storeAt _ _)
  have hc4 : Fits ((copiedRA s r a).storeAt ((contextSlot s).add 127#64) 64#8)
      ((contextSlot s).add 128#64) 512 :=
    context_chain_fits ((((hcl.storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _)
  have hiv4 : Fits ((copiedRA s r a).storeAt ((contextSlot s).add 127#64) 64#8)
      g.address0 512 := ((((allocated_live hwf hiv).storeAt _ _).storeAt _ _).storeAt _ _).fits.storeAt
  have hc5 : Fits (((copiedRA s r a).storeAt ((contextSlot s).add 127#64) 64#8).storeAt
      ((contextSlot s).add 128#64) initialWords) ((contextSlot s).add 192#64) 128 :=
    context_blocks_fits (((((hcl.storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _)
  have hc6 : Fits (entryState s r a).mem ((contextSlot s).add 127#64) 8 :=
    context_count_fits (entry_context_live hwf)
  have hdR : (Range.of (scratchSlot s) 256).Disjoint (Range.of rptr 256) :=
    Or.inl (scratch_ne_caller hwf hr)
  have hdA : (Range.of ((scratchSlot s).add 32#64) 256).Disjoint (Range.of aptr 256) :=
    Or.inl (scratch_ne_caller hwf ha)
  have hdCopy : (Range.of (contextSlot s) 1016).Disjoint (Range.of (scratchSlot s) 1016) :=
    Or.inl (scratch_ne_context s).symm
  have hdIV : (Range.of ((contextSlot s).add 128#64) 512).Disjoint (Range.of g.address0 512) :=
    Or.inl (context_ne_caller hwf hiv)
  have hreadR : (allocated s).mem.readAt rptr 256 = r := (allocated_read hwf hr 256).trans hrbytes
  have hreadA : (scratchR s r).readAt aptr 256 = a := by
    unfold scratchR
    rw [readAt_storeAt_of_id_ne _ _ _ _ _ (scratch_ne_caller hwf ha)]
    exact (allocated_read hwf ha 256).trans habytes
  have hreadIV : ((copiedRA s r a).storeAt ((contextSlot s).add 127#64) 64#8).readAt
      g.address0 512 = initialWords := by
    unfold copiedRA scratchRA scratchR
    rw [readAt_storeAt_of_id_ne _ ((contextSlot s).add 127#64) _ _ _ (context_ne_caller hwf hiv),
      readAt_storeAt_of_id_ne _ (contextSlot s) _ _ _ (context_ne_caller hwf hiv),
      readAt_storeAt_of_id_ne _ ((scratchSlot s).add 32#64) _ _ _ (scratch_ne_caller hwf hiv),
      readAt_storeAt_of_id_ne _ (scratchSlot s) _ _ _ (scratch_ne_caller hwf hiv)]
    exact (allocated_read hwf hiv 512).trans hivbytes
  have hreadCount : (entryState s r a).mem.readAt ((contextSlot s).add 127#64) 8 = 64#8 := by
    apply BitVec.eq_of_toNat_eq
    have hc := (entry_context sha s hwf r a).pendingCount
    simpa [Agave.Ed25519.Bridge.Challenge.bytesOf] using hc
  have hg20 : Operation.gepInboundsLive (scratchR s r) (.value (scratchSlot s))
      [.value (32 : Int)] = .value ((scratchSlot s).add 32#64) :=
    (hsl.storeAt _ _).gep (k := 32) (by decide)
  have hg21 : Operation.gepInboundsLive (copiedRA s r a) (.value (contextSlot s))
      [.value (127 : Int)] = .value ((contextSlot s).add 127#64) :=
    (((hcl.storeAt _ _).storeAt _ _).storeAt _ _).gep (k := 127) (by decide)
  have hg22 : Operation.gepInboundsLive
      ((copiedRA s r a).storeAt ((contextSlot s).add 127#64) 64#8) (.value (contextSlot s))
      [.value (128 : Int)] = .value ((contextSlot s).add 128#64) :=
    ((((hcl.storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).gep (k := 128) (by decide)
  have hg23 : Operation.gepInboundsLive
      (((copiedRA s r a).storeAt ((contextSlot s).add 127#64) 64#8).storeAt
        ((contextSlot s).add 128#64) initialWords) (.value (contextSlot s))
      [.value (192 : Int)] = .value ((contextSlot s).add 192#64) :=
    (((((hcl.storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).gep (k := 192) (by decide)
  have hg24 : Operation.gepInboundsLive (entryState s r a).mem (.value (contextSlot s))
      [.value (128 : Int)] = .value ((contextSlot s).add 128#64) :=
    (entry_context_live hwf).gep (k := 128) (by decide)
  have hg25 : Operation.gepInboundsLive (entryState s r a).mem (.value (contextSlot s))
      [.value (127 : Int)] = .value ((contextSlot s).add 127#64) :=
    (entry_context_live hwf).gep (k := 127) (by decide)
  simp only [entryState, initContext, copiedRA, scratchRA, scratchR, BitVec.ofNat_eq_ofNat] at ha1 hs1 hs2 hc2 hc3 hc4 hiv4 hc5 hc6 hreadA hreadIV hreadCount hg20 hg21 hg22 hg23 hg24 hg25
  simp only [allocated, scratchSlot, contextSlot, finalSlot] at hr0 hs0 ha1 hs1 hs2 hc2 hc3 hc4 hiv4 hc5 hc6 hdR hdA hdCopy hdIV hreadR hreadA hreadIV hreadCount hg20 hg21 hg22 hg23 hg24 hg25
  have hb : (program.bb0 g).run program.blockParams E s =
      .value ((entryEnv E g s n, .inr (if n.toNat < 64 then 2 else 1)), entryState s r a) := by
    have hmsb : (64#8).msb = false := by decide
    have hssub : (128#64).ssubOverflow 64#64 = false := by decide
    have husub : (128#64).usubOverflow 64#64 = false := by decide
    by_cases hshort : n.toNat < 64 <;>
      simp [BasicBlock.run, program.bb0, entryEnv, entryState, initContext, copiedRA, scratchRA, scratchR,
        List.foldlM_cons, List.foldlM_nil, Instr.run, run_alloca, modifyGet_apply, Ty.wrap,
        Operation.memcpy, Operation.store, Operation.load, UnOp.compute, BinOp.compute,
        Operation.zext, Operation.icmp, Operation.sub,
        EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
        Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
        GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
        hR, hA, hn, hr0, hs0, ha1, hs1, hs2, hc2, hc3, hc4, hiv4, hc5, hc6,
        hdR, hdA, hdCopy, hdIV, hreadR, hreadA, hreadIV, hreadCount,
        hg20, hg21, hg22, hg23, hg24, hg25,
        throwUBIf, ofBool_eq_one_iff, BitVec.ult, hshort, hmsb, hssub, husub,
        allocated, scratchSlot, contextSlot, finalSlot]
  rw [Func.runFrom_eq]
  change ((program.bb0 g).run program.blockParams E s >>= fun x =>
    (program p g).continue x.1.1 x.1.2 x.2) = _
  rw [hb]
  rfl

end Agave.Ed25519.Verifier.Execution.Challenge
