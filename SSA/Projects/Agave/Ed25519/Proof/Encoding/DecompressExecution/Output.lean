import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Cutpoint
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.OutputMemory
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Terminal

/-! Actual final success memcpy and Option-tag control, starting at compiler
instruction cut points. All field computation remains before these cut points;
the premises here are only registers, allocated byte ranges, and memcpy noalias. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

/-- Instructions 56--58 of the original success block copy the prepared point. -/
theorem success_copy_body (p : Primitives) (E : ⟪program.Γ⟫)
    (s : GlobalState) (out point : Pointer)
    (hout : E.read (%arg0) = .value out)
    (hpoint : E.read (%36) = .value point)
    (h8 : E.read (%8) = .value 8#64)
    (h160 : E.read (%29) = .value 160#64)
    (houtput : SmallRange s.mem out 168) (hsource : SmallRange s.mem point 160)
    (hdisjoint : (Range.of (out.add 8#64) 1280).Disjoint (Range.of point 1280)) :
    (program.bb1 p).runBodyFrom E 56 s =
      .value (E[%140 := .value (out.add 8#64)],
        {s with mem := s.mem.storeAt (out.add 8#64) (s.mem.readAt point 1280)}) := by
  change E.args 0 = .value out at hout
  have hgep := houtput.gep (k := 8) (by decide)
  change Operation.gepInboundsLive s.mem (.value out) [.value (8 : Int)] =
    .value (out.add 8#64) at hgep
  have hfd : Fits s.mem (out.add 8#64) 1280 :=
    houtput.fits_add (k := 8) (count := 160) (by decide)
  have hfs : Fits s.mem point 1280 := hsource.fits
  simp [BasicBlock.runBodyFrom, program.bb1, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Operation.memcpy, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, mlir_env, mlir_effect, GepIndex.inboundsOffset,
    Operation.gepInboundsIndex, Operation.GepSignedRange, hgep,
    hout, hpoint, h8, h160, hfd, hfs, hdisjoint, throwUBIf]

/-- The success suffix and common return block write the precise payload and tag1. -/
theorem success_copy_run (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (out point : Pointer)
    (hout : E.read (%arg0) = .value out)
    (hpoint : E.read (%36) = .value point)
    (h8 : E.read (%8) = .value 8#64)
    (h160 : E.read (%29) = .value 160#64)
    (hone : E.read (%6) = .value 1#64)
    (houtput : SmallRange s.mem out 168) (hsource : SmallRange s.mem point 160)
    (hdisjoint : (Range.of (out.add 8#64) 1280).Disjoint (Range.of point 1280)) :
    resume p g 1 56 E s = .value (.nil, successState s out (s.mem.readAt point 1280)) := by
  have hb := success_copy_body p E s out point hout hpoint h8 h160 houtput hsource hdisjoint
  unfold resume
  rw [Cutpoint.of_body (program p g) 1 56 E _ s _ hb]
  have he : (program.bb1 p).exit.run program.blockParams
      (E[%140 := .value (out.add 8#64)])
      {s with mem := s.mem.storeAt (out.add 8#64) (s.mem.readAt point 1280)} =
    .value (((E[%140 := .value (out.add 8#64)])[%141 := .value 1#64], .inr 2),
      {s with mem := s.mem.storeAt (out.add 8#64) (s.mem.readAt point 1280)}) := by
    simp [program.bb1, Exit.run, Jump.run, program.blockParams,
      Regs.read_nil, Regs.read_cons, Env.writeMany_nil, Env.writeMany_cons,
      EffectM.pure_eq, mlir_env, hone]
    rfl
  change (do
    let ((E', exit), t) ← (program.bb1 p).exit.run program.blockParams
      (E[%140 := .value (out.add 8#64)])
      {s with mem := s.mem.storeAt (out.add 8#64) (s.mem.readAt point 1280)}
    Func.continue (func := program p g) E' exit t) = _
  rw [he]
  change (program p g).runFrom
    ((E[%140 := .value (out.add 8#64)])[%141 := .value 1#64]) 2
    {s with mem := s.mem.storeAt (out.add 8#64) (s.mem.readAt point 1280)} = _
  apply terminal_run
  · exact (Fits.mono (by decide) houtput.fits).storeAt
  · simpa only [mlir_env] using hout
  · simp only [mlir_env]

/-- The zero sqrt flag follows the original rejection edge and writes only tag0. -/
theorem rejection_run (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (out : Pointer)
    (hout : E.read (%arg0) = .value out)
    (hflag : E.read (%93) = .value 0#8)
    (hzero : E.read (%20) = .value 0#8)
    (htag : E.read (%14) = .value 0#64)
    (houtput : SmallRange s.mem out 168) :
    resume p g 0 137 E s = .value (.nil, rejectionState s out) := by
  rw [decide_path p g E s 0#8 hflag hzero htag]
  simp only [ite_true]
  apply terminal_run
  · exact Fits.mono (by decide) houtput.fits
  · simpa only [mlir_env] using hout
  · simp only [mlir_env]

end Agave.Ed25519.Encoding.Decompress.Execution.Decode
