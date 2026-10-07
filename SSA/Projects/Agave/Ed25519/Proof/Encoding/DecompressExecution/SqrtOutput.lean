import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Cutpoint
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Linked
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.LimbMemory

/-! Exact final sqrt_ratio_i control and stores. The selected root is computed
before this cut point; this suffix forms the square flag from the two proved
byte equalities, executes the actual black_box body, and returns flag/root. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open Verifier.Execution.Dalek (ReadBytes smallRange_add disjoint_add_subrange)

def outputState (s : GlobalState) (out : Pointer) (flag : BitVec 8)
    (root : BitVec 320) : GlobalState :=
  {alloc := ⟨s.alloc.nextFreeBlock + 1⟩,
    mem := (s.mem.storeAt out flag).storeAt (out.add 8#64) root}

theorem outputState_live (h : SmallRange s.mem q bytes) (out : Pointer)
    (flag : BitVec 8) (root : BitVec 320) :
    SmallRange (outputState s out flag root).mem q bytes :=
  (h.storeAt _ _).storeAt _ _

theorem outputState_root (h : SmallRange s.mem out 48)
    (flag : BitVec 8) (root : BitVec 320) :
    ReadBytes (outputState s out flag root) (out.add 8#64) 40 root := by
  have hr := smallRange_add h (k := 8) (count := 40) (by decide)
  exact ⟨(hr.storeAt _ _).storeAt _ _, MemoryState.readAt_storeAt_self hr.fits.storeAt root⟩

theorem outputState_flag (h : SmallRange s.mem out 48)
    (flag : BitVec 8) (root : BitVec 320) :
    (outputState s out flag root).mem.readAt out 8 = flag := by
  have hoff := Pointer.offsetInBits_add (h.no_wrap (k := 8) (by decide))
  norm_num only [BitVec.toNat_ofNat, Nat.reduceMod] at hoff
  have hd : (Range.of (out.add 8#64) 320).Disjoint (Range.of out 8) := by
    simp only [Range.Disjoint, Range.of, Pointer.add_id, hoff]
    omega
  change ((s.mem.storeAt out flag).storeAt (out.add 8#64) root).readAt out 8 = flag
  rw [MemoryState.readAt_storeAt_disjoint hd]
  exact MemoryState.readAt_storeAt_self (Fits.mono (by decide) h.fits) flag

/-- The two comparison bytes are normalized 0/1; their emitted OR is exactly
the square predicate. No test for canonical input or small order is added. -/
theorem choice_or (first second : Bool) :
    (if first then 1#8 else 0#8) ||| (if second then 1#8 else 0#8) =
      if first || second then 1#8 else 0#8 := by
  cases first <;> cases second <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- Actual instructions 1047--1055 and original return terminator. -/
theorem output_run (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (out root : Pointer) (first second : BitVec 8)
    (hwf : s.WF) (ho : SmallRange s.mem out 48) (hr : SmallRange s.mem root 40)
    (hd : (Range.of out 384).Disjoint (Range.of root 320))
    (hout : E.read (%arg0) = .value out) (hroot : E.read (%79) = .value root)
    (hfirst : E.read (%430) = .value first) (hsecond : E.read (%236) = .value second)
    (h8 : E.read (%3) = .value 8#64) (h40 : E.read (%1) = .value 40#64) :
    Cutpoint.resume (program sqrtRatioPrimitives g) 0 1047 E s =
      .value (.nil, outputState s out (first ||| second) (s.mem.readAt root 320)) := by
  have hbox := BlackBox.program_call (first ||| second) s hwf
  have hbyte := Fits.mono (by decide : 8 ≤ 384) ho.fits
  have hcopy := (ho.fits_add (k := 8) (count := 40) (by decide)).storeAt
    (q := out) (x := first ||| second)
  have hrootfit := hr.fits.storeAt (q := out) (x := first ||| second)
  have hgep := (ho.storeAt out (first ||| second)).gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  have htagdis := disjoint_add_subrange ho hd.symm (k := 0) (count := 1) (by decide)
  have hcopydis := disjoint_add_subrange ho hd.symm (k := 8) (count := 40) (by decide)
  simp only [Pointer.add_zero] at htagdis
  have hrootread : (s.mem.storeAt out (first ||| second)).readAt root 320 =
      s.mem.readAt root 320 := MemoryState.readAt_storeAt_disjoint htagdis.symm _
  change E.args 0 = .value out at hout
  dsimp only [BlackBox.program.args] at hbox
  unfold Cutpoint.resume
  dsimp only [program, program.entry, BasicBlock.runBodyFrom, List.drop]
  simp [ List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, Operation.or, Operation.store, Operation.memcpy,
    Ty.flatten, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange, sqrtRatioPrimitives, hbox, BlackBox.program.args,
    hout, hroot, hfirst, hsecond, h8, h40, hbyte, hcopy, hrootfit, hgep,
    hcopydis.symm, hrootread, throwUBIf, outputState, GlobalState.alloca,
    Exit.run, Regs.read_nil, Func.continue]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio
