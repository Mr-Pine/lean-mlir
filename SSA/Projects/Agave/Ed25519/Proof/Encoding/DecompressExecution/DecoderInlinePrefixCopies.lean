import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixReadback
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderOuterExecution

/-! Original post-sqrt flag load and four copies (bb0:122--136).
The current state is the sqrt call's result; all addresses and constants are
those established by the actual entry allocation. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
open SmallOrder.Execution (PrivateFrame)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def copiedRootState (s t : GlobalState) : GlobalState :=
  {t with mem := t.mem.storeAt (slot7 s) (t.mem.readAt ((slot0 s).add 8#64) 320)}

def copiedPairState (s t : GlobalState) : GlobalState :=
  let u := copiedRootState s t
  {u with mem := u.mem.storeAt ((slot7 s).add 40#64) (u.mem.readAt (slot5 s) 320)}

def copiedXState (s t : GlobalState) : GlobalState :=
  let u := copiedPairState s t
  {u with mem := u.mem.storeAt (slot9 s) (u.mem.readAt (slot7 s) 320)}

def copiedXYState (s t : GlobalState) : GlobalState :=
  let u := copiedXState s t
  {u with mem := u.mem.storeAt (slot8 s) (u.mem.readAt ((slot7 s).add 40#64) 320)}

noncomputable def copiedRootEnv (g : Globals) (s t : GlobalState) (out input : Pointer) : Env program.Γ :=
  (sqrtInputEnv g s out input)[%93 := .value (t.mem.readAt (slot0 s) 8),
    %94 := .value ((slot0 s).add 8#64)]

noncomputable def copiedPairEnv (g : Globals) (s t : GlobalState) (out input : Pointer) : Env program.Γ :=
  (copiedRootEnv g s t out input)[%95 := .value ((slot7 s).add 40#64)]

theorem copy_root_segment (p : Primitives) (g : Globals) (s t : GlobalState)
    (out input : Pointer) (h0 : SmallRange t.mem (slot0 s) 48)
    (h7 : SmallRange t.mem (slot7 s) 80) :
    Cutpoint.segment (program p g) 0 122 3 (sqrtInputEnv g s out input) t =
      .value (copiedRootEnv g s t out input, copiedRootState s t) := by
  have e30 : (sqrtInputEnv g s out input).read (%30) = .value (slot0 s) := rfl
  have e37 : (sqrtInputEnv g s out input).read (%37) = .value (slot7 s) := rfl
  have e8 : (sqrtInputEnv g s out input).read (%8) = .value 8#64 := rfl
  have e19 : (sqrtInputEnv g s out input).read (%19) = .value 40#64 := rfl
  have hg := h0.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hg
  have hf0 := h0.fits_add (k := 0) (count := 1) (by decide)
  have hfs := h0.fits_add (k := 8) (count := 40) (by decide)
  have hfd := h7.fits_add (k := 0) (count := 40) (by decide)
  simp only [Pointer.add_zero] at hf0 hfd
  have hd : (Range.of (slot7 s) 320).Disjoint (Range.of ((slot0 s).add 8#64) 320) := by
    left; intro h
    have := congrArg BlockId.id h
    simp only [Range.of, Pointer.add_id, slot7_id, slot0_id] at this
    omega
  change List.foldlM Instr.run (sqrtInputEnv g s out input)
    (((program.bb0 p g).body.drop 122).take 3) t = _
  dsimp only [program.bb0, List.drop, List.take]
  simp (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load, Operation.memcpy,
    Operation.gepInboundsIndex, GepIndex.inboundsOffset, Operation.GepSignedRange,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect,
    e30,e37,e8,e19,hg,hf0,hfs,hfd,hd,throwUBIf,copiedRootEnv,copiedRootState]

theorem copy_y_segment (p : Primitives) (g : Globals) (s t : GlobalState)
    (out input : Pointer) (h5 : SmallRange t.mem (slot5 s) 40)
    (h7 : SmallRange t.mem (slot7 s) 80) :
    Cutpoint.segment (program p g) 0 125 3 (copiedRootEnv g s t out input)
      (copiedRootState s t) = .value (copiedPairEnv g s t out input, copiedPairState s t) := by
  have e37 : (copiedRootEnv g s t out input).read (%37) = .value (slot7 s) := rfl
  have e35 : (copiedRootEnv g s t out input).read (%35) = .value (slot5 s) := rfl
  have e19 : (copiedRootEnv g s t out input).read (%19) = .value 40#64 := rfl
  have hg := (h7.storeAt (slot7 s) (t.mem.readAt ((slot0 s).add 8#64) 320)).gep (k := 40) (by decide)
  norm_num only [Nat.cast_ofNat] at hg
  have hfs := h5.fits
  have hfd := h7.fits_add (k := 40) (count := 40) (by decide)
  have hd : (Range.of ((slot7 s).add 40#64) 320).Disjoint (Range.of (slot5 s) 320) := by
    left; intro h
    have := congrArg BlockId.id h
    simp only [Range.of, Pointer.add_id, slot7_id, slot5_id] at this
    omega
  change List.foldlM Instr.run (copiedRootEnv g s t out input)
    (((program.bb0 p g).body.drop 125).take 3) (copiedRootState s t) = _
  dsimp only [program.bb0, List.drop, List.take]
  simp (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.memcpy,
    Operation.gepInboundsIndex, GepIndex.inboundsOffset, Operation.GepSignedRange,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect,
    e37,e35,e19,hg,hfs,hfd,hd,throwUBIf,Fits.storeAt_iff,copiedPairEnv,copiedRootState,copiedPairState]

theorem copy_x_segment (p : Primitives) (g : Globals) (s t : GlobalState)
    (out input : Pointer) (h7 : SmallRange t.mem (slot7 s) 80)
    (h9 : SmallRange t.mem (slot9 s) 40) :
    Cutpoint.segment (program p g) 0 128 6 (copiedPairEnv g s t out input)
      (copiedPairState s t) = .value (copiedPairEnv g s t out input, copiedXState s t) := by
  have e37 : (copiedPairEnv g s t out input).read (%37) = .value (slot7 s) := rfl
  have e39 : (copiedPairEnv g s t out input).read (%39) = .value (slot9 s) := rfl
  have e19 : (copiedPairEnv g s t out input).read (%19) = .value 40#64 := rfl
  have hfs := h7.fits_add (k := 0) (count := 40) (by decide)
  simp only [Pointer.add_zero] at hfs
  have hfd := h9.fits
  have hd : (Range.of (slot9 s) 320).Disjoint (Range.of (slot7 s) 320) := by
    left; intro h
    have := congrArg BlockId.id h
    simp only [Range.of, slot9_id, slot7_id] at this
    omega
  change List.foldlM Instr.run (copiedPairEnv g s t out input)
    (((program.bb0 p g).body.drop 128).take 6) (copiedPairState s t) = _
  dsimp only [program.bb0, List.drop, List.take]
  simp (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.memcpy,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect,
    e37,e39,e19,hfs,hfd,hd,throwUBIf,Fits.storeAt_iff,copiedPairState,copiedRootState,copiedXState]

theorem copy_y_final_segment (p : Primitives) (g : Globals) (s t : GlobalState)
    (out input : Pointer) (h7 : SmallRange t.mem (slot7 s) 80)
    (h8 : SmallRange t.mem (slot8 s) 40) :
    Cutpoint.segment (program p g) 0 134 3 (copiedPairEnv g s t out input)
      (copiedXState s t) = .value (copiedPairEnv g s t out input, copiedXYState s t) := by
  have e95 : (copiedPairEnv g s t out input).read (%95) = .value ((slot7 s).add 40#64) := rfl
  have e38 : (copiedPairEnv g s t out input).read (%38) = .value (slot8 s) := rfl
  have e19 : (copiedPairEnv g s t out input).read (%19) = .value 40#64 := rfl
  have hfs := h7.fits_add (k := 40) (count := 40) (by decide)
  have hfd := h8.fits
  have hd : (Range.of (slot8 s) 320).Disjoint (Range.of ((slot7 s).add 40#64) 320) := by
    left; intro h
    have := congrArg BlockId.id h
    simp only [Range.of, Pointer.add_id, slot8_id, slot7_id] at this
    omega
  change List.foldlM Instr.run (copiedPairEnv g s t out input)
    (((program.bb0 p g).body.drop 134).take 3) (copiedXState s t) = _
  dsimp only [program.bb0, List.drop, List.take]
  simp (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.memcpy,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect,
    e95,e38,e19,hfs,hfd,hd,throwUBIf,Fits.storeAt_iff,
    copiedPairState,copiedRootState,copiedXState,copiedXYState]

theorem copies_segment (p : Primitives) (g : Globals) (s t : GlobalState)
    (out input : Pointer) (h0 : SmallRange t.mem (slot0 s) 48)
    (h5 : SmallRange t.mem (slot5 s) 40) (h7 : SmallRange t.mem (slot7 s) 80)
    (h8 : SmallRange t.mem (slot8 s) 40) (h9 : SmallRange t.mem (slot9 s) 40) :
    Cutpoint.segment (program p g) 0 122 15 (sqrtInputEnv g s out input) t =
      .value (copiedPairEnv g s t out input, copiedXYState s t) := by
  rw [show 15 = 3 + 12 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, copy_root_segment p g s t out input h0 h7,
    PoisonOr.value_bind]
  rw [show 12 = 3 + 9 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, copy_y_segment p g s t out input h5 h7,
    PoisonOr.value_bind]
  rw [show 9 = 6 + 3 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, copy_x_segment p g s t out input h7 h9,
    PoisonOr.value_bind]
  exact copy_y_final_segment p g s t out input h7 h8

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
