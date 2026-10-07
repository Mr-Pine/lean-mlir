import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixDecision

/-! Actual success-block sign byte load and linked subtle black_box call. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

noncomputable def successEntryEnv (g : Globals) (s t : GlobalState) (out input : Pointer) : Env program.Γ :=
  outerSuccessEnv (copiedPairEnv g s t out input) (t.mem.readAt (slot0 s) 8)

noncomputable def signByteEnv (g : Globals) (s t : GlobalState)
    (out input : Pointer) (byte : BitVec 8) : Env program.Γ :=
  (successEntryEnv g s t out input)[%97 := .value (input.add 31#64),
    %98 := .value byte, %99 := .value (byte >>> 7)]

noncomputable def signEnv (g : Globals) (s t : GlobalState)
    (out input : Pointer) (byte : BitVec 8) : Env program.Γ :=
  (signByteEnv g s t out input byte)[%100 := .value (byte >>> 7)]

def signState (q : GlobalState) : GlobalState :=
  {q with alloc := (q.alloca 1).alloc}

theorem sign_byte_segment (p : Primitives) (g : Globals) (s t q : GlobalState)
    (out input : Pointer) (hin : SmallRange q.mem input 32) :
    Cutpoint.segment (program p g) 1 0 8 (successEntryEnv g s t out input) q =
      .value (signByteEnv g s t out input (q.mem.readAt (input.add 31#64) 8), q) := by
  have ein : (successEntryEnv g s t out input).read (%arg1) = .value input := rfl
  change (successEntryEnv g s t out input).args 1 = .value input at ein
  have e21 : (successEntryEnv g s t out input).read (%21) = .value 31#64 := rfl
  have e22 : (successEntryEnv g s t out input).read (%22) = .value 7#8 := rfl
  have hg := hin.gep (k := 31) (by decide)
  norm_num only [Nat.cast_ofNat] at hg
  have hf := hin.fits_add (k := 31) (count := 1) (by decide)
  change List.foldlM Instr.run (successEntryEnv g s t out input)
    (((program.bb1 p).body.drop 0).take 8) q = _
  dsimp only [program.bb1, List.drop, List.take]
  simp (disch := first | assumption | decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,BinOp.compute,Operation.load,
    Operation.gepInboundsIndex,GepIndex.inboundsOffset,Operation.GepSignedRange,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_env,mlir_effect,mlir_operation,
    ein,e21,e22,hg,hf,throwUBIf,signByteEnv]

theorem sign_blackbox_segment (g : Globals) (sg : SqrtRatio.Globals)
    (s t q : GlobalState) (out input : Pointer) (byte : BitVec 8) (hwf : q.WF) :
    Cutpoint.segment (program (decodePrimitives sg) g) 1 8 1
      (signByteEnv g s t out input byte) q =
      .value (signEnv g s t out input byte, signState q) := by
  have hc := BlackBox.program_call (byte >>> 7) q hwf
  simp only [BlackBox.program.args] at hc
  have e99 : (signByteEnv g s t out input byte).read (%99) = .value (byte >>> 7) := rfl
  change List.foldlM Instr.run (signByteEnv g s t out input byte)
    [.call (decodePrimitives sg).blackBoxByte (.cons (%99) .nil) (.cons (%100) .nil)] q = _
  simp only [List.foldlM_cons,List.foldlM_nil,Instr.run,Regs.read_cons,Regs.read_nil,e99,
    decodePrimitives,EffectM.bind_eq,EffectM.pure_eq,hc,PoisonOr.value_bind,
    Env.writeMany_cons,Env.writeMany_nil,signEnv,signState]

theorem sign_entry_segment (g : Globals) (sg : SqrtRatio.Globals)
    (s t q : GlobalState) (out input : Pointer) (hwf : q.WF)
    (hin : SmallRange q.mem input 32) :
    Cutpoint.segment (program (decodePrimitives sg) g) 1 0 9
      (successEntryEnv g s t out input) q =
      .value (signEnv g s t out input (q.mem.readAt (input.add 31#64) 8), signState q) := by
  rw [show 9 = 8 + 1 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,
    sign_byte_segment (decodePrimitives sg) g s t q out input hin,PoisonOr.value_bind]
  exact sign_blackbox_segment g sg s t q out input _ hwf

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
