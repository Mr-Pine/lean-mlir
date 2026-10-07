import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixAllocation
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Linked
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecodeWords
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SquareExecution

/-! The exact first74 decoder instructions, including the parsed-Y stores
and the linked single-square invocation. These conclusions require no
register-readiness or helper-correctness premise. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
open SmallOrder.Execution (PrivateFrame)
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

noncomputable def initialEnv (out input : Pointer) : Env program.Γ :=
  Env.init (program.args (.value out) (.value input)).get

def parseState (s : GlobalState) (input : Pointer) : GlobalState :=
  {allocated s with mem := storeLimbs (allocated s).mem (slot5 s) (inputWords (allocated s) input)}

noncomputable def parseEnv (g : Globals) (s : GlobalState) (out input : Pointer) : Env program.Γ :=
  parsedEnv (allocatedEnv g (initialEnv out input) s) (allocated s) input (slot5 s)

def squareState (s : GlobalState) (input : Pointer) : GlobalState :=
  {parseState s input with mem := storeLimbs (parseState s input).mem (slot4 s) (SerialPoint.squareMachine (readLimbs (parseState s input) (slot5 s)))}

theorem parse_segment (p : Primitives) (g : Globals) (s : GlobalState)
    (out input : Pointer) (hwf : s.WF) (hin : SmallRange s.mem input 32) :
    Cutpoint.segment (program p g) 0 0 73 (initialEnv out input) s =
      .value (parseEnv g s out input, parseState s input) := by
  have hs := parsed_segment p g (allocatedEnv g (initialEnv out input) s)
    (allocated s) input (slot5 s) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl)
    (state10_live hwf hin) (slot5_live s hwf)
  have hsplit : ((program p g).blocks 0).body.take 73 =
      ((program p g).blocks 0).body.take 45 ++
        (((program p g).blocks 0).body.drop 45).take 28 := rfl
  unfold Cutpoint.segment
  rw [List.drop_zero, hsplit, List.foldlM_append]
  change (Cutpoint.segment (program p g) 0 0 45 (initialEnv out input) >>=
    fun E => Cutpoint.segment (program p g) 0 45 28 E) s = _
  simp only [EffectM.bind_eq, allocation_segment, PoisonOr.value_bind]
  exact hs

theorem parse_live (s : GlobalState) (input q : Pointer) (n : Nat)
    (h : SmallRange (allocated s).mem q n) : SmallRange (parseState s input).mem q n :=
  SerialPoint.Execution.smallRange_storeLimbs h _ _

theorem parse_frame (s : GlobalState) (input : Pointer) (hwf : s.WF) :
    PrivateFrame s (parseState s input) :=
  (allocation_frame s hwf).storeLimbs _ _ (by simp only [slot5_id]; omega)

theorem parse_readback (s : GlobalState) (input : Pointer) (bytes : BitVec 256)
    (hwf : s.WF) (hin : Verifier.Execution.Dalek.ReadBytes s input 32 bytes) :
    readLimbs (parseState s input) (slot5 s) = (parsedWord bytes).limbs := by
  rw [parseState, SerialPoint.Execution.readLimbs_storeLimbs _ _ _ (slot5_live s hwf)]
  exact inputWords_eq (allocated s) input bytes (state10_live hwf hin.1)
    ((state10_read s hwf input 32 256 hin.1).trans hin.2)

theorem square_segment (g : Globals) (sg : SqrtRatio.Globals) (s : GlobalState)
    (out input : Pointer) (hwf : s.WF) :
    Cutpoint.segment (program (decodePrimitives sg) g) 0 73 1 (parseEnv g s out input)
      (parseState s input) = .value (parseEnv g s out input, squareState s input) := by
  have hc := SerialPoint.Execution.square_call (slot4 s) (slot5 s) (parseState s input)
    (parse_frame s input hwf).wellFormed
    (parse_live s input _ _ (slot4_live s hwf))
    (parse_live s input _ _ (slot5_live s hwf))
  simp only [Pow2k.program.args] at hc
  change List.foldlM Instr.run (parseEnv g s out input)
    [.call (decodePrimitives sg).pow2k (.cons (%34) (.cons (%35) (.cons (%0) .nil))) .nil]
      (parseState s input) = _
  have e34 : (parseEnv g s out input).read (%34) = .value (slot4 s) := rfl
  have e35 : (parseEnv g s out input).read (%35) = .value (slot5 s) := rfl
  have e0 : (parseEnv g s out input).read (%0) = .value 1#32 := rfl
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, Regs.read_cons,
    Regs.read_nil, e34, e35, e0, decodePrimitives, Pow2k.program.args,
    EffectM.bind_eq, EffectM.pure_eq, hc, PoisonOr.value_bind,
    Env.writeMany_nil, squareState]

theorem first_square_segment (g : Globals) (sg : SqrtRatio.Globals) (s : GlobalState)
    (out input : Pointer) (hwf : s.WF) (hin : SmallRange s.mem input 32) :
    Cutpoint.segment (program (decodePrimitives sg) g) 0 0 74 (initialEnv out input) s =
      .value (parseEnv g s out input, squareState s input) := by
  have hsplit : ((program (decodePrimitives sg) g).blocks 0).body.take 74 =
      ((program (decodePrimitives sg) g).blocks 0).body.take 73 ++
        (((program (decodePrimitives sg) g).blocks 0).body.drop 73).take 1 := rfl
  unfold Cutpoint.segment
  rw [List.drop_zero, hsplit, List.foldlM_append]
  change (Cutpoint.segment (program (decodePrimitives sg) g) 0 0 73 (initialEnv out input) >>=
    fun E => Cutpoint.segment (program (decodePrimitives sg) g) 0 73 1 E) s = _
  simp only [EffectM.bind_eq, parse_segment _ _ _ _ _ hwf hin, PoisonOr.value_bind]
  exact square_segment g sg s out input hwf

theorem square_frame (s : GlobalState) (input : Pointer) (hwf : s.WF) :
    PrivateFrame s (squareState s input) :=
  (parse_frame s input hwf).storeLimbs _ _ (by simp only [slot4_id]; omega)

theorem square_readback (s : GlobalState) (input : Pointer) (bytes : BitVec 256)
    (hwf : s.WF) (hin : Verifier.Execution.Dalek.ReadBytes s input 32 bytes) :
    readLimbs (squareState s input) (slot4 s) = ((parsedWord bytes).square 1).limbs := by
  rw [squareState, SerialPoint.Execution.readLimbs_storeLimbs _ _ _
    (parse_live s input _ _ (slot4_live s hwf)), parse_readback s input bytes hwf hin]
  rfl

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
