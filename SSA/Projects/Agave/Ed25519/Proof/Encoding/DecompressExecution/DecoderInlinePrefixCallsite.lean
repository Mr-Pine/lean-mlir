import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixMemory

/-! Actual decoder execution up to its sqrt_ratio_i invocation (bb0:121).
The linked square and multiplication execute; no helper result is a premise. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul SerialPoint
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
open SmallOrder.Execution (PrivateFrame)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000

attribute [local irreducible] machine

def productState (g : Globals) (s : GlobalState) (input : Pointer) : GlobalState :=
  let t := numeratorState s input
  {t with mem := storeLimbs t.mem (slot1 s) (machine (readLimbs t (slot4 s)) (readLimbs t g.address0))}

theorem product_frame (g : Globals) (s : GlobalState) (input : Pointer) (hwf : s.WF) :
    PrivateFrame s (productState g s input) :=
  (numerator_frame s input hwf).storeLimbs _ _ (by simp only [slot1_id]; omega)

theorem product_live (g : Globals) (s : GlobalState) (input q : Pointer) (n : Nat)
    (h : SmallRange (allocated s).mem q n) : SmallRange (productState g s input).mem q n :=
  smallRange_storeLimbs (numerator_live s input q n h) _ _

theorem product_segment (g : Globals) (sg : SqrtRatio.Globals) (s : GlobalState)
    (out input : Pointer) (hwf : s.WF) (ready : Ready g sg s) :
    Cutpoint.segment (program (decodePrimitives sg) g) 0 105 1
      (afterNumeratorEnv g s out input) (numeratorState s input) =
      .value (afterNumeratorEnv g s out input, productState g s input) := by
  have frame := numerator_frame s input hwf
  have hc := kernel_call (slot1 s) (slot4 s) g.address0 (numeratorState s input)
    frame.wellFormed (numerator_live s input _ _ (slot1_live s hwf))
    (numerator_live s input _ _ (slot4_live s hwf))
    (private_live frame hwf ready.curveD.1)
  simp only [kernel.args] at hc
  have e31 : (afterNumeratorEnv g s out input).read (%31) = .value (slot1 s) := rfl
  have e34 : (afterNumeratorEnv g s out input).read (%34) = .value (slot4 s) := rfl
  have e17 : (afterNumeratorEnv g s out input).read (%17) = .value g.address0 := rfl
  change List.foldlM Instr.run (afterNumeratorEnv g s out input)
    [.call (decodePrimitives sg).mul (.cons (%31) (.cons (%34) (.cons (%17) .nil))) .nil]
      (numeratorState s input) = _
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, Regs.read_cons,
    Regs.read_nil, e31, e34, e17, decodePrimitives, kernel.args,
    EffectM.bind_eq, EffectM.pure_eq, hc, PoisonOr.value_bind,
    Env.writeMany_nil, productState]

def sqrtInputState (g : Globals) (s : GlobalState) (input : Pointer) : GlobalState :=
  let t := productState g s input
  {t with mem := denominatorStore t.mem (slot2 s) (readLimbs t (slot1 s))}

noncomputable def sqrtInputEnv (g : Globals) (s : GlobalState) (out input : Pointer) :
    Env program.Γ := denominatorEnv (afterNumeratorEnv g s out input) (slot2 s) (slot1 s)
      (readLimbs (productState g s input) (slot1 s))

theorem sqrtInput_frame (g : Globals) (s : GlobalState) (input : Pointer) (hwf : s.WF) :
    PrivateFrame s (sqrtInputState g s input) := by
  exact (((product_frame g s input hwf).storeAt _ _
    (by simp only [slot2_id]; omega)).storeAt _ _
    (by simp only [Pointer.add_id, slot2_id]; omega)).storeAt _ _
    (by simp only [Pointer.add_id, slot2_id]; omega)

theorem sqrtInput_live (g : Globals) (s : GlobalState) (input q : Pointer) (n : Nat)
    (h : SmallRange (allocated s).mem q n) : SmallRange (sqrtInputState g s input).mem q n :=
  (((product_live g s input q n h).storeAt _ _).storeAt _ _).storeAt _ _

theorem sqrtInput_ready (g : Globals) (sg : SqrtRatio.Globals) (s : GlobalState)
    (input : Pointer) (hwf : s.WF) (ready : Ready g sg s) :
    Ready g sg (sqrtInputState g s input) :=
  private_ready (sqrtInput_frame g s input hwf) hwf ready

theorem through_denominator_segment (g : Globals) (sg : SqrtRatio.Globals)
    (s : GlobalState) (out input : Pointer) (hwf : s.WF)
    (hin : SmallRange s.mem input 32) (ready : Ready g sg s) :
    Cutpoint.segment (program (decodePrimitives sg) g) 0 0 121 (initialEnv out input) s =
      .value (sqrtInputEnv g s out input, sqrtInputState g s input) := by
  rw [show 121 = 105 + 16 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq,
    through_numerator_segment g sg s out input hwf hin, PoisonOr.value_bind]
  rw [show 16 = 1 + 15 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, product_segment g sg s out input hwf ready,
    PoisonOr.value_bind]
  exact denominator_segment (decodePrimitives sg) g (afterNumeratorEnv g s out input)
    (productState g s input) (slot2 s) (slot1 s)
    (product_live g s input _ _ (slot2_live s hwf))
    (product_live g s input _ _ (slot1_live s hwf))
    (by intro h; have := congrArg BlockId.id h; simp only [slot2_id, slot1_id] at this; omega)
    (by constructor <;> rfl)

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
