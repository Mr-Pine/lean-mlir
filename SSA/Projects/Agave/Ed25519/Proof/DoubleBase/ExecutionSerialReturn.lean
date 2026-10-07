import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialProjective
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SquareExecution

/-! Exact execution of the serial result block. Its three multiplications and
single pow2k(1) call resolve to the imported kernels, including real stores. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
set_option maxRecDepth 10000

def squareState (s : GlobalState) (out input : Pointer) : GlobalState :=
  {s with
    mem := SerialFieldMul.storeLimbs s.mem out
      (SerialPoint.squareMachine (SerialFieldMul.readLimbs s input))}

theorem squareState_buffer (h : Buffer s.mem q bytes) (out input : Pointer) :
    Buffer (squareState s out input).mem q bytes :=
  ((((h.storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _

theorem squareState_wf (s : GlobalState) (out input : Pointer) (hwf : s.WF) :
    (squareState s out input).WF := by
  simpa only [squareState, SerialFieldMul.storeLimbs, GlobalState.WF_storeAt] using hwf

def serialReturnState (s : GlobalState) (out projective : Pointer) : GlobalState :=
  let s₁ := fieldState s out projective (projective.add 80)
  let s₂ := fieldState s₁ (out.add 40) (projective.add 40) (projective.add 80)
  let s₃ := squareState s₂ (out.add 80) (projective.add 80)
  fieldState s₃ (out.add 120) projective (projective.add 40)

def serialReturnInput (E : ⟪serialKernel.Γ⟫) (projective : Pointer) : ⟪serialKernel.Γ⟫ :=
  E[%0 := .value 1#32, %20 := .value 40#64, %22 := .value 80#64,
    %23 := .value 120#64, %38 := .value projective,
    %107 := .value (projective.add 40), %108 := .value (projective.add 80)]

def serialReturnResult (E : ⟪serialKernel.Γ⟫) (out projective : Pointer) : ⟪serialKernel.Γ⟫ :=
  (serialReturnInput E projective)[%157 := .value (out.add 40),
    %158 := .value (out.add 80), %159 := .value (out.add 120)]

theorem serial_return_block (p : SerialCFG.Primitives)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (hsquare : p.call8 = Encoding.Decompress.Execution.Pow2k.program.call)
    (E : ⟪serialKernel.Γ⟫) (out projective : Pointer) (s : GlobalState)
    (hwf : s.WF) (hout : Buffer s.mem out 160) (hp : Buffer s.mem projective 120)
    (harg : E.read (%arg0) = .value out) :
    (serialKernel.bb34 p).run serialKernel.blockParams (serialReturnInput E projective) s =
      .value ((serialReturnResult E out projective, .inl .nil),
        serialReturnState s out projective) := by
  change E.args 0 = .value out at harg
  let s₁ := fieldState s out projective (projective.add 80)
  let s₂ := fieldState s₁ (out.add 40) (projective.add 40) (projective.add 80)
  let s₃ := squareState s₂ (out.add 80) (projective.add 80)
  have hout₁ := fieldState_buffer hout out projective (projective.add 80)
  have hp₁ := fieldState_buffer hp out projective (projective.add 80)
  have hout₂ := fieldState_buffer hout₁ (out.add 40) (projective.add 40) (projective.add 80)
  have hp₂ := fieldState_buffer hp₁ (out.add 40) (projective.add 40) (projective.add 80)
  have hout₃ := squareState_buffer hout₂ (out.add 80) (projective.add 80)
  have hp₃ := squareState_buffer hp₂ (out.add 80) (projective.add 80)
  have hzeroOut := hout.slice 0 40 (by decide)
  have hzeroP := hp.slice 0 40 (by decide)
  have hzeroP₃ := hp₃.slice 0 40 (by decide)
  simp only [Pointer.add_zero] at hzeroOut hzeroP hzeroP₃
  have h₁ := SerialFieldMul.kernel_call out projective (projective.add 80) s hwf
    hzeroOut hzeroP (hp.slice 80 40 (by decide))
  have h₂ := SerialFieldMul.kernel_call (out.add 40) (projective.add 40) (projective.add 80)
    s₁ (fieldState_wf _ _ _ _ hwf) (hout₁.slice 40 40 (by decide))
    (hp₁.slice 40 40 (by decide)) (hp₁.slice 80 40 (by decide))
  have h₃ := SerialPoint.Execution.square_call (out.add 80) (projective.add 80)
    s₂ (fieldState_wf _ _ _ _ (fieldState_wf _ _ _ _ hwf))
    (hout₂.slice 80 40 (by decide)) (hp₂.slice 80 40 (by decide))
  have h₄ := SerialFieldMul.kernel_call (out.add 120) projective (projective.add 40)
    s₃ (squareState_wf _ _ _ (fieldState_wf _ _ _ _ (fieldState_wf _ _ _ _ hwf)))
    (hout₃.slice 120 40 (by decide)) hzeroP₃ (hp₃.slice 40 40 (by decide))
  change SerialFieldMul.kernel.call _ s = .value (.nil, s₁) at h₁
  change SerialFieldMul.kernel.call _ s₁ = .value (.nil, s₂) at h₂
  change Encoding.Decompress.Execution.Pow2k.program.call _ s₂ = .value (.nil, s₃) at h₃
  change SerialFieldMul.kernel.call _ s₃ = .value (.nil, serialReturnState s out projective) at h₄
  simp [SerialFieldMul.kernel.args, Encoding.Decompress.Execution.Pow2k.program.args] at h₁ h₂ h₃ h₄
  have hscale40 : Operation.gepInboundsIndex 1 (.value 40#64) = .value (40 : Int) := by decide +kernel
  have hscale80 : Operation.gepInboundsIndex 1 (.value 80#64) = .value (80 : Int) := by decide +kernel
  have hscale120 : Operation.gepInboundsIndex 1 (.value 120#64) = .value (120 : Int) := by decide +kernel
  have hgep40 := hout₁.gep 40 (by decide)
  have hgep80 := hout₂.gep 80 (by decide)
  have hgep120 := hout₃.gep 120 (by decide)
  simp only [Int.cast_ofNat_Int] at hgep40 hgep80 hgep120
  change Operation.gepInboundsLive s₁.mem (.value out) [.value (40 : Int)] =
    .value (out.add 40#64) at hgep40
  change Operation.gepInboundsLive s₂.mem (.value out) [.value (80 : Int)] =
    .value (out.add 80#64) at hgep80
  change Operation.gepInboundsLive s₃.mem (.value out) [.value (120 : Int)] =
    .value (out.add 120#64) at hgep120
  simp [BasicBlock.run, serialKernel.bb34, serialReturnInput, serialReturnResult,
    List.foldlM_cons, List.foldlM_nil, Instr.run, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    hfield, hsquare, harg, h₁, h₂, h₃, h₄,
    hscale40, hscale80, hscale120, hgep40, hgep80, hgep120,
    Exit.run, Regs.read_nil, Env.writeMany_nil]

theorem serial_return_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (hsquare : p.call8 = Encoding.Decompress.Execution.Pow2k.program.call)
    (E : ⟪serialKernel.Γ⟫) (out projective : Pointer) (s : GlobalState)
    (hwf : s.WF) (hout : Buffer s.mem out 160) (hp : Buffer s.mem projective 120)
    (harg : E.read (%arg0) = .value out) :
    (serialKernel p g).runFrom (serialReturnInput E projective) 34 s =
      .value (.nil, serialReturnState s out projective) := by
  rw [Func.runFrom_eq,
    show (serialKernel p g).blocks 34 = serialKernel.bb34 p from rfl,
    serial_return_block p hfield hsquare E out projective s hwf hout hp harg]
  rfl

end Agave.Ed25519.DoubleBase.RIR
