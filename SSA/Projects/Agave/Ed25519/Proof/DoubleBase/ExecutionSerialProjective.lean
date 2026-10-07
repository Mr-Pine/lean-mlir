import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialConversionCalls

/-! The actual end of every serial ladder round: three imported field
multiplications, a full projective copy, and the zero-index exit test. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
set_option maxRecDepth 10000

def projectiveCalls (mul : Vals [.ptr, .ptr, .ptr] → EffectM (Vals []))
    (out input : Pointer) : EffectM (Vals []) := do
  let _ ← mul (.cons (.value out) (.cons (.value input) (.cons (.value (input.add 120)) .nil)))
  let _ ← mul (.cons (.value (out.add 40)) (.cons (.value (input.add 40))
    (.cons (.value (input.add 80)) .nil)))
  mul (.cons (.value (out.add 80)) (.cons (.value (input.add 80))
    (.cons (.value (input.add 120)) .nil)))

def projectiveState (s : GlobalState) (out input : Pointer) : GlobalState :=
  let s₁ := fieldState s out input (input.add 120)
  let s₂ := fieldState s₁ (out.add 40) (input.add 40) (input.add 80)
  fieldState s₂ (out.add 80) (input.add 80) (input.add 120)

theorem projectiveState_buffer (h : Buffer s.mem q bytes) (out input : Pointer) :
    Buffer (projectiveState s out input).mem q bytes :=
  fieldState_buffer (fieldState_buffer (fieldState_buffer h _ _ _) _ _ _) _ _ _

theorem projectiveState_wf (s : GlobalState) (out input : Pointer) (hwf : s.WF) :
    (projectiveState s out input).WF :=
  fieldState_wf _ _ _ _ (fieldState_wf _ _ _ _ (fieldState_wf _ _ _ _ hwf))

theorem projectiveCalls_kernel (s : GlobalState) (out input : Pointer) (hwf : s.WF)
    (hout : Buffer s.mem out 120) (hinput : Buffer s.mem input 160) :
    projectiveCalls SerialFieldMul.kernel.call out input s =
      .value (.nil, projectiveState s out input) := by
  let s₁ := fieldState s out input (input.add 120)
  let s₂ := fieldState s₁ (out.add 40) (input.add 40) (input.add 80)
  have hout₁ := fieldState_buffer hout out input (input.add 120)
  have hin₁ := fieldState_buffer hinput out input (input.add 120)
  have hout₂ := fieldState_buffer hout₁ (out.add 40) (input.add 40) (input.add 80)
  have hin₂ := fieldState_buffer hin₁ (out.add 40) (input.add 40) (input.add 80)
  have hzeroOut := hout.slice 0 40 (by decide)
  have hzeroIn := hinput.slice 0 40 (by decide)
  simp only [Pointer.add_zero] at hzeroOut hzeroIn
  have h₁ := SerialFieldMul.kernel_call out input (input.add 120) s hwf
    hzeroOut hzeroIn (hinput.slice 120 40 (by decide))
  have h₂ := SerialFieldMul.kernel_call (out.add 40) (input.add 40) (input.add 80)
    s₁ (fieldState_wf _ _ _ _ hwf) (hout₁.slice 40 40 (by decide))
    (hin₁.slice 40 40 (by decide)) (hin₁.slice 80 40 (by decide))
  have h₃ := SerialFieldMul.kernel_call (out.add 80) (input.add 80) (input.add 120)
    s₂ (fieldState_wf _ _ _ _ (fieldState_wf _ _ _ _ hwf)) (hout₂.slice 80 40 (by decide))
    (hin₂.slice 80 40 (by decide)) (hin₂.slice 120 40 (by decide))
  change SerialFieldMul.kernel.call _ s = .value (.nil, s₁) at h₁
  change SerialFieldMul.kernel.call _ s₁ = .value (.nil, s₂) at h₂
  change SerialFieldMul.kernel.call _ s₂ = .value (.nil, projectiveState s out input) at h₃
  simp only [SerialFieldMul.kernel.args] at h₁ h₂ h₃
  unfold projectiveCalls
  simp only [EffectM.bind_eq, h₁, PoisonOr.value_bind, h₂, h₃]

def projectiveRoundState (s : GlobalState) (temporary completed projective : Pointer) :
    GlobalState :=
  let converted := projectiveState s temporary completed
  {converted with mem := converted.mem.storeAt projective (converted.mem.readAt temporary 960)}

def projectiveInput (E : ⟪serialKernel.Γ⟫) (temporary completed projective : Pointer)
    (i : Fin 256) : ⟪serialKernel.Γ⟫ :=
  E[%4 := .value 0#64, %23 := .value 120#64,
    %32 := .value temporary, %37 := .value completed, %38 := .value projective,
    %109 := .value (completed.add 120), %110 := .value (completed.add 40),
    %111 := .value (completed.add 80), %124 := .value (temporary.add 40),
    %125 := .value (temporary.add 80), %131 := .value (BitVec.ofNat 64 i.val)]

def projectiveResult (E : ⟪serialKernel.Γ⟫) (temporary completed projective : Pointer)
    (i : Fin 256) : ⟪serialKernel.Γ⟫ :=
  (projectiveInput E temporary completed projective i)[%151 := .value
    (if i.val = 0 then 1#1 else 0#1)]

private theorem emptyVals_eq (v : Vals []) : v = .nil := by cases v; rfl

theorem projective_zero_compare : ∀ i : Fin 256,
    Operation.icmp .eq (.value (BitVec.ofNat 64 i.val)) (.value 0#64) =
      .value (if i.val = 0 then 1#1 else 0#1) := by
  decide +kernel

/-- No successful conversion or branch premise is required. -/
theorem serial_projective_block (p : SerialCFG.Primitives)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (E : ⟪serialKernel.Γ⟫) (temporary completed projective : Pointer)
    (i : Fin 256) (s : GlobalState) (hwf : s.WF)
    (ht : Buffer s.mem temporary 120) (hc : Buffer s.mem completed 160)
    (hp : Buffer s.mem projective 120) (hne : projective.id ≠ temporary.id) :
    (serialKernel.bb28 p).run serialKernel.blockParams
      (projectiveInput E temporary completed projective i) s =
      .value ((projectiveResult E temporary completed projective i,
        .inr (if i.val = 0 then 34 else 35)),
        projectiveRoundState s temporary completed projective) := by
  let converted := projectiveState s temporary completed
  have hcopy (env : ⟪serialKernel.Γ⟫) :=
    run_memcpy (env := env) (s := converted) (dst := projective) (src := temporary)
      (show (120#64).toNat = 120 from rfl) (Range.disjoint_of_id_ne hne)
      (projectiveState_buffer hp temporary completed).fits
      (projectiveState_buffer ht temporary completed).fits
  let s₁ := fieldState s temporary completed (completed.add 120)
  let s₂ := fieldState s₁ (temporary.add 40) (completed.add 40) (completed.add 80)
  have ht₁ := fieldState_buffer ht temporary completed (completed.add 120)
  have hc₁ := fieldState_buffer hc temporary completed (completed.add 120)
  have ht₂ := fieldState_buffer ht₁ (temporary.add 40) (completed.add 40) (completed.add 80)
  have hc₂ := fieldState_buffer hc₁ (temporary.add 40) (completed.add 40) (completed.add 80)
  have hzeroT := ht.slice 0 40 (by decide)
  have hzeroC := hc.slice 0 40 (by decide)
  simp only [Pointer.add_zero] at hzeroT hzeroC
  have h₁ := SerialFieldMul.kernel_call temporary completed (completed.add 120) s hwf
    hzeroT hzeroC (hc.slice 120 40 (by decide))
  have h₂ := SerialFieldMul.kernel_call (temporary.add 40) (completed.add 40) (completed.add 80)
    s₁ (fieldState_wf _ _ _ _ hwf) (ht₁.slice 40 40 (by decide))
    (hc₁.slice 40 40 (by decide)) (hc₁.slice 80 40 (by decide))
  have h₃ := SerialFieldMul.kernel_call (temporary.add 80) (completed.add 80) (completed.add 120)
    s₂ (fieldState_wf _ _ _ _ (fieldState_wf _ _ _ _ hwf)) (ht₂.slice 80 40 (by decide))
    (hc₂.slice 80 40 (by decide)) (hc₂.slice 120 40 (by decide))
  change SerialFieldMul.kernel.call _ s = .value (.nil, s₁) at h₁
  change SerialFieldMul.kernel.call _ s₁ = .value (.nil, s₂) at h₂
  change SerialFieldMul.kernel.call _ s₂ = .value (.nil, converted) at h₃
  simp [SerialFieldMul.kernel.args] at h₁ h₂ h₃
  have hcmp := projective_zero_compare i
  by_cases hz : i.val = 0 <;>
    simp only [hz, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, serialKernel.bb28, projectiveInput, projectiveResult,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, hfield,
      EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
      h₁, h₂, h₃, hcopy, hcmp, hz, emptyVals_eq, Exit.run, Jump.run,
      Regs.read_nil, Env.writeMany_nil, projectiveRoundState, converted]

theorem serial_projective_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (E : ⟪serialKernel.Γ⟫) (temporary completed projective : Pointer)
    (i : Fin 256) (s : GlobalState) (hwf : s.WF)
    (ht : Buffer s.mem temporary 120) (hc : Buffer s.mem completed 160)
    (hp : Buffer s.mem projective 120) (hne : projective.id ≠ temporary.id) :
    (serialKernel p g).runFrom (projectiveInput E temporary completed projective i) 28 s =
      (serialKernel p g).runFrom (projectiveResult E temporary completed projective i)
        (if i.val = 0 then 34 else 35) (projectiveRoundState s temporary completed projective) := by
  rw [Func.runFrom_eq,
    show (serialKernel p g).blocks 28 = serialKernel.bb28 p from rfl,
    serial_projective_block p hfield E temporary completed projective i s hwf ht hc hp hne]
  rfl

end Agave.Ed25519.DoubleBase.RIR
