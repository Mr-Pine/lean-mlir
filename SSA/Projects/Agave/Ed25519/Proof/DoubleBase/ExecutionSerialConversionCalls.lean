import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialConvert
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialSelect
import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Execution

/-!
# Serial conversion and table-selection composition

The completed-to-extended conversions execute the four real field-multiply
calls. Their input and output field ranges follow from two 160-byte objects.
The subsequent guard and scaled table address are derived from the NAF
magnitude. The sole remaining effect premise is one selected point-helper
call; neither conversion, indexing, nor a whole CFG run is assumed.
-/
namespace Agave.Ed25519.DoubleBase.RIR

open LeanMLIR.RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000

def fieldState (s : GlobalState) (out a b : Pointer) : GlobalState :=
  {s with
    mem := SerialFieldMul.storeLimbs s.mem out
      (SerialFieldMul.machine (SerialFieldMul.readLimbs s a) (SerialFieldMul.readLimbs s b))}

theorem fieldState_wf (s : GlobalState) (out a b : Pointer) (hwf : s.WF) :
    (fieldState s out a b).WF := by
  simpa only [fieldState, SerialFieldMul.storeLimbs, GlobalState.WF_storeAt] using hwf

theorem fieldState_buffer (h : Buffer s.mem q bytes) (out a b : Pointer) :
    Buffer (fieldState s out a b).mem q bytes := by
  exact ((((h.storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _

def completedState (s : GlobalState) (out input : Pointer) : GlobalState :=
  let s₁ := fieldState s out input (input.add 120)
  let s₂ := fieldState s₁ (out.add 40) (input.add 40) (input.add 80)
  let s₃ := fieldState s₂ (out.add 80) (input.add 80) (input.add 120)
  fieldState s₃ (out.add 120) input (input.add 40)

theorem completedState_buffer (h : Buffer s.mem q bytes) (out input : Pointer) :
    Buffer (completedState s out input).mem q bytes :=
  fieldState_buffer (fieldState_buffer (fieldState_buffer (fieldState_buffer h _ _ _) _ _ _) _ _ _) _ _ _

theorem completedState_wf (s : GlobalState) (out input : Pointer) (hwf : s.WF) :
    (completedState s out input).WF :=
  fieldState_wf _ _ _ _ (fieldState_wf _ _ _ _ (fieldState_wf _ _ _ _ (fieldState_wf _ _ _ _ hwf)))

/-- No arithmetic or successful-conversion premise: each named multiply is
resolved to its independently checked imported kernel. -/
theorem completedCalls_kernel (s : GlobalState) (out input : Pointer) (hwf : s.WF)
    (hout : Buffer s.mem out 160) (hinput : Buffer s.mem input 160) :
    completedCalls SerialFieldMul.kernel.call out input s =
      .value (.nil, completedState s out input) := by
  let s₁ := fieldState s out input (input.add 120)
  let s₂ := fieldState s₁ (out.add 40) (input.add 40) (input.add 80)
  let s₃ := fieldState s₂ (out.add 80) (input.add 80) (input.add 120)
  have hout₁ := fieldState_buffer hout out input (input.add 120)
  have hin₁ := fieldState_buffer hinput out input (input.add 120)
  have hout₂ := fieldState_buffer hout₁ (out.add 40) (input.add 40) (input.add 80)
  have hin₂ := fieldState_buffer hin₁ (out.add 40) (input.add 40) (input.add 80)
  have hout₃ := fieldState_buffer hout₂ (out.add 80) (input.add 80) (input.add 120)
  have hin₃ := fieldState_buffer hin₂ (out.add 80) (input.add 80) (input.add 120)
  have hzeroOut := hout.slice 0 40 (by decide)
  have hzeroIn := hinput.slice 0 40 (by decide)
  have hzeroIn₃ := hin₃.slice 0 40 (by decide)
  simp only [Pointer.add_zero] at hzeroOut hzeroIn hzeroIn₃
  have h₁ := SerialFieldMul.kernel_call out input (input.add 120) s hwf
    hzeroOut hzeroIn (hinput.slice 120 40 (by decide))
  have h₂ := SerialFieldMul.kernel_call (out.add 40) (input.add 40) (input.add 80)
    s₁ (fieldState_wf _ _ _ _ hwf) (hout₁.slice 40 40 (by decide))
    (hin₁.slice 40 40 (by decide)) (hin₁.slice 80 40 (by decide))
  have h₃ := SerialFieldMul.kernel_call (out.add 80) (input.add 80) (input.add 120)
    s₂ (fieldState_wf _ _ _ _ (fieldState_wf _ _ _ _ hwf)) (hout₂.slice 80 40 (by decide))
    (hin₂.slice 80 40 (by decide)) (hin₂.slice 120 40 (by decide))
  have h₄ := SerialFieldMul.kernel_call (out.add 120) input (input.add 40)
    s₃ (fieldState_wf _ _ _ _ (fieldState_wf _ _ _ _ (fieldState_wf _ _ _ _ hwf)))
    (hout₃.slice 120 40 (by decide)) hzeroIn₃ (hin₃.slice 40 40 (by decide))
  change SerialFieldMul.kernel.call _ s = .value (.nil, s₁) at h₁
  change SerialFieldMul.kernel.call _ s₁ = .value (.nil, s₂) at h₂
  change SerialFieldMul.kernel.call _ s₂ = .value (.nil, s₃) at h₃
  change SerialFieldMul.kernel.call _ s₃ = .value (.nil, completedState s out input) at h₄
  simp only [SerialFieldMul.kernel.args] at h₁ h₂ h₃ h₄
  unfold completedCalls
  simp only [EffectM.bind_eq, h₁, PoisonOr.value_bind, h₂, h₃, h₄]

/-- The finite magnitude is constructed from the NAF proof, not assumed about
an arbitrary loaded byte. -/
def nafMagnitude (width n i : Nat) (hw : NAF.Supported width) : Fin (2 ^ (width - 1)) :=
  ⟨(nafDigits width n i).natAbs, by
    obtain ⟨hlo, hhi, _⟩ := NAF.digits_bounds width hw 256 0 ⟨n, 0⟩ (by norm_num) i
    have habs : ((nafDigits width n i).natAbs : Int) = nafDigits width n i ∨
        ((nafDigits width n i).natAbs : Int) = -nafDigits width n i := by
      rcases le_total 0 (nafDigits width n i) with h | h
      · exact Or.inl (Int.natAbs_of_nonneg h)
      · exact Or.inr (Int.ofNat_natAbs_of_nonpos h)
    change -(2 ^ (width - 1) : Int) < nafDigits width n i at hlo
    change nafDigits width n i < (2 ^ (width - 1) : Int) at hhi
    rcases hw with rfl | rfl <;> norm_num at * <;> omega⟩

theorem serial_cached_sub_convert_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (E : ⟪serialKernel.Γ⟫) (out input : Pointer) (magnitude : Fin 16)
    (s : GlobalState) (hwf : s.WF) (hout : Buffer s.mem out 160)
    (hinput : Buffer s.mem input 160) :
    (serialKernel p g).runFrom (cached_subConvertInput E out input magnitude) 20 s =
      (serialKernel p g).runFrom (cached_subConvertResult E out input magnitude) 22
        (completedState s out input) := by
  rw [Func.runFrom_eq,
    show (serialKernel p g).blocks 20 = serialKernel.bb20 p from rfl,
    serial_cached_sub_convert_block]
  rw [hfield]
  simp only [EffectM.bind_eq, completedCalls_kernel s out input hwf hout hinput,
    PoisonOr.value_bind, EffectM.pure_eq, Func.continue]

/-- Exact conversion, checked magnitude guard, table GEP, and selected point
call. The effect assumption names only that last arithmetic helper. -/
theorem serial_cached_sub_conversion_select (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (E : ⟪serialKernel.Γ⟫) (temporary completed table : Pointer) (magnitude : Fin 16)
    (s final : GlobalState) (hwf : s.WF) (htemporary : Buffer s.mem temporary 160)
    (hcompleted : Buffer s.mem completed 160) (htable : Buffer s.mem table 1280)
    (hcall : p.call3 (.cons (.value completed) (.cons (.value temporary)
      (.cons (.value (table.add (BitVec.ofNat 64 (160 * (magnitude.val / 2))))) .nil)))
      (completedState s temporary completed) = .value (.nil, final)) :
    let base := E[%39 := .value table]
    let converted := cached_subConvertResult base temporary completed magnitude
    let k : Fin 8 := ⟨magnitude.val / 2, by have := magnitude.isLt; omega⟩
    (serialKernel p g).runFrom (cached_subConvertInput base temporary completed magnitude) 20 s =
      (serialKernel p g).runFrom
        ((cached_subInput converted completed temporary table k)[%142 :=
          .value (table.add (BitVec.ofNat 64 (160 * k.val)))]) 26 final := by
  dsimp only
  rw [serial_cached_sub_convert_run p g hfield _ temporary completed magnitude s hwf htemporary hcompleted]
  let converted := cached_subConvertResult (E[%39 := .value table]) temporary completed magnitude
  let k : Fin 8 := ⟨magnitude.val / 2, by have := magnitude.isLt; omega⟩
  have h37 : converted.read (%37) = .value completed := by
    simp [converted, cached_subConvertResult, cached_subConvertInput, mlir_env]
  have htemp : converted.read (%35) = .value temporary := by
    simp [converted, cached_subConvertResult, cached_subConvertInput, mlir_env]
  have htableReg : converted.read (%39) = .value table := by
    simp [converted, cached_subConvertResult, cached_subConvertInput, mlir_env]
  have hindex : converted.read (%137) = .value (BitVec.ofNat 64 k.val) := by
    simp [converted, k, cached_subConvertResult, cached_subConvertInput, mlir_env]
  have henv : cached_subInput converted completed temporary table k = converted := by
    unfold cached_subInput
    rw [Env.write_of_read converted (%37) h37, Env.write_of_read converted (%35) htemp,
      Env.write_of_read converted (%39) htableReg, Env.write_of_read converted (%137) hindex]
  have hblock := serial_cached_sub_block p converted completed temporary table k
    (completedState s temporary completed) final (completedState_buffer htable _ _) hcall
  rw [henv] at hblock
  rw [Func.runFrom_eq, show (serialKernel p g).blocks 22 = serialKernel.bb22 p from rfl, hblock]
  dsimp only [converted, k] at henv
  simp only [PoisonOr.value_bind, Func.continue, converted, k, henv]

theorem serial_cached_add_convert_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (E : ⟪serialKernel.Γ⟫) (out input : Pointer) (magnitude : Fin 16)
    (s : GlobalState) (hwf : s.WF) (hout : Buffer s.mem out 160)
    (hinput : Buffer s.mem input 160) :
    (serialKernel p g).runFrom (cached_addConvertInput E out input magnitude) 21 s =
      (serialKernel p g).runFrom (cached_addConvertResult E out input magnitude) 24
        (completedState s out input) := by
  rw [Func.runFrom_eq,
    show (serialKernel p g).blocks 21 = serialKernel.bb21 p from rfl,
    serial_cached_add_convert_block]
  rw [hfield]
  simp only [EffectM.bind_eq, completedCalls_kernel s out input hwf hout hinput,
    PoisonOr.value_bind, EffectM.pure_eq, Func.continue]

/-- Exact conversion, checked magnitude guard, table GEP, and selected point
call. The effect assumption names only that last arithmetic helper. -/
theorem serial_cached_add_conversion_select (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (E : ⟪serialKernel.Γ⟫) (temporary completed table : Pointer) (magnitude : Fin 16)
    (s final : GlobalState) (hwf : s.WF) (htemporary : Buffer s.mem temporary 160)
    (hcompleted : Buffer s.mem completed 160) (htable : Buffer s.mem table 1280)
    (hcall : p.call5 (.cons (.value completed) (.cons (.value temporary)
      (.cons (.value (table.add (BitVec.ofNat 64 (160 * (magnitude.val / 2))))) .nil)))
      (completedState s temporary completed) = .value (.nil, final)) :
    let base := E[%39 := .value table]
    let converted := cached_addConvertResult base temporary completed magnitude
    let k : Fin 8 := ⟨magnitude.val / 2, by have := magnitude.isLt; omega⟩
    (serialKernel p g).runFrom (cached_addConvertInput base temporary completed magnitude) 21 s =
      (serialKernel p g).runFrom
        ((cached_addInput converted completed temporary table k)[%143 :=
          .value (table.add (BitVec.ofNat 64 (160 * k.val)))]) 26 final := by
  dsimp only
  rw [serial_cached_add_convert_run p g hfield _ temporary completed magnitude s hwf htemporary hcompleted]
  let converted := cached_addConvertResult (E[%39 := .value table]) temporary completed magnitude
  let k : Fin 8 := ⟨magnitude.val / 2, by have := magnitude.isLt; omega⟩
  have h37 : converted.read (%37) = .value completed := by
    simp [converted, cached_addConvertResult, cached_addConvertInput, mlir_env]
  have htemp : converted.read (%36) = .value temporary := by
    simp [converted, cached_addConvertResult, cached_addConvertInput, mlir_env]
  have htableReg : converted.read (%39) = .value table := by
    simp [converted, cached_addConvertResult, cached_addConvertInput, mlir_env]
  have hindex : converted.read (%140) = .value (BitVec.ofNat 64 k.val) := by
    simp [converted, k, cached_addConvertResult, cached_addConvertInput, mlir_env]
  have henv : cached_addInput converted completed temporary table k = converted := by
    unfold cached_addInput
    rw [Env.write_of_read converted (%37) h37, Env.write_of_read converted (%36) htemp,
      Env.write_of_read converted (%39) htableReg, Env.write_of_read converted (%140) hindex]
  have hblock := serial_cached_add_block p converted completed temporary table k
    (completedState s temporary completed) final (completedState_buffer htable _ _) hcall
  rw [henv] at hblock
  rw [Func.runFrom_eq, show (serialKernel p g).blocks 24 = serialKernel.bb24 p from rfl, hblock]
  dsimp only [converted, k] at henv
  simp only [PoisonOr.value_bind, Func.continue, converted, k, henv]

theorem serial_affine_sub_convert_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (E : ⟪serialKernel.Γ⟫) (out input : Pointer) (magnitude : Fin 128)
    (s : GlobalState) (hwf : s.WF) (hout : Buffer s.mem out 160)
    (hinput : Buffer s.mem input 160) :
    (serialKernel p g).runFrom (affine_subConvertInput E out input magnitude) 27 s =
      (serialKernel p g).runFrom (affine_subConvertResult E out input magnitude) 30
        (completedState s out input) := by
  rw [Func.runFrom_eq,
    show (serialKernel p g).blocks 27 = serialKernel.bb27 p from rfl,
    serial_affine_sub_convert_block]
  rw [hfield]
  simp only [EffectM.bind_eq, completedCalls_kernel s out input hwf hout hinput,
    PoisonOr.value_bind, EffectM.pure_eq, Func.continue]

/-- Exact conversion, checked magnitude guard, table GEP, and selected point
call. The effect assumption names only that last arithmetic helper. -/
theorem serial_affine_sub_conversion_select (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (E : ⟪serialKernel.Γ⟫) (temporary completed table : Pointer) (magnitude : Fin 128)
    (s final : GlobalState) (hwf : s.WF) (htemporary : Buffer s.mem temporary 160)
    (hcompleted : Buffer s.mem completed 160) (htable : Buffer s.mem table 7680)
    (hcall : p.call6 (.cons (.value completed) (.cons (.value temporary)
      (.cons (.value (table.add (BitVec.ofNat 64 (120 * (magnitude.val / 2))))) .nil)))
      (completedState s temporary completed) = .value (.nil, final)) :
    let base := E[%29 := .value table]
    let converted := affine_subConvertResult base temporary completed magnitude
    let k : Fin 64 := ⟨magnitude.val / 2, by have := magnitude.isLt; omega⟩
    (serialKernel p g).runFrom (affine_subConvertInput base temporary completed magnitude) 27 s =
      (serialKernel p g).runFrom
        ((affine_subInput converted completed temporary table k)[%155 :=
          .value (table.add (BitVec.ofNat 64 (120 * k.val)))]) 28 final := by
  dsimp only
  rw [serial_affine_sub_convert_run p g hfield _ temporary completed magnitude s hwf htemporary hcompleted]
  let converted := affine_subConvertResult (E[%29 := .value table]) temporary completed magnitude
  let k : Fin 64 := ⟨magnitude.val / 2, by have := magnitude.isLt; omega⟩
  have h37 : converted.read (%37) = .value completed := by
    simp [converted, affine_subConvertResult, affine_subConvertInput, mlir_env]
  have htemp : converted.read (%33) = .value temporary := by
    simp [converted, affine_subConvertResult, affine_subConvertInput, mlir_env]
  have htableReg : converted.read (%29) = .value table := by
    simp [converted, affine_subConvertResult, affine_subConvertInput, mlir_env]
  have hindex : converted.read (%149) = .value (BitVec.ofNat 64 k.val) := by
    simp [converted, k, affine_subConvertResult, affine_subConvertInput, mlir_env]
  have henv : affine_subInput converted completed temporary table k = converted := by
    unfold affine_subInput
    rw [Env.write_of_read converted (%37) h37, Env.write_of_read converted (%33) htemp,
      Env.write_of_read converted (%29) htableReg, Env.write_of_read converted (%149) hindex]
  have hblock := serial_affine_sub_block p converted completed temporary table k
    (completedState s temporary completed) final (completedState_buffer htable _ _) hcall
  rw [henv] at hblock
  rw [Func.runFrom_eq, show (serialKernel p g).blocks 30 = serialKernel.bb30 p from rfl, hblock]
  dsimp only [converted, k] at henv
  simp only [PoisonOr.value_bind, Func.continue, converted, k, henv]

theorem serial_affine_add_convert_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (E : ⟪serialKernel.Γ⟫) (out input : Pointer) (magnitude : Fin 128)
    (s : GlobalState) (hwf : s.WF) (hout : Buffer s.mem out 160)
    (hinput : Buffer s.mem input 160) :
    (serialKernel p g).runFrom (affine_addConvertInput E out input magnitude) 29 s =
      (serialKernel p g).runFrom (affine_addConvertResult E out input magnitude) 32
        (completedState s out input) := by
  rw [Func.runFrom_eq,
    show (serialKernel p g).blocks 29 = serialKernel.bb29 p from rfl,
    serial_affine_add_convert_block]
  rw [hfield]
  simp only [EffectM.bind_eq, completedCalls_kernel s out input hwf hout hinput,
    PoisonOr.value_bind, EffectM.pure_eq, Func.continue]

/-- Exact conversion, checked magnitude guard, table GEP, and selected point
call. The effect assumption names only that last arithmetic helper. -/
theorem serial_affine_add_conversion_select (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (E : ⟪serialKernel.Γ⟫) (temporary completed table : Pointer) (magnitude : Fin 128)
    (s final : GlobalState) (hwf : s.WF) (htemporary : Buffer s.mem temporary 160)
    (hcompleted : Buffer s.mem completed 160) (htable : Buffer s.mem table 7680)
    (hcall : p.call7 (.cons (.value completed) (.cons (.value temporary)
      (.cons (.value (table.add (BitVec.ofNat 64 (120 * (magnitude.val / 2))))) .nil)))
      (completedState s temporary completed) = .value (.nil, final)) :
    let base := E[%29 := .value table]
    let converted := affine_addConvertResult base temporary completed magnitude
    let k : Fin 64 := ⟨magnitude.val / 2, by have := magnitude.isLt; omega⟩
    (serialKernel p g).runFrom (affine_addConvertInput base temporary completed magnitude) 29 s =
      (serialKernel p g).runFrom
        ((affine_addInput converted completed temporary table k)[%156 :=
          .value (table.add (BitVec.ofNat 64 (120 * k.val)))]) 28 final := by
  dsimp only
  rw [serial_affine_add_convert_run p g hfield _ temporary completed magnitude s hwf htemporary hcompleted]
  let converted := affine_addConvertResult (E[%29 := .value table]) temporary completed magnitude
  let k : Fin 64 := ⟨magnitude.val / 2, by have := magnitude.isLt; omega⟩
  have h37 : converted.read (%37) = .value completed := by
    simp [converted, affine_addConvertResult, affine_addConvertInput, mlir_env]
  have htemp : converted.read (%34) = .value temporary := by
    simp [converted, affine_addConvertResult, affine_addConvertInput, mlir_env]
  have htableReg : converted.read (%29) = .value table := by
    simp [converted, affine_addConvertResult, affine_addConvertInput, mlir_env]
  have hindex : converted.read (%153) = .value (BitVec.ofNat 64 k.val) := by
    simp [converted, k, affine_addConvertResult, affine_addConvertInput, mlir_env]
  have henv : affine_addInput converted completed temporary table k = converted := by
    unfold affine_addInput
    rw [Env.write_of_read converted (%37) h37, Env.write_of_read converted (%34) htemp,
      Env.write_of_read converted (%29) htableReg, Env.write_of_read converted (%153) hindex]
  have hblock := serial_affine_add_block p converted completed temporary table k
    (completedState s temporary completed) final (completedState_buffer htable _ _) hcall
  rw [henv] at hblock
  rw [Func.runFrom_eq, show (serialKernel p g).blocks 32 = serialKernel.bb32 p from rfl, hblock]
  dsimp only [converted, k] at henv
  simp only [PoisonOr.value_bind, Func.continue, converted, k, henv]

end Agave.Ed25519.DoubleBase.RIR
