import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Cutpoint
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Program

/-! Individual external-call cut points in the exact imported body. Each premise
concerns one invocation only; no decoder or square-root result is assumed. -/
set_option maxRecDepth 8192

namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode
open LeanMLIR.RIR

/-- Original bb0 instruction 73: `pow2k(%34, %35, %0)`. -/
theorem call_0_73 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : BitVec 32)
    (h0 : E.read (%34) = .value v0)
    (h1 : E.read (%35) = .value v1)
    (h2 : E.read (%0) = .value v2)
    (hcall : p.pow2k (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 73 E s =
      Cutpoint.resume (program p g) 0 74 E t := by
  apply Cutpoint.step (program p g) 0 73 E E s t (by change 73 < 138; decide)
  change (do
    let returnedValues ← p.pow2k (.cons (E.read (%34)) (.cons (E.read (%35)) (.cons (E.read (%0)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 105: `mul(%31, %34, %17)`. -/
theorem call_0_105 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%31) = .value v0)
    (h1 : E.read (%34) = .value v1)
    (h2 : E.read (%17) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 105 E s =
      Cutpoint.resume (program p g) 0 106 E t := by
  apply Cutpoint.step (program p g) 0 105 E E s t (by change 105 < 138; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%31)) (.cons (E.read (%34)) (.cons (E.read (%17)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 121: `sqrtRatio(%30, %33, %32)`. -/
theorem call_0_121 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%30) = .value v0)
    (h1 : E.read (%33) = .value v1)
    (h2 : E.read (%32) = .value v2)
    (hcall : p.sqrtRatio (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 121 E s =
      Cutpoint.resume (program p g) 0 122 E t := by
  apply Cutpoint.step (program p g) 0 121 E E s t (by change 121 < 138; decide)
  change (do
    let returnedValues ← p.sqrtRatio (.cons (E.read (%30)) (.cons (E.read (%33)) (.cons (E.read (%32)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb1 instruction 8: `blackBoxByte(%99)`. -/
theorem call_1_8 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : BitVec 8) (returned : BitVec 8)
    (h0 : E.read (%99) = .value v0)
    (hcall : p.blackBoxByte (.cons (.value v0) .nil) s = .value ((.cons (.value returned) .nil), t)) :
    Cutpoint.resume (program p g) 1 8 E s =
      Cutpoint.resume (program p g) 1 9 (E[%100 := .value returned]) t := by
  apply Cutpoint.step (program p g) 1 8 E (E[%100 := .value returned]) s t (by change 8 < 59; decide)
  change (do
    let returnedValues ← p.blackBoxByte (.cons (E.read (%99)) .nil)
    pure (E.writeMany (.cons (%100) .nil) returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb1 instruction 49: `mul(%136, %39, %38)`. -/
theorem call_1_49 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%136) = .value v0)
    (h1 : E.read (%39) = .value v1)
    (h2 : E.read (%38) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 1 49 E s =
      Cutpoint.resume (program p g) 1 50 E t := by
  apply Cutpoint.step (program p g) 1 49 E E s t (by change 49 < 59; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%136)) (.cons (E.read (%39)) (.cons (E.read (%38)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

end Agave.Ed25519.Encoding.Decompress.Execution.Decode
