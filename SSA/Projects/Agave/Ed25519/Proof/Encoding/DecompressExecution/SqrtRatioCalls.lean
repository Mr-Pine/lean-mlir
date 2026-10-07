import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Cutpoint
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioProgram

/-! Individual external-call cut points in the exact imported body. Each premise
concerns one invocation only; no decoder or square-root result is assumed. -/
set_option maxRecDepth 8192

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio
open LeanMLIR.RIR

/-- Original bb0 instruction 86: `pow2k(%82, %arg2, %0)`. -/
theorem call_0_86 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : BitVec 32)
    (h0 : E.read (%82) = .value v0)
    (h1 : E.read (%arg2) = .value v1)
    (h2 : E.read (%0) = .value v2)
    (hcall : p.pow2k (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 86 E s =
      Cutpoint.resume (program p g) 0 87 E t := by
  apply Cutpoint.step (program p g) 0 86 E E s t (by change 86 < 1056; decide)
  change (do
    let returnedValues ← p.pow2k (.cons (E.read (%82)) (.cons (E.read (%arg2)) (.cons (E.read (%0)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 87: `mul(%83, %82, %arg2)`. -/
theorem call_0_87 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%83) = .value v0)
    (h1 : E.read (%82) = .value v1)
    (h2 : E.read (%arg2) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 87 E s =
      Cutpoint.resume (program p g) 0 88 E t := by
  apply Cutpoint.step (program p g) 0 87 E E s t (by change 87 < 1056; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%83)) (.cons (E.read (%82)) (.cons (E.read (%arg2)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 91: `pow2k(%80, %83, %0)`. -/
theorem call_0_91 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : BitVec 32)
    (h0 : E.read (%80) = .value v0)
    (h1 : E.read (%83) = .value v1)
    (h2 : E.read (%0) = .value v2)
    (hcall : p.pow2k (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 91 E s =
      Cutpoint.resume (program p g) 0 92 E t := by
  apply Cutpoint.step (program p g) 0 91 E E s t (by change 91 < 1056; decide)
  change (do
    let returnedValues ← p.pow2k (.cons (E.read (%80)) (.cons (E.read (%83)) (.cons (E.read (%0)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 92: `mul(%81, %80, %arg2)`. -/
theorem call_0_92 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%81) = .value v0)
    (h1 : E.read (%80) = .value v1)
    (h2 : E.read (%arg2) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 92 E s =
      Cutpoint.resume (program p g) 0 93 E t := by
  apply Cutpoint.step (program p g) 0 92 E E s t (by change 92 < 1056; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%81)) (.cons (E.read (%80)) (.cons (E.read (%arg2)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 95: `mul(%78, %arg1, %83)`. -/
theorem call_0_95 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%78) = .value v0)
    (h1 : E.read (%arg1) = .value v1)
    (h2 : E.read (%83) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 95 E s =
      Cutpoint.resume (program p g) 0 96 E t := by
  apply Cutpoint.step (program p g) 0 95 E E s t (by change 95 < 1056; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%78)) (.cons (E.read (%arg1)) (.cons (E.read (%83)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 98: `mul(%76, %arg1, %81)`. -/
theorem call_0_98 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%76) = .value v0)
    (h1 : E.read (%arg1) = .value v1)
    (h2 : E.read (%81) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 98 E s =
      Cutpoint.resume (program p g) 0 99 E t := by
  apply Cutpoint.step (program p g) 0 98 E E s t (by change 98 < 1056; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%76)) (.cons (E.read (%arg1)) (.cons (E.read (%81)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 100: `pow22501(%69, %76)`. -/
theorem call_0_100 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer)
    (h0 : E.read (%69) = .value v0)
    (h1 : E.read (%76) = .value v1)
    (hcall : p.pow22501 (.cons (.value v0) (.cons (.value v1) .nil)) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 100 E s =
      Cutpoint.resume (program p g) 0 101 E t := by
  apply Cutpoint.step (program p g) 0 100 E E s t (by change 100 < 1056; decide)
  change (do
    let returnedValues ← p.pow22501 (.cons (E.read (%69)) (.cons (E.read (%76)) .nil))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 105: `pow2k(%68, %70, %2)`. -/
theorem call_0_105 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : BitVec 32)
    (h0 : E.read (%68) = .value v0)
    (h1 : E.read (%70) = .value v1)
    (h2 : E.read (%2) = .value v2)
    (hcall : p.pow2k (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 105 E s =
      Cutpoint.resume (program p g) 0 106 E t := by
  apply Cutpoint.step (program p g) 0 105 E E s t (by change 105 < 1056; decide)
  change (do
    let returnedValues ← p.pow2k (.cons (E.read (%68)) (.cons (E.read (%70)) (.cons (E.read (%2)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 106: `mul(%77, %76, %68)`. -/
theorem call_0_106 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%77) = .value v0)
    (h1 : E.read (%76) = .value v1)
    (h2 : E.read (%68) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 106 E s =
      Cutpoint.resume (program p g) 0 107 E t := by
  apply Cutpoint.step (program p g) 0 106 E E s t (by change 106 < 1056; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%77)) (.cons (E.read (%76)) (.cons (E.read (%68)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 109: `mul(%79, %78, %77)`. -/
theorem call_0_109 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%79) = .value v0)
    (h1 : E.read (%78) = .value v1)
    (h2 : E.read (%77) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 109 E s =
      Cutpoint.resume (program p g) 0 110 E t := by
  apply Cutpoint.step (program p g) 0 109 E E s t (by change 109 < 1056; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%79)) (.cons (E.read (%78)) (.cons (E.read (%77)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 115: `pow2k(%74, %79, %0)`. -/
theorem call_0_115 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : BitVec 32)
    (h0 : E.read (%74) = .value v0)
    (h1 : E.read (%79) = .value v1)
    (h2 : E.read (%0) = .value v2)
    (hcall : p.pow2k (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 115 E s =
      Cutpoint.resume (program p g) 0 116 E t := by
  apply Cutpoint.step (program p g) 0 115 E E s t (by change 115 < 1056; decide)
  change (do
    let returnedValues ← p.pow2k (.cons (E.read (%74)) (.cons (E.read (%79)) (.cons (E.read (%0)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 116: `mul(%75, %arg2, %74)`. -/
theorem call_0_116 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%75) = .value v0)
    (h1 : E.read (%arg2) = .value v1)
    (h2 : E.read (%74) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 116 E s =
      Cutpoint.resume (program p g) 0 117 E t := by
  apply Cutpoint.step (program p g) 0 116 E E s t (by change 116 < 1056; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%75)) (.cons (E.read (%arg2)) (.cons (E.read (%74)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 306: `toBytes(%66, %arg1)`. -/
theorem call_0_306 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer)
    (h0 : E.read (%66) = .value v0)
    (h1 : E.read (%arg1) = .value v1)
    (hcall : p.toBytes (.cons (.value v0) (.cons (.value v1) .nil)) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 306 E s =
      Cutpoint.resume (program p g) 0 307 E t := by
  apply Cutpoint.step (program p g) 0 306 E E s t (by change 306 < 1056; decide)
  change (do
    let returnedValues ← p.toBytes (.cons (E.read (%66)) (.cons (E.read (%arg1)) .nil))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 307: `bytesEq(%67, %66)`. -/
theorem call_0_307 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (returned : BitVec 8)
    (h0 : E.read (%67) = .value v0)
    (h1 : E.read (%66) = .value v1)
    (hcall : p.bytesEq (.cons (.value v0) (.cons (.value v1) .nil)) s = .value ((.cons (.value returned) .nil), t)) :
    Cutpoint.resume (program p g) 0 307 E s =
      Cutpoint.resume (program p g) 0 308 (E[%236 := .value returned]) t := by
  apply Cutpoint.step (program p g) 0 307 E (E[%236 := .value returned]) s t (by change 307 < 1056; decide)
  change (do
    let returnedValues ← p.bytesEq (.cons (E.read (%67)) (.cons (E.read (%66)) .nil))
    pure (E.writeMany (.cons (%236) .nil) returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 569: `bytesEq(%65, %64)`. -/
theorem call_0_569 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (returned : BitVec 8)
    (h0 : E.read (%65) = .value v0)
    (h1 : E.read (%64) = .value v1)
    (hcall : p.bytesEq (.cons (.value v0) (.cons (.value v1) .nil)) s = .value ((.cons (.value returned) .nil), t)) :
    Cutpoint.resume (program p g) 0 569 E s =
      Cutpoint.resume (program p g) 0 570 (E[%430 := .value returned]) t := by
  apply Cutpoint.step (program p g) 0 569 E (E[%430 := .value returned]) s t (by change 569 < 1056; decide)
  change (do
    let returnedValues ← p.bytesEq (.cons (E.read (%65)) (.cons (E.read (%64)) .nil))
    pure (E.writeMany (.cons (%430) .nil) returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 576: `mul(%73, %72, %52)`. -/
theorem call_0_576 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%73) = .value v0)
    (h1 : E.read (%72) = .value v1)
    (h2 : E.read (%52) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 576 E s =
      Cutpoint.resume (program p g) 0 577 E t := by
  apply Cutpoint.step (program p g) 0 576 E E s t (by change 576 < 1056; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%73)) (.cons (E.read (%72)) (.cons (E.read (%52)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 947: `bytesEq(%63, %62)`. -/
theorem call_0_947 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (returned : BitVec 8)
    (h0 : E.read (%63) = .value v0)
    (h1 : E.read (%62) = .value v1)
    (hcall : p.bytesEq (.cons (.value v0) (.cons (.value v1) .nil)) s = .value ((.cons (.value returned) .nil), t)) :
    Cutpoint.resume (program p g) 0 947 E s =
      Cutpoint.resume (program p g) 0 948 (E[%731 := .value returned]) t := by
  apply Cutpoint.step (program p g) 0 947 E (E[%731 := .value returned]) s t (by change 947 < 1056; decide)
  change (do
    let returnedValues ← p.bytesEq (.cons (E.read (%63)) (.cons (E.read (%62)) .nil))
    pure (E.writeMany (.cons (%731) .nil) returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 953: `mul(%71, %52, %79)`. -/
theorem call_0_953 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%71) = .value v0)
    (h1 : E.read (%52) = .value v1)
    (h2 : E.read (%79) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p g) 0 953 E s =
      Cutpoint.resume (program p g) 0 954 E t := by
  apply Cutpoint.step (program p g) 0 953 E E s t (by change 953 < 1056; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%71)) (.cons (E.read (%52)) (.cons (E.read (%79)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 955: `blackBoxByte(%732)`. -/
theorem call_0_955 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : BitVec 8) (returned : BitVec 8)
    (h0 : E.read (%732) = .value v0)
    (hcall : p.blackBoxByte (.cons (.value v0) .nil) s = .value ((.cons (.value returned) .nil), t)) :
    Cutpoint.resume (program p g) 0 955 E s =
      Cutpoint.resume (program p g) 0 956 (E[%733 := .value returned]) t := by
  apply Cutpoint.step (program p g) 0 955 E (E[%733 := .value returned]) s t (by change 955 < 1056; decide)
  change (do
    let returnedValues ← p.blackBoxByte (.cons (E.read (%732)) .nil)
    pure (E.writeMany (.cons (%733) .nil) returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 1028: `blackBoxByte(%805)`. -/
theorem call_0_1028 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : BitVec 8) (returned : BitVec 8)
    (h0 : E.read (%805) = .value v0)
    (hcall : p.blackBoxByte (.cons (.value v0) .nil) s = .value ((.cons (.value returned) .nil), t)) :
    Cutpoint.resume (program p g) 0 1028 E s =
      Cutpoint.resume (program p g) 0 1029 (E[%806 := .value returned]) t := by
  apply Cutpoint.step (program p g) 0 1028 E (E[%806 := .value returned]) s t (by change 1028 < 1056; decide)
  change (do
    let returnedValues ← p.blackBoxByte (.cons (E.read (%805)) .nil)
    pure (E.writeMany (.cons (%806) .nil) returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 1048: `blackBoxByte(%822)`. -/
theorem call_0_1048 (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : BitVec 8) (returned : BitVec 8)
    (h0 : E.read (%822) = .value v0)
    (hcall : p.blackBoxByte (.cons (.value v0) .nil) s = .value ((.cons (.value returned) .nil), t)) :
    Cutpoint.resume (program p g) 0 1048 E s =
      Cutpoint.resume (program p g) 0 1049 (E[%823 := .value returned]) t := by
  apply Cutpoint.step (program p g) 0 1048 E (E[%823 := .value returned]) s t (by change 1048 < 1056; decide)
  change (do
    let returnedValues ← p.blackBoxByte (.cons (E.read (%822)) .nil)
    pure (E.writeMany (.cons (%823) .nil) returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio
