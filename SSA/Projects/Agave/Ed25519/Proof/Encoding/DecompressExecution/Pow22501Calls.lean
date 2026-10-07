import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Cutpoint
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow22501Program

/-! Individual external-call cut points in the exact imported body. Each premise
concerns one invocation only; no decoder or square-root result is assumed. -/
set_option maxRecDepth 8192

namespace Agave.Ed25519.Encoding.Decompress.Execution.Pow22501
open LeanMLIR.RIR

/-- Original bb0 instruction 28: `pow2k(%26, %arg1, %0)`. -/
theorem call_0_28 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : BitVec 32)
    (h0 : E.read (%26) = .value v0)
    (h1 : E.read (%arg1) = .value v1)
    (h2 : E.read (%0) = .value v2)
    (hcall : p.pow2k (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 28 E s =
      Cutpoint.resume (program p) 0 29 E t := by
  apply Cutpoint.step (program p) 0 28 E E s t (by change 28 < 90; decide)
  change (do
    let returnedValues ← p.pow2k (.cons (E.read (%26)) (.cons (E.read (%arg1)) (.cons (E.read (%0)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 31: `pow2k(%24, %26, %0)`. -/
theorem call_0_31 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : BitVec 32)
    (h0 : E.read (%24) = .value v0)
    (h1 : E.read (%26) = .value v1)
    (h2 : E.read (%0) = .value v2)
    (hcall : p.pow2k (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 31 E s =
      Cutpoint.resume (program p) 0 32 E t := by
  apply Cutpoint.step (program p) 0 31 E E s t (by change 31 < 90; decide)
  change (do
    let returnedValues ← p.pow2k (.cons (E.read (%24)) (.cons (E.read (%26)) (.cons (E.read (%0)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 32: `pow2k(%25, %24, %0)`. -/
theorem call_0_32 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : BitVec 32)
    (h0 : E.read (%25) = .value v0)
    (h1 : E.read (%24) = .value v1)
    (h2 : E.read (%0) = .value v2)
    (hcall : p.pow2k (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 32 E s =
      Cutpoint.resume (program p) 0 33 E t := by
  apply Cutpoint.step (program p) 0 32 E E s t (by change 32 < 90; decide)
  change (do
    let returnedValues ← p.pow2k (.cons (E.read (%25)) (.cons (E.read (%24)) (.cons (E.read (%0)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 35: `mul(%23, %arg1, %25)`. -/
theorem call_0_35 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%23) = .value v0)
    (h1 : E.read (%arg1) = .value v1)
    (h2 : E.read (%25) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 35 E s =
      Cutpoint.resume (program p) 0 36 E t := by
  apply Cutpoint.step (program p) 0 35 E E s t (by change 35 < 90; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%23)) (.cons (E.read (%arg1)) (.cons (E.read (%25)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 37: `mul(%22, %26, %23)`. -/
theorem call_0_37 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%22) = .value v0)
    (h1 : E.read (%26) = .value v1)
    (h2 : E.read (%23) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 37 E s =
      Cutpoint.resume (program p) 0 38 E t := by
  apply Cutpoint.step (program p) 0 37 E E s t (by change 37 < 90; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%22)) (.cons (E.read (%26)) (.cons (E.read (%23)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 39: `pow2k(%21, %22, %0)`. -/
theorem call_0_39 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : BitVec 32)
    (h0 : E.read (%21) = .value v0)
    (h1 : E.read (%22) = .value v1)
    (h2 : E.read (%0) = .value v2)
    (hcall : p.pow2k (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 39 E s =
      Cutpoint.resume (program p) 0 40 E t := by
  apply Cutpoint.step (program p) 0 39 E E s t (by change 39 < 90; decide)
  change (do
    let returnedValues ← p.pow2k (.cons (E.read (%21)) (.cons (E.read (%22)) (.cons (E.read (%0)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 41: `mul(%20, %23, %21)`. -/
theorem call_0_41 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%20) = .value v0)
    (h1 : E.read (%23) = .value v1)
    (h2 : E.read (%21) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 41 E s =
      Cutpoint.resume (program p) 0 42 E t := by
  apply Cutpoint.step (program p) 0 41 E E s t (by change 41 < 90; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%20)) (.cons (E.read (%23)) (.cons (E.read (%21)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 43: `pow2k(%19, %20, %1)`. -/
theorem call_0_43 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : BitVec 32)
    (h0 : E.read (%19) = .value v0)
    (h1 : E.read (%20) = .value v1)
    (h2 : E.read (%1) = .value v2)
    (hcall : p.pow2k (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 43 E s =
      Cutpoint.resume (program p) 0 44 E t := by
  apply Cutpoint.step (program p) 0 43 E E s t (by change 43 < 90; decide)
  change (do
    let returnedValues ← p.pow2k (.cons (E.read (%19)) (.cons (E.read (%20)) (.cons (E.read (%1)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 45: `mul(%18, %19, %20)`. -/
theorem call_0_45 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%18) = .value v0)
    (h1 : E.read (%19) = .value v1)
    (h2 : E.read (%20) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 45 E s =
      Cutpoint.resume (program p) 0 46 E t := by
  apply Cutpoint.step (program p) 0 45 E E s t (by change 45 < 90; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%18)) (.cons (E.read (%19)) (.cons (E.read (%20)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 47: `pow2k(%17, %18, %2)`. -/
theorem call_0_47 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : BitVec 32)
    (h0 : E.read (%17) = .value v0)
    (h1 : E.read (%18) = .value v1)
    (h2 : E.read (%2) = .value v2)
    (hcall : p.pow2k (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 47 E s =
      Cutpoint.resume (program p) 0 48 E t := by
  apply Cutpoint.step (program p) 0 47 E E s t (by change 47 < 90; decide)
  change (do
    let returnedValues ← p.pow2k (.cons (E.read (%17)) (.cons (E.read (%18)) (.cons (E.read (%2)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 49: `mul(%16, %17, %18)`. -/
theorem call_0_49 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%16) = .value v0)
    (h1 : E.read (%17) = .value v1)
    (h2 : E.read (%18) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 49 E s =
      Cutpoint.resume (program p) 0 50 E t := by
  apply Cutpoint.step (program p) 0 49 E E s t (by change 49 < 90; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%16)) (.cons (E.read (%17)) (.cons (E.read (%18)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 51: `pow2k(%15, %16, %3)`. -/
theorem call_0_51 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : BitVec 32)
    (h0 : E.read (%15) = .value v0)
    (h1 : E.read (%16) = .value v1)
    (h2 : E.read (%3) = .value v2)
    (hcall : p.pow2k (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 51 E s =
      Cutpoint.resume (program p) 0 52 E t := by
  apply Cutpoint.step (program p) 0 51 E E s t (by change 51 < 90; decide)
  change (do
    let returnedValues ← p.pow2k (.cons (E.read (%15)) (.cons (E.read (%16)) (.cons (E.read (%3)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 53: `mul(%14, %15, %16)`. -/
theorem call_0_53 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%14) = .value v0)
    (h1 : E.read (%15) = .value v1)
    (h2 : E.read (%16) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 53 E s =
      Cutpoint.resume (program p) 0 54 E t := by
  apply Cutpoint.step (program p) 0 53 E E s t (by change 53 < 90; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%14)) (.cons (E.read (%15)) (.cons (E.read (%16)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 55: `pow2k(%13, %14, %2)`. -/
theorem call_0_55 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : BitVec 32)
    (h0 : E.read (%13) = .value v0)
    (h1 : E.read (%14) = .value v1)
    (h2 : E.read (%2) = .value v2)
    (hcall : p.pow2k (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 55 E s =
      Cutpoint.resume (program p) 0 56 E t := by
  apply Cutpoint.step (program p) 0 55 E E s t (by change 55 < 90; decide)
  change (do
    let returnedValues ← p.pow2k (.cons (E.read (%13)) (.cons (E.read (%14)) (.cons (E.read (%2)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 57: `mul(%12, %13, %18)`. -/
theorem call_0_57 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%12) = .value v0)
    (h1 : E.read (%13) = .value v1)
    (h2 : E.read (%18) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 57 E s =
      Cutpoint.resume (program p) 0 58 E t := by
  apply Cutpoint.step (program p) 0 57 E E s t (by change 57 < 90; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%12)) (.cons (E.read (%13)) (.cons (E.read (%18)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 59: `pow2k(%11, %12, %4)`. -/
theorem call_0_59 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : BitVec 32)
    (h0 : E.read (%11) = .value v0)
    (h1 : E.read (%12) = .value v1)
    (h2 : E.read (%4) = .value v2)
    (hcall : p.pow2k (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 59 E s =
      Cutpoint.resume (program p) 0 60 E t := by
  apply Cutpoint.step (program p) 0 59 E E s t (by change 59 < 90; decide)
  change (do
    let returnedValues ← p.pow2k (.cons (E.read (%11)) (.cons (E.read (%12)) (.cons (E.read (%4)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 61: `mul(%10, %11, %12)`. -/
theorem call_0_61 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%10) = .value v0)
    (h1 : E.read (%11) = .value v1)
    (h2 : E.read (%12) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 61 E s =
      Cutpoint.resume (program p) 0 62 E t := by
  apply Cutpoint.step (program p) 0 61 E E s t (by change 61 < 90; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%10)) (.cons (E.read (%11)) (.cons (E.read (%12)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 63: `pow2k(%9, %10, %5)`. -/
theorem call_0_63 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : BitVec 32)
    (h0 : E.read (%9) = .value v0)
    (h1 : E.read (%10) = .value v1)
    (h2 : E.read (%5) = .value v2)
    (hcall : p.pow2k (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 63 E s =
      Cutpoint.resume (program p) 0 64 E t := by
  apply Cutpoint.step (program p) 0 63 E E s t (by change 63 < 90; decide)
  change (do
    let returnedValues ← p.pow2k (.cons (E.read (%9)) (.cons (E.read (%10)) (.cons (E.read (%5)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 65: `mul(%8, %9, %10)`. -/
theorem call_0_65 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%8) = .value v0)
    (h1 : E.read (%9) = .value v1)
    (h2 : E.read (%10) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 65 E s =
      Cutpoint.resume (program p) 0 66 E t := by
  apply Cutpoint.step (program p) 0 65 E E s t (by change 65 < 90; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%8)) (.cons (E.read (%9)) (.cons (E.read (%10)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 67: `pow2k(%7, %8, %4)`. -/
theorem call_0_67 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : BitVec 32)
    (h0 : E.read (%7) = .value v0)
    (h1 : E.read (%8) = .value v1)
    (h2 : E.read (%4) = .value v2)
    (hcall : p.pow2k (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 67 E s =
      Cutpoint.resume (program p) 0 68 E t := by
  apply Cutpoint.step (program p) 0 67 E E s t (by change 67 < 90; decide)
  change (do
    let returnedValues ← p.pow2k (.cons (E.read (%7)) (.cons (E.read (%8)) (.cons (E.read (%4)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

/-- Original bb0 instruction 68: `mul(%arg0, %7, %12)`. -/
theorem call_0_68 (p : Primitives) (E : ⟪program.Γ⟫)
    (s t : GlobalState) (v0 : Pointer) (v1 : Pointer) (v2 : Pointer)
    (h0 : E.read (%arg0) = .value v0)
    (h1 : E.read (%7) = .value v1)
    (h2 : E.read (%12) = .value v2)
    (hcall : p.mul (.cons (.value v0) (.cons (.value v1) (.cons (.value v2) .nil))) s = .value (.nil, t)) :
    Cutpoint.resume (program p) 0 68 E s =
      Cutpoint.resume (program p) 0 69 E t := by
  apply Cutpoint.step (program p) 0 68 E E s t (by change 68 < 90; decide)
  change (do
    let returnedValues ← p.mul (.cons (E.read (%arg0)) (.cons (E.read (%7)) (.cons (E.read (%12)) .nil)))
    pure (E.writeMany .nil returnedValues) : EffectM ⟪program.Γ⟫) s = _
  simp only [h0, h1, h2, hcall, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, Env.writeMany_nil, Env.writeMany_cons]

end Agave.Ed25519.Encoding.Decompress.Execution.Pow22501
