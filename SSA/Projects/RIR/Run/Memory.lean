module

public import SSA.Projects.RIR.Semantics.Instruction

namespace LeanMLIR.RIR

public section

theorem run_store {ptr : Pointer} {t : Ty} {v} {b : BitVec t.width} (hfits : Fits s.mem ptr t.width)
    (hv : t.flatten v = .value b) :
    (Operation.store (.value ptr) v) env s =
      .value (env, { s with mem := s.mem.storeAt ptr b }) := by
  simp [Operation.store, hfits, throwUBIf, hv, mlir_effect]

theorem run_load {ptr : Pointer} {t : Ty} {v} {dst : Dst Γ t} (hfits : Fits s.mem ptr t.width)
    (hv : (t.unflatten (s.mem.readAt ptr t.width)) = v) :
    (Operation.load dst (.value ptr)) env s = .value (env[dst := v], s) := by
  simp [Operation.load, hfits, throwUBIf, hv, mlir_effect]

theorem run_alloca {Γ : Ctx} {env : ⟪Γ⟫} {dst : Dst Γ .ptr} {s : GlobalState} {bytes : Nat} :
    (modifyGetThe GlobalState fun s => (env.write dst (.value s.allocaPtr), s.alloca bytes) :
          EffectM ⟪Γ⟫)
        s =
      .value (env.write dst (.value s.allocaPtr), s.alloca bytes) :=
  rfl

@[mlir_operation]
theorem gep_value {ptr} (h : ¬ptr.offset.uaddOverflow off) :
    Operation.gep (.value off) (.value ptr) = .value (ptr.add off) := by simp [Operation.gep, h]

end

end LeanMLIR.RIR
