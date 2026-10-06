module

public import MLIR.Semantics.Instruction

namespace MLIR

public section

theorem run_store {ptr : Pointer} {t : Ty} {v} {b : BitVec t.width} (hfits : Fits s.mem ptr t.width)
    (hv : t.flatten v = .value b) :
    (Operation.store (.value ptr) v) env s =
      .value (env, { s with mem := s.mem.storeAt ptr b }) := by
  simp [Operation.store, hfits, throwUBIf, hv, mlir_effect]

/-- `memcpy` of `n` bytes: a store at `dst` of the bits read at `src`. -/
theorem run_memcpy {dst src : Pointer} {len : BitVec w} {n : Nat} (hn : len.toNat = n)
    (hd : (Range.of dst (8 * n)).Disjoint (Range.of src (8 * n))) (hfd : Fits s.mem dst (8 * n))
    (hfs : Fits s.mem src (8 * n)) :
    (Operation.memcpy (.value dst) (.value src) (.value len)) env s =
      .value (env, { s with mem := s.mem.storeAt dst (s.mem.readAt src (8 * n)) }) := by
  subst hn
  simp [Operation.memcpy, hd, hfd, hfs, throwUBIf, mlir_effect]

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

theorem run_addressof {Γ : Ctx} {env : ⟪Γ⟫} {s : GlobalState} {t : Ty} {v : EffectM ⟦t⟧} {x : ⟦t⟧}
    {b : BitVec t.width} {dst : Dst Γ .ptr} (hv : v s = .value (x, s))
    (hb : t.flatten x = .value b) :
    Instr.run env (.addressof v dst) s =
      .value
        (env.write dst (.value s.allocaPtr),
          let s' := s.alloca ((t.width + 7) / 8)
          { s' with mem := s'.mem.storeAt s.allocaPtr b }) := by
  simp only [Instr.run, EffectM.bind_eq, hv, PoisonOr.value_bind, hb]
  rfl

@[mlir_operation]
theorem gep_value {ptr} (h : ¬ptr.offset.uaddOverflow off) :
    Operation.gep (.value off) (.value ptr) = .value (ptr.add off) := by simp [Operation.gep, h]

end

end MLIR
