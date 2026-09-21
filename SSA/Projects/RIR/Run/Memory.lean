module

public import SSA.Projects.RIR.Semantics.Instruction

namespace LeanMLIR.RIR

public section

theorem run_store {p : Reg Γ .ptr} {ptr : Pointer} {t : Ty} {v : ⟦t⟧} {b : BitVec t.width} {reg : Reg Γ t}
  (hptr : env.read p = .value ptr)
  (hfits : Fits s.mem ptr t.width)
  (hreg : env.read reg = v)
  (hv : t.flatten v = .value b) :
    (Instr.run env (.store p reg)) s = .value (env, {s with mem := s.mem.storeAt ptr b}) := by
  simp [mlir_instr, Operation.store, throwUBIf, hptr, hfits, hreg, hv, mlir_effect]

theorem run_load {p : Reg Γ .ptr} {ptr : Pointer} {t : Ty}
  {v : match t with
  | Ty.bv w => BitVec w
  | Ty.ptr => Pointer}
  {b : BitVec t.width} {dst : Dst Γ t}
  {env env' : ⟪Γ⟫}
  (hptr : env.read p = .value ptr)
  (hfits : Fits s.mem ptr t.width)
  (hb : b = s.mem.readAt ptr t.width)
  (hv : t.unflatten b = .value v)
  (henv : env' = env.write dst (.value v)) :
    (Instr.run env (.load dst p)) s = .value (env', s) := by
  simp [mlir_instr, mlir_effect, Operation.load, throwUBIf, hptr, hfits, ← hb, hv, henv]

end

end LeanMLIR.RIR
