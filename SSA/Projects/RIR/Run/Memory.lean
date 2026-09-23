module

public import SSA.Projects.RIR.Semantics.Instruction

namespace LeanMLIR.RIR

public section

theorem run_store {ptr : Pointer} {t : Ty} {v} {b : BitVec t.width} (hfits : Fits s.mem ptr t.width)
    (hv : t.flatten (.value v) = .value b) :
    (Operation.store (.value ptr) (.value v)) env s =
      .value (env, { s with mem := s.mem.storeAt ptr b }) := by
  simp [mlir_instr, Operation.store, -Ty.width, hfits, throwUBIf, hv, mlir_effect]

theorem run_load {ptr : Pointer} {t : Ty} {v} {dst : Dst Γ t} (hfits : Fits s.mem ptr t.width)
    (hv : t.unflatten (s.mem.readAt ptr t.width) = .value v) :
    (Operation.load dst (.value ptr)) env s = .value (env[dst := (.value v)], s) := by
  simp [mlir_instr, Operation.load, -Ty.width, hfits, throwUBIf, hv, mlir_effect]

end

end LeanMLIR.RIR
