module

public import MLIR.Semantics.Instruction

namespace MLIR

public section

theorem run_store {ptr : Pointer} {t : Ty} {v} {b : BitVec t.width} (hfits : Fits s.mem ptr t.width)
    (hv : t.flatten (.value v) = .value b) :
    (Operation.store (.value ptr) (.value v)) env s =
      .value (env, { s with mem := s.mem.storeAt ptr b }) := by
  simp [Operation.store, hfits, throwUBIf, hv, mlir_effect]

theorem run_load {ptr : Pointer} {t : Ty} {v} {dst : Dst Γ t} (hfits : Fits s.mem ptr t.width)
    (hv : t.unflatten (s.mem.readAt ptr t.width) = .value v) :
    (Operation.load dst (.value ptr)) env s = .value (env[dst := (.value v)], s) := by
  simp [Operation.load, hfits, throwUBIf, hv, mlir_effect]

@[mlir_operation]
theorem gep_value {ptr} (h : ¬ptr.offset.uaddOverflow off) :
    Operation.gep (.value off) (.value ptr) = .value (ptr.add off) := by simp [Operation.gep, h]

end

end MLIR
