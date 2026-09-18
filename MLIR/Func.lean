module

public import MLIR.Context
public import MLIR.Instruction

namespace MLIR

@[expose] public section

/-- One `mlir` basic block -/
structure BasicBlock (Γ : Ctx) (tRets : List Ty)
    (blockParams : Fin n → List (Fin Γ.vals.length)) where
  body : List (Instr Γ)
  exit : Exit Γ tRets blockParams

/-- Represents an entire function in `mlir` -/
structure Func where
  Γ : Ctx
  tRets : List Ty
  n : Nat
  blockParams : Fin n → List (Fin Γ.vals.length)
  hhasBlock : n > 0
  hentry : blockParams ⟨0, hhasBlock⟩ = [] -- Block 0 is the entry block and has no parameters
  blocks : Fin n → BasicBlock Γ tRets blockParams

end

end MLIR
