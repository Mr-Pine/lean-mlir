module

public import MLIR.Context
public import MLIR.Instruction

namespace MLIR

@[expose] public section

/-- One `mlir` basic block -/
structure BasicBlock (Γ : Ctx) (tRets : List Ty) (blockTys : Fin n → List Ty) where
  body : List (Instr Γ)
  exit : Exit Γ tRets blockTys

/-- Represents an entire function in `mlir` -/
structure Func where
  Γ : Ctx
  tRets : List Ty
  n : Nat
  /-- The types of each block's parameters -/
  blockTys : Fin n → List Ty
  /-- Each block's parameters: the registers a jump to it writes its arguments to -/
  blockParams : (k : Fin n) → Dsts Γ (blockTys k)
  hhasBlock : n > 0
  hentry : blockTys ⟨0, hhasBlock⟩ = [] -- Block 0 is the entry block and has no parameters
  blocks : Fin n → BasicBlock Γ tRets blockTys

end

/-- `^bbk` is block `k`, a `Fin n` whose bound checks by evaluation. -/
syntax :max "^bb" noWs num : term

macro_rules
  | `(^bb$k) => `(⟨$k, Nat.le_of_ble_eq_true rfl⟩)

end MLIR
