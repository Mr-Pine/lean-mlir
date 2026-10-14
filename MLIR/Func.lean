module

public import MLIR.Context
public import MLIR.Instruction

namespace MLIR

@[expose] public section

/-- One `mlir` basic block -/
structure BasicBlock (Γ : Ctx) (tRets : List Ty) (blockTys : Fin n → List Ty) where
  body : List (Instr Γ)
  exit : Exit Γ tRets blockTys

/-- A global's initializer region: one block without arguments that returns the global's value of
type `t`, its pointer members poison, and those members `ptrs` (each by its bit offset, the symbol
of the global it points into and the byte offset into it); the global is read-only if `constant`,
its address insignificant if `unnamedAddr`. -/
structure GlobalInitializer where
  Γ : Ctx
  hΓ : Γ.args = []
  t : Ty
  block : BasicBlock Γ [t] (fun _ : Fin 1 => [])
  constant : Bool := true
  unnamedAddr : Bool := false
  ptrs : List (Nat × String × BitVec 64) := []

/-- A global: its symbol and initializer. -/
structure Global where
  sym : String
  init : GlobalInitializer

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
  /-- The globals whose addresses it, or a callee, takes (callees' lists appended, with repeats):
  a call's state must hold them (`MemoryState.Globals`). -/
  globals : List Global := []

end

/-- `^bbk` is block `k`, a `Fin n` whose bound checks by evaluation. -/
syntax :max "^bb" noWs num : term

macro_rules
  | `(^bb$k) => `(⟨$k, Nat.le_of_ble_eq_true rfl⟩)

end MLIR
