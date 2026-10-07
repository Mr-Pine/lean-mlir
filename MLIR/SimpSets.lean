module

public meta import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.LabelAttribute

/-- Unfolds the definitions and `do` blocks of the mlir operations -/
register_simp_attr mlir_operation

/-- Reduces operations on `Env` -/
register_simp_attr mlir_env

/-- Reduces the `EffectM` monad and its operations -/
register_simp_attr mlir_effect

/-- Reduces memory operations -/
register_simp_attr mlir_mem

/-- Reductions for running single instructions -/
register_simp_attr mlir_instr

/-- Removes a returning function's frame: `eraseFrom` through stores and `alloca`s, and reads
through `alloca`s; to close a proof with `simp [mlir_frame, *]` -/
register_simp_attr mlir_frame

/-- Erases a returning function's frame, for `erase_frame`: `eraseFrom` past a write, and a write
into an erased block dropped -/
register_simp_attr mlir_erase

/-- Simplifies the state a step produces, as the step tactics seal it: reads through stores and
`alloca`s -/
register_simp_attr mlir_state

public meta section

/-- Transports a fact about a state to the state after a store or call (`h : P s → P s'`), for
the step tactics' fast path -/
register_label_attr mlir_transport

/-- Reads through a write: back (`read (store m p x) p = x`), or past it (`read (write m …) p =
read m p`), side conditions allowed. The step tactics record a write's read back as a fact about the
new state, and carry read facts past writes -/
register_label_attr mlir_read

/-- A program constant (`def quadMask : Vector (BitVec 64) 8 := #v[…]`): the step tactics write it
into the env by its name, not its unfolded value -/
register_label_attr mlir_const

end
