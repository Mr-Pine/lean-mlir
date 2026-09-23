module

public meta import Lean.Meta.Tactic.Simp.RegisterCommand

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
