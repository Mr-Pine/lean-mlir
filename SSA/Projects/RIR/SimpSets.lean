module

public meta import Lean.Meta.Tactic.Simp.RegisterCommand

/-- Unfolds the definitions and `do` blocks of the mlir operations -/
register_simp_attr mlir_operation

/-- Reduces operations on `Env` -/
register_simp_attr mlir_env
