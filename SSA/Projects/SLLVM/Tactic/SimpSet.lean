/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute

-- A simpset to simplify SLLVM semantics
register_simp_attr simp_sllvm

/-- A simpset that takes a block's *valuation spine* apart: the block arguments
arrive as an `HVector` appended to the ambient valuation, and a variable is a
numeral, so a lookup only reduces once `ofHVector`/`append` have turned the
spine into `cons`es and `cons_succ`/`cons_zero` have walked it.

Deliberately not the default simp set: `Ctxt.Valuation.cons_succ` matches a
numeral against `?i + 1`, which pulls against the `Nat` literal simprocs, so it
is opt-in. -/
register_simp_attr simp_spine
