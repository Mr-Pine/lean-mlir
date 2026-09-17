/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
## LeanMLIR trace classes
-/

-- Trace class for LeanMLIR elaboration code
initialize
  Lean.registerTraceClass `LeanMLIR.Elab

/-- The emoji a `withTraceNode` header shows for an `Except` result. v4.34 dropped core's
`exceptEmoji` in favour of `TraceResult.toEmoji`, which does not see the `Except`. -/
def exceptEmoji : Except ε α → String
  | .ok _ => Lean.checkEmoji
  | .error _ => Lean.bombEmoji
