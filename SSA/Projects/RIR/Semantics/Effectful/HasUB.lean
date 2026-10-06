module

public import SSA.Projects.RIR.Poison

/-!
# HasUB typeclass

This file defines an `HasUB m` typeclass, which can be used to indicate that a
monad `m` has a UB side-effect.
-/

@[expose] public section

namespace LeanMLIR.RIR

class HasUB (m : Type u → Type v) where
  /-- Undefined Behaviour effect -/
  throwUB {α : Type u} : m α

export HasUB (throwUB)
variable {m} [HasUB m]

/-- throw UB if `p` is true -/
def throwUBIf [Pure m] (p : Prop) [Decidable p] : m Unit :=
  if p then HasUB.throwUB else pure ()

end LeanMLIR.RIR

/-! ## Helpers on core types -/

namespace LeanMLIR.RIR

section CoreHelpers

variable {m} [Pure m] [HasUB m]

/-- `x.getOrUB` raises UB if `x` is poison.
This helper belongs to RIR's poison type and UB effect, independently of SLLVM's. -/
def PoisonOr.getOrUB : PoisonOr α → m α
  | .value x => pure x
  | .poison => throwUB

/-- `x.getOrUB` raises UB if `x` is `none` -/
def Option.getOrUB : Option α → m α
  | .some x => pure x
  | .none => throwUB

section Lemmas
-- TODO: presumable we'll want lemmas about {PoisonOr,Option}.getOrUB applied to some/none/value/poison
end Lemmas

end CoreHelpers

/-! ## Instances -/

-- PoisonOr is the canonical monad with UB semantics
instance : HasUB PoisonOr where
  throwUB := .poison

-- Alternatively, Option may also be used to model UB.
instance : HasUB Option where
  throwUB := none
