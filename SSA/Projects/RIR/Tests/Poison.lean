module

import SSA.Projects.RIR.Poison
meta import SSA.Projects.RIR.Poison

/-! # `PoisonOr`: evaluation and instances -/

namespace LeanMLIR.RIR.Tests

private abbrev P :=
  PoisonOr Nat

#guard ((pure 3 : P) >>= fun x => pure (x + 1)) == PoisonOr.value 4

#guard ((PoisonOr.poison : P) >>= fun x => pure (x + 1)) == PoisonOr.poison

#guard ((pure 3 : P) >>= fun _ => (PoisonOr.poison : P)) == PoisonOr.poison

#guard ((· + 1) <$> (pure 3 : P)) == PoisonOr.value 4

#guard ((· + 1) <$> (PoisonOr.poison : P)) == PoisonOr.poison

#guard PoisonOr.bind₂ (pure 2 : P) (pure 3) (fun a b => pure (a * b)) == PoisonOr.value 6

#guard PoisonOr.bind₂ (PoisonOr.poison : P) (pure 3) (fun a b => pure (a * b)) == PoisonOr.poison

#guard PoisonOr.bind₂ (pure 2 : P) (PoisonOr.poison) (fun a b => pure (a * b)) == PoisonOr.poison

#guard (PoisonOr.poison : P).isPoison

#guard !(PoisonOr.value 3 : P).isPoison

#guard (PoisonOr.value 3 : P).getValue == 3

#guard (PoisonOr.poison : P).getValue == default

#guard ((PoisonOr.value 3 : P) == PoisonOr.value 3)

#guard !((PoisonOr.value 3 : P) == PoisonOr.value 4)

#guard !((PoisonOr.value 3 : P) == PoisonOr.poison)

#guard toString (PoisonOr.value 3 : P) == "(value 3)"

#guard toString (PoisonOr.poison : P) == "poison"

end LeanMLIR.RIR.Tests
