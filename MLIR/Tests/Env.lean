module

import MLIR.Semantics.Env
meta import MLIR.Semantics.Env

/-! # `Env`: reads, writes, and the definitional behaviour proofs rely on -/

namespace MLIR.Tests

/-- One argument (`%arg0 : i8`) and three values (`%0 %1 %2`). -/
private abbrev G : Ctx :=
  ⟨[.bv 8], [.bv 8, .bv 8, .bv 8]⟩

private def args (x : BitVec 8) : (i : Fin G.args.length) → ⟦G.args[i]⟧
  | ⟨0, _⟩ => .value x

private def E0 (x : BitVec 8) : ⟪G⟫ :=
  Env.init (args x)

/-! ## Definitional sanity: the casts and index proofs must reduce -/

example : G.vals[(⟨1, by decide⟩ : Fin G.vals.length)] = .bv 8 :=
  rfl

example (x : BitVec 8) (v : ⟦Ty.bv 8⟧) : ((E0 x).write ⟨1, rfl⟩ v).read (.val 1 rfl) = v := by
  simp only [mlir_env]

example (x : BitVec 8) (v : ⟦Ty.bv 8⟧) :
    ((E0 x).write ⟨1, rfl⟩ v).read (.val 2 rfl) = (E0 x).read (.val 2 rfl) := by
  simp (disch := decide) only [mlir_env]

-- a write never disturbs an argument
example (x : BitVec 8) (v : ⟦Ty.bv 8⟧) :
    ((E0 x).write ⟨1, rfl⟩ v).read (.arg 0 rfl) = (E0 x).read (.arg 0 rfl) := by
  simp only [mlir_env]

/-! ## Reads through a chain of writes stay cheap

If these budgets start failing, reads have become quadratic in the chain depth; that is what the
`↓` read simproc is for (plan §5.5). -/

set_option maxHeartbeats 2000 in
example (x : BitVec 8) (v : ⟦Ty.bv 8⟧) :
    ((((E0 x).write ⟨0, rfl⟩ v).write ⟨1, rfl⟩ v).write ⟨2, rfl⟩ v).read (.val 0 rfl) = v := by
  simp (disch := decide) only [mlir_env]

/-! ## Evaluation

`G.args[i]`/`G.vals[i]` do not reduce during instance search, so a read's type has to be forced
before `==` can find its `BEq`; `bv8` does that. -/

private def bv8 (x : ⟦Ty.bv 8⟧) : PoisonOr (BitVec 8) :=
  x

#guard bv8 ((E0 7#8).read (.arg 0 rfl)) == PoisonOr.value 7#8

-- an unwritten register is poison
#guard ((E0 7#8).read (.val 0 rfl)).isPoison

-- a write is visible, and only at its own index
#guard bv8 (((E0 7#8).write ⟨1, rfl⟩ (.value 3#8)).read (.val 1 rfl)) == PoisonOr.value 3#8

#guard (((E0 7#8).write ⟨1, rfl⟩ (.value 3#8)).read (.val 0 rfl)).isPoison

-- the later write to the same register wins
#guard
  bv8 ((((E0 7#8).write ⟨1, rfl⟩ (.value 3#8)).write ⟨1, rfl⟩ (.value 4#8)).read (.val 1 rfl)) ==
    PoisonOr.value 4#8

-- writing poison is fine; it just reads back as poison
#guard (((E0 7#8).write ⟨1, rfl⟩ .poison).read (.val 1 rfl)).isPoison

end MLIR.Tests
