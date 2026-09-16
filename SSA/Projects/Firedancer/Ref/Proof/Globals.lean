/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Proof.Globals
import SSA.Projects.Firedancer.Ref.Spec.F25519

/-!
# The `ref` module's globals

`ref.mlir` declares three, all `constant`: `@fd_f25519_sqrtm1`,
`@fd_f25519_one` and `@fd_f25519_d`. A region reaches one through
`llvm.mlir.addressof`, which reads its address out of `GlobalState.globals`,
so a conformance proof carries `HoldsGlobal name init s g` and needs to turn
what those limbs *are* into the curve constants a spec is stated over.

These are that step: each says the limbs `ref.mlir` initialises a global with
decode to the constant named in `Ed25519.lean`, so the chain artifact → limbs →
field element is checked rather than asserted.
-/

namespace Firedancer.Ref

open LeanMLIR SLLVM

/-- `@fd_f25519_sqrtm1` is the field's `√-1`. -/
theorem decodeFieldElem_sqrtm1 :
    decodeFieldElem
        ![1718705420411056, 234908883556509, 2233514472574048, 2117202627021982, 765476049583133] =
      sqrtm1 := by
  decide +kernel

end Firedancer.Ref
