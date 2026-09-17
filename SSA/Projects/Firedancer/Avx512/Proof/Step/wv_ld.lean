/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Proof.Util.wv_ld

/-!
# One `wv_ld` call, peeled

`wv_ld_conforms` in the continuation form `peel_call` wants, so that the quad
the load returns reaches the walk as an opaque local rather than as a `readWv`
term the residual program then carries.

The kernel is pure and reads a single slot, so there is no `Wrote2` here: what
it leaves behind is the state equivalence the spec already states.
-/

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `wv_ld( p )` in continuation form: the quad arrives as an opaque `v`, with
`v = readWv hp` for whenever the walk needs to say what it holds. -/
theorem wv_ld_step {p : Pointer} {u : GlobalState} (hu : u.WF) (hp : IsWvPtr u.mem p)
    {P : Prop}
    (k : ∀ (u' : GlobalState) (v : Vector (BitVec 64) 4),
        StateT.run (runFunction (wv_ld.denote (Ctxt.Valuation.singleton (.value p)))) u
          = .value ([v.map PoisonOr.value]ₕ, u') →
        v = readWv hp → u ≈ u' → P) : P := by
  obtain ⟨u', hrun, hequ⟩ := wv_ld_conforms p u hu hp
  exact k u' (readWv hp) hrun rfl hequ

end Firedancer.Avx512
