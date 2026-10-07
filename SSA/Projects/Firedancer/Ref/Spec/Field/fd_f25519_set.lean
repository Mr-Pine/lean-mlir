module

public import SSA.Projects.SLLVM.Dialect
public import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_set
public import SSA.Projects.Firedancer.Ref.Spec.F25519

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `r = a`, limb for limb -- so the value *and* whatever limb bounds `a`
satisfied carry over, with no bounds hypothesis. Stated for `o` and `q` in
different blocks: the region interleaves its loads and stores, so with overlap
the later loads would see earlier stores. -/
abbrev fd_f25519_set_spec (o q : Pointer) (s : GlobalState) (_ : o.id ≠ q.id) : Prop :=
  let invocation :=
    runFunction (fd_f25519_set.denote (Ctxt.Valuation.ofHVector [.value q, .value o]ₕ))
  let result := StateT.run invocation s
  ∃ out : BitVec (5 * 64),
    let output_state : GlobalState := { s with mem := s.mem.splice o out }
    (∃ s' : GlobalState, result = .value ([.value o]ₕ, s') ∧ output_state ≈ s') ∧
      ∀ i : Fin 5, readLimb? o i output_state.mem = readLimb? q i s.mem

end Firedancer.Ref
