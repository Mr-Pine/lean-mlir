import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_cmovznz_u64
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- Constant-time select: `*o = a` when the condition byte is zero, `b`
otherwise. -/
abbrev fiat_25519_cmovznz_u64_spec (o : Pointer) (c : BitVec 8) (a b : BitVec 64)
    (s : GlobalState) : Prop :=
  let invocation :=
    runFunction
      (fiat_25519_cmovznz_u64.denote
        (Ctxt.Valuation.ofHVector [.value b, .value a, .value c, .value o]ₕ))
  let result := StateT.run invocation s
  let v := if c = 0#8 then a else b
  ∃ s' : GlobalState,
    result = .value ([]ₕ, s') ∧ ({ s with mem := s.mem.splice o v } : GlobalState) ≈ s'

end Firedancer.Ref
