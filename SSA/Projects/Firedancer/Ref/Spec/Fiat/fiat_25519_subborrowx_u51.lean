import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_subborrowx_u51
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- One 51-bit subtract-with-borrow step: for `d = a - (b + c)` over 64 bits,
`*o₁ = d mod 2^51` and `*o₂ = -(d >>> 51)` -- the arithmetic shift's sign
spelled as a negated truncation, `0xff` on borrow at fiat's contract. -/
abbrev fiat_25519_subborrowx_u51_spec (o₁ o₂ : Pointer) (c : BitVec 8) (a b : BitVec 64)
    (s : GlobalState) : Prop :=
  let invocation := runFunction (fiat_25519_subborrowx_u51.denote
    (Ctxt.Valuation.ofHVector [.value b, .value a, .value c, .value o₂, .value o₁]ₕ))
  let result := StateT.run invocation s
  let diff := a - (BitVec.zeroExtend 64 c + b)
  let low := diff &&& 0x7ffffffffffff#64
  let borrow := 0#8 - (diff >>> (51 : Nat)).truncate 8

  ∃ s' : GlobalState , result = .value ([]ₕ, s')
    ∧ ({ s with mem := (s.mem.splice o₁ low).splice o₂ borrow } : GlobalState) ≈ s'

end Firedancer.Ref
