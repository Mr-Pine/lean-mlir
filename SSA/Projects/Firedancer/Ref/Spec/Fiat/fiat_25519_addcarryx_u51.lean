import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_addcarryx_u51
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- One 51-bit add-with-carry step: `*o₁ = (c + a + b) mod 2^51` and
`*o₂ = (c + a + b) / 2^51`, stated bit-exactly over the 64-bit sum -- at
fiat's contract (`c ≤ 1`, `a b < 2^51`) it does not wrap, but that is the
caller's arithmetic, not this spec's. -/
abbrev fiat_25519_addcarryx_u51_spec (o₁ o₂ : Pointer) (c : BitVec 8) (a b : BitVec 64)
    (s : GlobalState) : Prop :=
  let invocation := runFunction (fiat_25519_addcarryx_u51.denote
    (Ctxt.Valuation.ofHVector [.value b, .value a, .value c, .value o₂, .value o₁]ₕ))
  let result := StateT.run invocation s
  let sum := BitVec.zeroExtend 64 c + a + b
  let low := sum &&& 0x7ffffffffffff#64
  let carry := (sum >>> (51 : Nat)).truncate 8

  ∃ s' : GlobalState , result = .value ([]ₕ, s')
    ∧ ({ s with mem := (s.mem.splice o₁ low).splice o₂ carry } : GlobalState) ≈ s'

end Firedancer.Ref
