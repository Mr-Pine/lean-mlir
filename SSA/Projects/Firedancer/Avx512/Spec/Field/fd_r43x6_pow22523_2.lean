/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_pow22523_2
import SSA.Projects.Firedancer.Avx512.Spec.Vec

/-!
# What `fd_r43x6_pow22523_2` is specified to compute

`z^((p-5)/8) = z^(2^252 - 3)` for two elements at once -- the exponentiation
`fd_r43x6_ge_decode2` needs for the square root of `u/v`. The ladder is
eleven `fd_r43x6_repsqr_mul2` calls, so the two chains share every squaring
loop.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

abbrev fd_r43x6_pow22523_2_spec (za zb : Pointer) (xa xb : Vector (BitVec 64) 8)
    (s : GlobalState) (hza : IsVecPtr s.mem za) (hzb : IsVecPtr s.mem zb) : Prop :=
  let invocation := runFunction (fd_r43x6_pow22523_2.denote (Ctxt.Valuation.ofHVector
    [xb.map PoisonOr.value, .value zb, xa.map PoisonOr.value, .value za]ₕ))
  let result := StateT.run invocation s

  ∃ s' : GlobalState,
    result = .value ([]ₕ, s') ∧
    ∃ oa ob : Vector (BitVec 64) 8,
    let outMem := (s.mem.splice za (vecBV oa)).splice zb (vecBV ob)
    s' ≈ ({ s with mem := outMem } : GlobalState)
    ∧ vecValue oa = vecValue xa ^ (2 ^ 252 - 3)
    ∧ vecValue ob = vecValue xb ^ (2 ^ 252 - 3)
    -- the header's `u44` out
    ∧ R43x6.U44 (oa.take R43x6.limbCount)
    ∧ R43x6.U44 (ob.take R43x6.limbCount)
    -- ... and the two ignored lanes, which the next kernel's `y` operand needs
    ∧ oa[6] = 0 ∧ oa[7] = 0
    ∧ ob[6] = 0 ∧ ob[7] = 0

end Firedancer.Avx512
