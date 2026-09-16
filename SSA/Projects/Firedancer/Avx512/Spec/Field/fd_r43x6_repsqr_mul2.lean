/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_repsqr_mul2
import SSA.Projects.Firedancer.Avx512.Spec.Vec

/-!
# What `fd_r43x6_repsqr_mul2` is specified to compute

`*za = xa^(2^n) · ya` and `*zb = xb^(2^n) · yb`, the two chains interleaved
for instruction-level parallelism. `n` is the number of squarings, and the
loop is the region's `^bb1`.

The out-parameters are two separate `wwl_t *`, and they must be distinct
blocks: the region writes both, and a spec that let them alias could not say
what either holds afterwards.
-/

namespace Firedancer.Avx512

open LeanMLIR SLLVM
open InstCombine (LLVM)

abbrev fd_r43x6_repsqr_mul2_spec (za zb : Pointer) (xa ya xb yb : Vector (BitVec 64) 8)
    (n : BitVec 64) (s : GlobalState) (hza : IsVecPtr s.mem za) (hzb : IsVecPtr s.mem zb) : Prop :=
  let invocation :=
    runFunction
      (fd_r43x6_repsqr_mul2.denote
        (Ctxt.Valuation.ofHVector
          [.value n, yb.map PoisonOr.value, xb.map PoisonOr.value, .value zb, ya.map PoisonOr.value,
            xa.map PoisonOr.value, .value za]ₕ))
  let result := StateT.run invocation s
  ∃ s' : GlobalState,
    result = .value ([]ₕ, s') ∧
      ∃ oa ob : Vector (BitVec 64) 8,
        let outMem := (s.mem.splice za (vecBV oa)).splice zb (vecBV ob)
        s' ≈ ({ s with mem := outMem } : GlobalState) ∧
          vecValue oa = vecValue xa ^ (2 ^ n.toNat) * vecValue ya ∧
          vecValue ob = vecValue xb ^ (2 ^ n.toNat) * vecValue yb
          -- what `FD_R43X6_MUL2_INL` leaves, and what the next call takes: the
          -- `u44` limbs and the two lanes the fold zeroes, which are the input
          -- contract of the `fd_r43x6_sqr_fast`/`mul_fast` this feeds
          ∧
          R43x6.U44 (oa.take R43x6.limbCount) ∧
          R43x6.U44 (ob.take R43x6.limbCount) ∧ oa[6] = 0 ∧ oa[7] = 0 ∧ ob[6] = 0 ∧ ob[7] = 0

end Firedancer.Avx512
