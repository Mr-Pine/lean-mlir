/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_f25519_sub
import SSA.Projects.Firedancer.Avx512.Spec.Vec

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

abbrev fd_f25519_sub_spec (r a b : Pointer) (s : GlobalState)
    (hr : IsVecPtr s.mem r) (ha : IsVecPtr s.mem a) (hb : IsVecPtr s.mem b) : Prop :=
  R43x6.Unreduced ((readVec ha).take R43x6.limbCount) →
  R43x6.Unreduced ((readVec hb).take R43x6.limbCount) →

  let invocation := runFunction (fd_f25519_sub.denote
    (Ctxt.Valuation.ofHVector [.value b, .value a, .value r]ₕ))
  let result := StateT.run invocation s

  ∃ s',
    result = .value ([.value r]ₕ, s') ∧
    ∃ o, ∃ hEq : s' ≈ { s with mem := s.mem.splice r (vecBV o) },
      have hr' : IsVecPtr s'.mem r :=
        isVecPtr_of_equiv (GlobalState.Equiv.symm hEq) (isVecPtr_splice hr)
      let readBack := readVec hr'
      vecValue readBack = vecValue (readVec ha) - vecValue (readVec hb)
      -- `u44` and the two lanes the fold zeroes: the input contract of the next
      -- `fd_r43x6_sqr_fast`/`mul_fast`. Not `NearlyReduced` -- the fold is
      -- approximate, so limb `k` is `z k % 2^43` plus a carry plus the bias,
      -- which passes `2^43` whenever the masked part is near it.
      ∧ R43x6.U44 (readBack.take R43x6.limbCount)
      ∧ readBack[6] = 0 ∧ readBack[7] = 0

end Firedancer.Avx512
