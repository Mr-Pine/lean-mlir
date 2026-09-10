/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_is_zero
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_f25519_is_zero
import SSA.Projects.Firedancer.Avx512.Spec.Vec
import SSA.Projects.Firedancer.Curve

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

abbrev fd_f25519_is_zero_equivalent : Prop :=
  ∀ (s : GlobalState) (q : Pointer),
  (hs : s.WF) → (hq : Ref.IsFieldElemPtr s.mem q) → (hlimb : Ref.LimbBounds hq) →

  let refResult := StateT.run (runFunction
    (Ref.fd_f25519_is_zero.denote (Ctxt.Valuation.singleton (.value q)))) s

  ∀ (s' : GlobalState) (q' : Pointer),
  (hs' : s'.WF) → (hq' : Avx512.IsVecPtr s'.mem q') →
  (hnr : R43x6.NearlyReduced (Avx512.readVec hq')) →
  (hhi6 : (Avx512.readVec hq')[6] = 0) → (hhi7 : (Avx512.readVec hq')[7] = 0) →

  let avxResult := StateT.run (runFunction
    (Avx512.fd_f25519_is_zero.denote (Ctxt.Valuation.singleton (.value q')))) s'

  Ref.readFieldElem hq = Avx512.vecValue (Avx512.readVec hq') →

  ∃ (r : BitVec 32) (sOut sOut' : GlobalState),
    refResult = .value ([(PoisonOr.value r : LLVM.IntW 32)]ₕ, sOut) ∧
    avxResult = .value ([(PoisonOr.value r : LLVM.IntW 32)]ₕ, sOut') ∧
    s ≈ sOut ∧ s' ≈ sOut'

end Firedancer
