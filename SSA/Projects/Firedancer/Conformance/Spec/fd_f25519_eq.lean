/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_eq
import SSA.Projects.Firedancer.Ref.Spec.Bias
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_f25519_eq
import SSA.Projects.Firedancer.Avx512.Spec.Vec
import SSA.Projects.Firedancer.Curve

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

abbrev fd_f25519_eq_equivalent : Prop :=
  ∀ (s : GlobalState) (p q : Pointer),
  (hs : s.WF) →
  (hp : Ref.IsFieldElemPtr s.mem p) → (hq : Ref.IsFieldElemPtr s.mem q) →
  (hpBounds : Ref.LimbBounds hp) → (hqBounds : Ref.BiasBounds hq) →

  let refResult := StateT.run (runFunction
    (Ref.fd_f25519_eq.denote (Ctxt.Valuation.ofPair (.value q) (.value p)))) s

  ∀ (s' : GlobalState) (p' q' : Pointer),
  (hs' : s'.WF) →
  (hp' : Avx512.IsVecPtr s'.mem p') → (hq' : Avx512.IsVecPtr s'.mem q') →
  (hpRed : R43x6.Reduced (Avx512.readVec hp')) →
  (hqRed : R43x6.Reduced (Avx512.readVec hq')) →

  let avxResult := StateT.run (runFunction
    (Avx512.fd_f25519_eq.denote (Ctxt.Valuation.ofPair (.value q') (.value p')))) s'

  Ref.readFieldElem hp = Avx512.vecValue (Avx512.readVec hp') →
  Ref.readFieldElem hq = Avx512.vecValue (Avx512.readVec hq') →

  ∃ (r : BitVec 32) (sOut sOut' : GlobalState),
    refResult = .value ([(PoisonOr.value r : LLVM.IntW 32)]ₕ, sOut) ∧
    avxResult = .value ([(PoisonOr.value r : LLVM.IntW 32)]ₕ, sOut') ∧
    s ≈ sOut ∧ s' ≈ sOut'

end Firedancer
