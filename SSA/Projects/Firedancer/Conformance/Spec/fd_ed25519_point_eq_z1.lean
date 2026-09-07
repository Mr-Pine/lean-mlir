import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_point_eq_z1
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_eq_z1
import SSA.Projects.Firedancer.Curve

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

abbrev fd_ed25519_point_eq_z1_equivalent : Prop :=
  ∀ (s : GlobalState) (p q : Pointer),
  (hs : s.WF) → (hp : Ref.IsPointPtr s.mem p) → (hq : Ref.IsPointPtr s.mem q) →
  (hpLimbs : Ref.AllLimbBounds hp) → (hqLimbs : Ref.AllLimbBounds hq) → (hpZUnit : IsUnit (Ref.readPoint hp).Z) →
  (hqZ1 : (Ref.readPoint hq).Z = 1) →
  let refResult := StateT.run (runFunction (Ref.fd_ed25519_point_eq_z1.denote (Ctxt.Valuation.ofPair (.value q) (.value p)))) s

  ∀ (s' : GlobalState) (p' q' : Pointer), (hs' : s'.WF) → (hp' : Avx512.IsQuadPtr s'.mem p') → (hq' : Avx512.IsQuadPtr s'.mem q') →
  (hp'U46 : (Avx512.readQuad hp').U46) → (hq'U46 : (Avx512.readQuad hq').U46) → (hp'zUnit : IsUnit (Avx512.readQuad hp').toPoint.Z) →
  (hq'Z1 : (Avx512.readQuad hq').toPoint.Z = 1) →
  let avxResult := StateT.run (runFunction (Avx512.fd_ed25519_point_eq_z1.denote (Ctxt.Valuation.ofPair (.value q') (.value p')))) s'

  (Ref.readPoint hp).SamePoint (Avx512.readQuad hp').toPoint →
  (Ref.readPoint hq).SamePoint (Avx512.readQuad hq').toPoint →

  (Prod.fst) <$> refResult = (Prod.fst) <$> avxResult

end Firedancer
