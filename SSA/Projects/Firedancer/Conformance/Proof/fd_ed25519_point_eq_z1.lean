import SSA.Projects.Firedancer.Conformance.Spec.fd_ed25519_point_eq_z1
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_eq_z1
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_eq_z1

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

theorem fd_ed25519_point_eq_z1 : fd_ed25519_point_eq_z1_equivalent := by
  unfold fd_ed25519_point_eq_z1_equivalent
  intro s p q hs hp hq hpLimbs hqLimbs hpZUnit hqZ1 refResult

  obtain ⟨s₂, hrefRes, hs₂⟩ := Ref.fd_ed25519_point_eq_z1_conforms p q s hs hp hq hpLimbs hqLimbs hpZUnit hqZ1


  intro s' p' q' hs' hp' hq' hp'U46 hq'U46 hp'zUnit hq'Z1 avxResult
  obtain ⟨s'₂, havxRes, hs'₂⟩ := Avx512.fd_ed25519_point_eq_z1_conforms p' q' s' hs' hp' hq' hp'U46 hq'U46 hp'zUnit hq'Z1

  intro hpSame hqSame

  simp [refResult, hrefRes, avxResult, havxRes, Functor.map]

  have hiff : (Ref.readPoint hp).SamePoint (Ref.readPoint hq)
      ↔ (Avx512.readQuad hp').toPoint.SamePoint (Avx512.readQuad hq').toPoint :=
    ⟨fun h => Point.samePoint_equivalence.trans
        (Point.samePoint_equivalence.trans (Point.samePoint_equivalence.symm hpSame) h) hqSame,
     fun h => Point.samePoint_equivalence.trans
        (Point.samePoint_equivalence.trans hpSame h) (Point.samePoint_equivalence.symm hqSame)⟩
  simp only [hiff]

end Firedancer
