import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.CancellationBounds

namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR
open Agave.Ed25519.ScalarReduce32.Arithmetic
set_option exponentiation.threshold 512

/-- Any positive partial sum bounded by 2^127 admits both LLVM addition flags. -/
theorem add128_flags (a b : BitVec 128) (h : a.toNat + b.toNat < 2 ^ 127) :
    Operation.add { nsw := true, nuw := true } (.value a) (.value b) =
      .value (a + b) ∧ (a + b).toNat = a.toNat + b.toNat := by
  have hai : a.toInt = (a.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at h ⊢; omega)
  have hbi : b.toInt = (b.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at h ⊢; omega)
  have hu : a.uaddOverflow b = false := by
    simp only [BitVec.uaddOverflow]
    norm_num at h ⊢
    omega
  have hs : a.saddOverflow b = false := by
    simp only [BitVec.saddOverflow, hai, hbi]
    norm_num at h ⊢
    omega
  constructor
  · simp [Operation.add, hu, hs]
  · rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (h.trans (by decide))

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
