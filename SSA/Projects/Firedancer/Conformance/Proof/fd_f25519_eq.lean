/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Conformance.Spec.fd_f25519_eq
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_eq
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_f25519_eq

/-!
# `fd_f25519_eq`: ref ≡ avx512

Each side already decides equality of the values it holds -- ref under
`LimbBounds`/`BiasBounds`, avx512 under `R43x6.Reduced` on both operands, that
being what makes `fold_signed`'s unreduced difference land on a canonical
pattern. The two `if` conditions are then the same, one link hypothesis per
operand.
-/

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

theorem fd_f25519_eq : fd_f25519_eq_equivalent := by
  unfold fd_f25519_eq_equivalent
  intro s p q hs hp hq hpBounds hqBounds refResult
  obtain ⟨sOut, hrefRun, hrefEq⟩ :=
    Ref.fd_f25519_eq_conforms p q s hs hp hq hpBounds hqBounds

  intro s' p' q' hs' hp' hq' hpRed hqRed avxResult hlinkP hlinkQ
  obtain ⟨sOut', havxRun, havxEq⟩ :=
    Avx512.fd_f25519_eq_conforms p' q' s' hs' hp' hq' hpRed hqRed

  have hout : (if Ref.readFieldElem hp = Ref.readFieldElem hq then (1#32) else 0#32)
      = (if Avx512.vecValue (Avx512.readVec hp')
            = Avx512.vecValue (Avx512.readVec hq') then (1#32) else 0#32) := by
    simp only [hlinkP, hlinkQ]

  refine ⟨_, sOut, sOut', hrefRun, ?_, hrefEq, havxEq⟩
  rw [hout]
  exact havxRun

end Firedancer
