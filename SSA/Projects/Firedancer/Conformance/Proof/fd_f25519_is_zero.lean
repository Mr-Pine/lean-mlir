/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Conformance.Spec.fd_f25519_is_zero
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_is_zero
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_f25519_is_zero

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

theorem fd_f25519_is_zero : fd_f25519_is_zero_equivalent := by
  unfold fd_f25519_is_zero_equivalent
  intro s q hs hq hlimb refResult
  obtain ⟨sOut, hrefRun, hrefEq⟩ := Ref.fd_f25519_is_zero_conforms q s hs hq hlimb

  intro s' q' hs' hq' hnr hhi6 hhi7 avxResult hlink
  obtain ⟨sOut', havxRun, havxEq⟩ :=
    Avx512.fd_f25519_is_zero_conforms q' s' hs' hq' hnr hhi6 hhi7

  -- `readFieldElem?` is `some` of the total read, so the ref condition is
  -- `readFieldElem hq = 0`, which `hlink` carries to the avx512 side.
  have hsome : Ref.readFieldElem? q s.mem = some (Ref.readFieldElem hq) :=
    (Option.some_get _).symm
  have hiff : (Ref.readFieldElem? q s.mem = .some 0)
      ↔ (Avx512.vecValue (Avx512.readVec hq') = 0) := by
    rw [hsome, Option.some_inj, hlink]

  have hout : (if Ref.readFieldElem? q s.mem = .some 0 then (1#32) else 0#32)
      = (if Avx512.vecValue (Avx512.readVec hq') = 0 then (1#32) else 0#32) := by
    by_cases h : Avx512.vecValue (Avx512.readVec hq') = 0
    · rw [if_pos h, if_pos (hiff.mpr h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]

  refine ⟨_, sOut, sOut', hrefRun, ?_, hrefEq, havxEq⟩
  rw [hout]
  exact havxRun

end Firedancer
