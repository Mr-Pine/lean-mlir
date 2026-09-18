/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Conformance.Spec.fd_ed25519_verify

/-!
# `RefWF` supplies the AVX-512 verify spec's globals

Address by address: `RefWF` names the two order-8 constants and the table, and keeps the table apart
from `sha`. The contents come from `Avx512Globals`, since the two builds lay them out differently.
An AVX-512 caller `obtain`s the two halves and hands them straight to
`Avx512.fd_ed25519_verify_conforms`.
-/

namespace Firedancer

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

theorem fd_ed25519_verify_globals_equivalent_proof : fd_ed25519_verify_globals_equivalent := by
  intro s s' sha Bt hRef _ hglob hAvx
  have ptr : ∀ (name : String) (g : Pointer), GlobalPtr s name g → GlobalPtr s' name g :=
    fun _ _ h => by
    unfold GlobalPtr at h ⊢; rw [hglob]; exact h
  obtain ⟨g0, hg0, -⟩ := hRef.gy0
  obtain ⟨g1, hg1, -⟩ := hRef.gy1
  obtain ⟨g, hgtbl, hapart⟩ := hRef.gtbl
  obtain ⟨h0, hv0, hr0⟩ := hAvx.y0 g0 (ptr _ _ hg0.addr)
  obtain ⟨h1, hv1, hr1⟩ := hAvx.y1 g1 (ptr _ _ hg1.addr)
  refine
    ⟨⟨g0, g1, h0, h1, ptr _ _ hg0.addr, ptr _ _ hg1.addr, hv0, hv1, hr0, hr1⟩, g,
      ptr _ _ hgtbl.addr, hapart sha (List.mem_singleton_self _), fun k hk => ?_⟩
  exact hAvx.tbl g (ptr _ _ hgtbl.addr) k hk

end Firedancer
