/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.fd_ed25519_verify
import SSA.Projects.Firedancer.Conformance.Spec.fd_ed25519_verify
import SSA.Projects.Firedancer.Ref.Proof.fd_ed25519_verify

/-!
# `fd_ed25519_verify`: the two builds agree

Neither specification names the code a run returns; each says which checks decide it. Those checks
are the same predicates on both sides -- `S < ℓ`, what the two encodings name, small order, and
`[S]B = R + [k]A` -- so the codes agree case by case, and the frames come from the specs unchanged.

`RefWF` supplies the AVX-512 globals; only the layout at those addresses is the build's own.
-/

namespace Firedancer

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519 Common

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
  exact
    ⟨⟨g0, g1, h0, h1, ptr _ _ hg0.addr, ptr _ _ hg1.addr, hv0, hv1, hr0, hr1⟩, g,
      ptr _ _ hgtbl.addr, hapart sha (List.mem_singleton_self _), fun k hk =>
      hAvx.tbl g (ptr _ _ hgtbl.addr) k hk⟩

set_option maxHeartbeats 1000000 in
theorem fd_ed25519_verify_equivalent_proof (msg : Pointer) (sz : BitVec 64) (sig pk sha : Pointer)
    (s : GlobalState) (hmsg : Fits s.mem msg (sz.toNat * 8)) (hr : IsByteBufPtr s.mem sig)
    (hS : IsByteBufPtr s.mem (sig.withOffset 32)) (ha : IsByteBufPtr s.mem pk)
    (hsignull : sig.id ≠ SLLVM.nullBlock) (hsigoff : sig.offset.toNat + 64 ≤ 2 ^ 64)
    (hmsgoff : msg.offset.toNat + sz.toNat ≤ 2 ^ 64) (hsha : IsSha512Ptr s.mem sha)
    (hshaoff : sha.offset.toNat + 256 ≤ 2 ^ 64) (hshasig : sha.id ≠ sig.id)
    (hshapk : sha.id ≠ pk.id) (hshamsg : sha.id ≠ msg.id) (hRef : s.RefWF [sha]) :
    fd_ed25519_verify_equivalent msg sz sig pk sha s hmsg hr hS ha hsignull hsigoff hmsgoff hsha
      hshaoff hshasig hshapk hshamsg hRef := by
  intro f kbits fInit fApp fFini Bt dig w hTbl hAvx hB hK hf hInit hApp hFini hdig hw
  obtain ⟨⟨g0, g1, hg0, hg1, hgp0, hgp1, hgv0, hgv1, hgr0, hgr1⟩, hTbl'⟩ :=
    fd_ed25519_verify_globals_equivalent_proof s s sha Bt hRef hTbl rfl hAvx
  obtain ⟨sRef, retRef, hrunRef, haRef, hglRef, hlRef, -, -, hsigRef, hpkRef, hrRef, hlowRef⟩ :=
    Ref.fd_ed25519_verify_conforms msg sz sig pk sha s hmsg hr hS ha hsignull f kbits fInit fApp
      fFini hsigoff hmsgoff hsha hshaoff hK hshasig hshapk hshamsg hRef hf hInit hApp hFini Bt hTbl
      hB dig hdig w hw
  obtain ⟨sAvx, retAvx, hrunAvx, haAvx, hglAvx, hlAvx, -, -, hsigAvx, hpkAvx, hrAvx, hlowAvx⟩ :=
    Avx512.fd_ed25519_verify_conforms msg sz sig pk sha s hmsg hr hS ha hsignull f kbits fInit fApp
      fFini hsigoff hmsgoff hsha hshaoff hK hshasig hshapk hshamsg hRef.wf hf hInit hApp hFini g0 g1
      hg0 hg1 hgp0 hgp1 hgv0 hgv1 hgr0 hgr1 Bt hTbl' hB dig hdig w hw
  -- the checks that decide the code, in the order the regions make them
  have hret : retRef = retAvx := by
    by_cases hℓ : groupOrder ≤ (readBuf hS).toNat
    · rw [hsigRef hℓ, hsigAvx hℓ]
    push_neg at hℓ
    by_cases hA : ∃ A, Encodes (readBuf ha) A
    case neg => rw [hpkRef hℓ hA, hpkAvx hℓ hA]
    by_cases hRenc : ∃ R, Encodes (readBuf hr) R
    case neg => rw [hrRef hℓ hA hRenc, hrAvx hℓ hA hRenc]
    obtain ⟨A, hAe⟩ := hA
    obtain ⟨R, hRe⟩ := hRenc
    obtain ⟨hlowA, hlowR, heqRef⟩ := hlowRef hℓ A R hAe hRe
    obtain ⟨hlowA', hlowR', heqAvx⟩ := hlowAvx hℓ A R hAe hRe
    by_cases hAlow : (A.x, A.y) ∈ lowOrder
    · rw [hlowA hAlow, hlowA' hAlow]
    by_cases hRlow : (R.x, R.y) ∈ lowOrder
    · rw [hlowR hAlow hRlow, hlowR' hAlow hRlow]
    obtain ⟨hiffRef, horRef⟩ := heqRef hAlow hRlow
    obtain ⟨hiffAvx, horAvx⟩ := heqAvx hAlow hRlow
    by_cases heq :
      ((packWords w).toNat % 2 ^ 255) • -A +
          (readBuf hS).toNat • basePoint.toAffine wellFormed_basePoint =
        R
    · rw [hiffRef.mpr heq, hiffAvx.mpr heq]
    · rw [horRef.resolve_left fun h => heq (hiffRef.mp h),
        horAvx.resolve_left fun h => heq (hiffAvx.mp h)]
  subst hret
  exact ⟨sRef, sAvx, retRef, hrunRef, hrunAvx, haRef, haAvx, hglRef, hglAvx, hlRef, hlAvx⟩

end Firedancer
