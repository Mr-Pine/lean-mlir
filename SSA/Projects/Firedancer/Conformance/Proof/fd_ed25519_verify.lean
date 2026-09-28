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

`RefWF` supplies the AVX-512 globals; only the layout at those addresses is the build's own, which
is why the two regions start from two states.
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
    (sR sA : GlobalState) (hargs : VerifyArgs sR msg sz sig pk sha) (hRef : sR.RefWF [sha])
    (hA : sA.WF) (hst : VerifyStates sR sA msg sig pk sha) :
    fd_ed25519_verify_equivalent msg sz sig pk sha sR sA hargs hRef hA hst := by
  intro f kbits fInit fApp fFini fFiniBlk Bt dig w hTbl hAvx hB hK hKA hf hInit hApp hFini hdig hw
  -- the arguments read the same at `sA`
  have hl : ∀ b ∈ [msg.id, sig.id, pk.id, sha.id], sA.mem.live? b = sR.mem.live? b :=
    fun b hb => (hst.live b hb).symm
  have hlm := hl msg.id (by simp)
  have hls := hl sig.id (by simp)
  have hlp := hl pk.id (by simp)
  have hlh := hl sha.id (by simp)
  obtain ⟨hmsgA, hmw⟩ := readWord_of_live?_eq hlm hargs.msgFits
  have hargsA : VerifyArgs sA msg sz sig pk sha :=
    { hargs with
      msgFits := hmsgA
      sigBuf := ⟨fits_of_live?_eq hls hargs.sigBuf.1, hargs.sigBuf.2⟩
      sBuf := ⟨fits_of_live?_eq hls hargs.sBuf.1, hargs.sBuf.2⟩
      pkBuf := ⟨fits_of_live?_eq hlp hargs.pkBuf.1, hargs.pkBuf.2⟩
      shaPtr := fits_of_live?_eq hlh hargs.shaPtr }
  have hr : readBuf hargsA.sigBuf = readBuf hargs.sigBuf := readBuf_of_live?_eq hls
  have hS : readBuf hargsA.sBuf = readBuf hargs.sBuf :=
    readBuf_of_live?_eq (p := sig.withOffset 32) hls
  have ha : readBuf hargsA.pkBuf = readBuf hargs.pkBuf := readBuf_of_live?_eq hlp
  have hdigA :
      ed25519Digest fInit fApp fFini (sA.mem.live? sha.id) sha.offset (readBuf hargsA.sigBuf)
          (readBuf hargsA.pkBuf) (bytesOf (readWord hargsA.msgFits)) =
        some dig := by
    rw [hlh, hr, ha, hmw]; exact hdig
  obtain ⟨⟨g0, g1, hg0, hg1, hgp0, hgp1, hgv0, hgv1, hgr0, hgr1⟩, hTbl'⟩ :=
    fd_ed25519_verify_globals_equivalent_proof sR sA sha Bt hRef hTbl hst.globals.symm hAvx
  obtain
    ⟨sRef, retRef, hrunRef, haRef, hglRef, hlRef, hretList, hearlyRef, hshaRef, hsigRef, hpkRef,
      hrRef, hlowRef⟩ :=
    Ref.fd_ed25519_verify_conforms msg sz sig pk sha sR hargs.msgFits hargs.sigBuf hargs.sBuf
      hargs.pkBuf hargs.sigNull f kbits fInit fApp fFini fFiniBlk hargs.sigOff hargs.msgOff
      hargs.shaPtr hargs.shaOff hK hargs.shaSig hargs.shaPk hargs.shaMsg hRef hf hInit hApp hFini Bt
      hTbl hB dig hdig w hw
  obtain
    ⟨sAvx, retAvx, hrunAvx, haAvx, hglAvx, hlAvx, -, hearlyAvx, hshaAvx, hsigAvx, hpkAvx, hrAvx,
      hlowAvx⟩ :=
    Avx512.fd_ed25519_verify_conforms msg sz sig pk sha sA hargsA.msgFits hargsA.sigBuf
      hargsA.sBuf hargsA.pkBuf hargs.sigNull f kbits fInit fApp fFini fFiniBlk hargs.sigOff
      hargs.msgOff hargsA.shaPtr hargs.shaOff hKA hargs.shaSig hargs.shaPk hargs.shaMsg hA hf hInit
      hApp hFini g0 g1 hg0 hg1 hgp0 hgp1 hgv0 hgv1 hgr0 hgr1 Bt hTbl' hB dig hdigA w hw
  simp only [hr, hS, ha, hmw, hlh] at hshaAvx hsigAvx hpkAvx hrAvx hlowAvx
  -- the checks that decide the code, in the order the regions make them
  have hret : retRef = retAvx := by
    by_cases hℓ : groupOrder ≤ (readBuf hargs.sBuf).toNat
    · rw [hsigRef hℓ, hsigAvx hℓ]
    push Not at hℓ
    by_cases hA : ∃ A, Encodes (readBuf hargs.pkBuf) A
    case neg => rw [hpkRef hℓ hA, hpkAvx hℓ hA]
    by_cases hRenc : ∃ R, Encodes (readBuf hargs.sigBuf) R
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
          (readBuf hargs.sBuf).toNat • basePoint.toAffine wellFormed_basePoint =
        R
    · rw [hiffRef.mpr heq, hiffAvx.mpr heq]
    · rw [horRef.resolve_left fun h => heq (hiffRef.mp h),
        horAvx.resolve_left fun h => heq (hiffAvx.mp h)]
  subst hret
  -- the two states: each start off `sha`, and what `fini` left at `sha` on both sides
  obtain ⟨shaBlk, hshaBlk⟩ :=
    Option.isSome_iff_exists.mp (ed25519ShaBlock_isSome (fFiniBlk := fFiniBlk) hdig)
  have hsha : sRef.mem.live? sha.id = sAvx.mem.live? sha.id := by
    by_cases hhashed : retRef = FD_ED25519_SUCCESS ∨ retRef = FD_ED25519_ERR_MSG
    · rw [hshaRef hhashed shaBlk hshaBlk, hshaAvx hhashed shaBlk hshaBlk]
    · have hearly : retRef = FD_ED25519_ERR_SIG ∨ retRef = FD_ED25519_ERR_PUBKEY := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hretList
        push Not at hhashed
        rcases hretList with h | h | h | h
        · exact absurd h hhashed.1
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hhashed.2
      rw [← (hearlyRef hearly).live sha.id, ← (hearlyAvx hearly).live sha.id, hlh]
  refine
    ⟨sRef, sAvx, retRef, hrunRef, hrunAvx, by rw [haRef, haAvx, hst.alloc],
      by rw [hglRef, hglAvx, hst.globals], fun b hb => ?_, haRef, hglRef, hlRef, hlAvx⟩
  by_cases hbs : b = sha.id
  · subst hbs; exact hsha
  · rw [hlRef b hbs, hlAvx b hbs, hb]

end Firedancer
