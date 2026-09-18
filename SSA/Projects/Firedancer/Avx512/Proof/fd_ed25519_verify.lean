/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_double_scalar_mul_base
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_eq_z1
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_frombytes_2x
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_neg_self
import SSA.Projects.Firedancer.Avx512.Spec.fd_ed25519_verify
import SSA.Projects.Firedancer.Common.Proof.Scalar.fd_curve25519_scalar_reduce
import SSA.Projects.Firedancer.Common.Proof.Scalar.fd_curve25519_scalar_validate
import SSA.Projects.Firedancer.Common.Proof.fd_ed25519_verify
import SSA.Projects.Firedancer.Conformance.Proof.fd_ed25519_point_frombytes_2x
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics

/-!
# `fd_ed25519_verify` conformance (AVX-512)

The ref proof's walk, with QUADs for points: each call's frame is a `writeQuad` (or one splice
of a QUAD) instead of four coordinate stores, and what a decoded point satisfies comes from
`Decodes` and `DecodeBounds` instead of `IsDecoding` and limb bounds.
-/

namespace Firedancer.Avx512

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519 Common

attribute [local irreducible] Common.fd_curve25519_scalar_validate fd_ed25519_point_frombytes_2x
  fd_ed25519_affine_is_small_order Common.fd_curve25519_scalar_reduce fd_ed25519_point_neg
  fd_ed25519_double_scalar_mul_base fd_ed25519_point_eq_z1

/-! ### Encodings, as `wv_t`s -/

/-- An encoded point makes the encoding decodable. -/
theorem decodable_of_encodes {m : MemoryState} {q : Pointer} (h : IsByteBufPtr m q)
    {A : Edwards.Point curve} (hA : Encodes (readBuf h) A) : Decodable (readWv h) := by
  rw [Decodable, ← decodeBytes_eq_wvY h h rfl]
  exact isSquare_of_encodes hA

/-- A decodable encoding names a point: a root of the ratio, its sign fixed by the top bit. -/
theorem exists_encodes_of_decodable {m : MemoryState} {q : Pointer} (h : IsByteBufPtr m q)
    (hd : Decodable (readWv h)) : ∃ A : Edwards.Point curve, Encodes (readBuf h) A := by
  rw [Decodable, ← decodeBytes_eq_wvY h h rfl] at hd
  set y := Ref.decodeBytes (readBuf h)
  obtain ⟨x, hx⟩ := (isSquare_div_iff (denom_ne_zero y)).mp hd
  have hp : p % 2 = 1 := by norm_num [p]
  -- `x` or `-x`, whichever has the parity the sign bit asks for
  obtain ⟨x', hx'2, hsgn⟩ :
    ∃ x' : ZMod p, x' ^ 2 = x ^ 2 ∧ (x' ≠ 0 → (x'.val % 2 = 0 ↔ (readBuf h)[255] = false)) := by
    by_cases hpar : x = 0 ∨ (x.val % 2 = 0 ↔ (readBuf h)[255] = false)
    · exact ⟨x, rfl, fun hne => hpar.resolve_left hne⟩
    · push_neg at hpar
      obtain ⟨hne, hpar⟩ := hpar
      refine ⟨-x, by ring, fun _ => ?_⟩
      have hlt := ZMod.val_lt x
      have hpos : x.val ≠ 0 := (ZMod.val_ne_zero x).mpr hne
      rw [ZMod.neg_val, if_neg hne]
      revert hpar
      cases (readBuf h)[255] <;> simp <;> omega
  refine ⟨⟨x', y, ?_⟩, rfl, hsgn⟩
  show -x' ^ 2 + y ^ 2 = 1 + d * x' ^ 2 * y ^ 2
  rw [hx'2]
  linear_combination -hx

theorem wellFormed_of_decodes {u : Vector (BitVec 64) 4} {Q : Quad} (h : Decodes u Q) :
    Q.toPoint.WellFormed := by
  have hz : Q.toPoint.Z = 1 := h.2.1
  refine ⟨hz ▸ isUnit_one, h.1, ?_⟩
  have ht := h.2.2.2.1
  simp only [Point.x, Point.y, hz, inv_one, mul_one, div_one] at ht
  rw [hz, mul_one, ht]

theorem encodes_of_decodes {m : MemoryState} {q : Pointer} (h : IsByteBufPtr m q) {Q : Quad}
    (hd : Decodes (readWv h) Q) :
    Encodes (readBuf h) (Q.toPoint.toAffine (wellFormed_of_decodes hd)) := by
  have hz : Q.toPoint.Z = 1 := hd.2.1
  refine ⟨?_, fun hne => ?_⟩
  · show Q.toPoint.Y * Q.toPoint.Z⁻¹ = _
    rw [hz, inv_one, mul_one, hd.2.2.1]
    exact (decodeBytes_eq_wvY h h rfl).symm
  · change Q.toPoint.X * Q.toPoint.Z⁻¹ ≠ 0 at hne
    show (Q.toPoint.X * Q.toPoint.Z⁻¹).val % 2 = 0 ↔ _
    rw [hz, inv_one, mul_one] at hne ⊢
    rw [hd.2.2.2.2 hne, wvSign_eq_getElem_readBuf h h rfl]

/-- Any point the encoding names has the decoding's coordinates. -/
theorem coords_of_encodes {m : MemoryState} {q : Pointer} (h : IsByteBufPtr m q) {Q : Quad}
    (hd : Decodes (readWv h) Q) {A : Edwards.Point curve} (hA : Encodes (readBuf h) A) :
    A.x = Q.toPoint.X ∧ A.y = Q.toPoint.Y := by
  obtain rfl := encodes_unique hA (encodes_of_decodes h hd)
  have hz : Q.toPoint.Z = 1 := hd.2.1
  exact
    ⟨show Q.toPoint.X * Q.toPoint.Z⁻¹ = _ by rw [hz, inv_one, mul_one],
      show Q.toPoint.Y * Q.toPoint.Z⁻¹ = _ by rw [hz, inv_one, mul_one]⟩

/-! ### A decoded QUAD's limbs -/

theorem extractLimbs_widenVec {v : Vector (BitVec 64) 6} {k : Fin 6}
    (hk : v[k.val].toNat < 2 ^ 62) : R43x6.extractLimbs (widenVec v) k = v[k.val].toNat := by
  have e : R43x6.extractLimbs (widenVec v) k = v[k.val].toInt := by fin_cases k <;> rfl
  rw [e, BitVec.toInt_eq_toNat_of_lt (by omega)]

theorem folded_of_decodeBounds {q : Quad} (hb : q.DecodeBounds) (j : Fin 4) :
    R43x6.Folded (widenVec (q.vector j)) := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have h : (q.vector j)[i.val].toNat < _ := hb.1 j i
    rw [if_neg
        (fun e => by
          subst e; simp at hi)] at h
    rw [extractLimbs_widenVec (by omega)]
    omega
  · have h : (q.vector j)[(5 : Fin 6).val].toNat < _ := hb.1 j 5
    rw [if_pos rfl] at h
    rw [extractLimbs_widenVec (by omega)]
    omega

theorem bits255_of_decodeBounds {q : Quad} (hb : q.DecodeBounds) :
    R43x6.Bits255 (widenVec (q.vector 1)) := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have h : (q.vector 1)[i.val].toNat < _ := hb.2 i
    rw [if_neg
        (fun e => by
          subst e; simp at hi)] at h
    rw [extractLimbs_widenVec (by omega)]
    omega
  · have h : (q.vector 1)[(5 : Fin 6).val].toNat < _ := hb.2 5
    rw [if_pos rfl] at h
    rw [extractLimbs_widenVec (by omega)]
    omega

theorem negBounds_of_decodeBounds {q : Quad} (hb : q.DecodeBounds) (j : Fin 4) : q.NegBounds j := by
  intro k
  have h := hb.1 j k
  fin_cases k <;> simp [twoPLimb] at h ⊢ <;> omega

theorem unn_of_negBounds {q : Quad} (h : ∀ j, q.NegBounds j) :
    R43x6.U44 q.v03 ∧ R43x6.U44 q.v14 ∧ R43x6.U44 q.v25 :=
  Ge.unn_of_quadLimb (by norm_num) fun j k => by
    rw [← laneFunc_vector]
    have hk := h j k
    show q.vectorFunc j k < _
    fin_cases k <;> simp [twoPLimb] at hk ⊢ <;> omega

theorem u46_of_u44 {q : Quad} (h : R43x6.U44 q.v03 ∧ R43x6.U44 q.v14 ∧ R43x6.U44 q.v25) : q.U46 :=
  have u46 {v : Vector (BitVec 64) 8} (h : R43x6.U44 v) : R43x6.U46 v :=
    ⟨fun i => (h.1 i).trans (by norm_num), h.2⟩
  ⟨u46 h.1, u46 h.2.1, u46 h.2.2⟩

theorem u46_of_decodeBounds {q : Quad} (hb : q.DecodeBounds) : q.U46 :=
  u46_of_u44 (unn_of_negBounds (negBounds_of_decodeBounds hb))

/-! ### Frames -/

theorem wf_writeQuad' {t : GlobalState} {m : MemoryState} {r : Pointer} {q : Quad}
    (ht : ({ t with mem := m } : GlobalState).WF) :
    ({ t with mem := m.writeQuad r q } : GlobalState).WF := fun b hb =>
  live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none (ht b hb)))

theorem isQuadPtr_writeQuad_of {m : MemoryState} {p r : Pointer} {q : Quad} (hp : IsQuadPtr m p) :
    IsQuadPtr (m.writeQuad r q) p :=
  ⟨fits_splice (fits_splice (fits_splice hp.1)), hp.2⟩

set_option maxHeartbeats 5000000 in
theorem fd_ed25519_verify_conforms (msg : Pointer) (sz : BitVec 64) (sig pk sha : Pointer)
    (s : GlobalState) (hmsg : Fits s.mem msg (sz.toNat * 8)) (hr : IsByteBufPtr s.mem sig)
    (hS : IsByteBufPtr s.mem (sig.withOffset 32)) (ha : IsByteBufPtr s.mem pk)
    (hsignull : sig.id ≠ SLLVM.nullBlock) (f : BitVec (64 * 8) → Option (Fin 4 → BitVec 64))
    (kbits : BitVec (80 * 64)) (fInit : Option LiveBlock → BitVec 64 → Option (Option LiveBlock))
    (fApp : Option LiveBlock → BitVec 64 → List (BitVec 8) → Option (Option LiveBlock))
    (fFini : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option (BitVec 512))
    (fFiniBlk : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option LiveBlock) :
    fd_ed25519_verify_spec msg sz sig pk sha s hmsg hr hS ha f kbits fInit fApp fFini fFiniBlk := by
  simp only [fd_ed25519_verify_spec, Cfg.denote]
  intro hsigoff hmsgoff hsha hshaoff hK hshasig hshapk hshamsg hwf hf hInit hApp hFini g0 g1 hg0 hg1
    hgp0 hgp1 hgv0 hgv1 hgr0 hgr1 Bt hTbl hB dig hdig w hw
  -- the digest's chain: the init, three appends and the fini, each of which returned
  simp only [ed25519Digest, Option.bind_eq_some_iff] at hdig
  obtain ⟨b₀, hb₀, b₁, hb₁, b₂, hb₂, b₃, hb₃, hfin⟩ := hdig
  refine
    run_runFunction_ret
      (fun ret : BitVec 32 => ([.value ret]ₕ : HVector toType [SLLVM.Ty.bitvec 32])) _ ?_
  -- `%0`–`%6`: the return codes, `1`, `32` and `NULL`
  denote_step_reduce v 6 [LLVM.const?] fold
  -- `%7`–`%10`: `Aprime`, `R`, `k`, `Rcmp`
  obtain ⟨Ap, s₁, hApdef, hs₁def, hs₁, hApfits, -, hApoff, hctr₁, -⟩ :=
    GlobalState.exists_afterAlloca_facts s hwf (3 * 8 * 64)
  obtain ⟨Rp, s₂, hRpdef, hs₂def, hs₂, hRpfits, -, hRpoff, hctr₂, -⟩ :=
    GlobalState.exists_afterAlloca_facts s₁ hs₁ (3 * 8 * 64)
  obtain ⟨kp, s₃, hkpdef, hs₃def, hs₃, hkpfits, -, hkpoff, hctr₃, -⟩ :=
    GlobalState.exists_afterAlloca_facts s₂ hs₂ (64 * 8)
  obtain ⟨Rc, s₄, hRcdef, hs₄def, hs₄, hRcfits, -, hRcoff, hctr₄, -⟩ :=
    GlobalState.exists_afterAlloca_facts s₃ hs₃ (3 * 8 * 64)
  peel_alloca from s as s₁ with hs₁def
  peel_alloca from s₁ as s₂ with hs₂def
  peel_alloca from s₂ as s₃ with hs₃def
  peel_alloca from s₃ as s₄ with hs₄def
  rw [← hApdef, ← hRpdef, ← hkpdef, ← hRcdef]
  -- `%11`: `S = sig + 32`
  denote_step_all v 11
  denote_eval v 11 11
  replace hv11 : v11 = .value (sig.withOffset 32) := hv11.trans rfl
  subst hv11
  -- `%12`: `fd_curve25519_scalar_validate( S )`
  have fb₄ : FrameBelow s.alloc.nextFreeBlock s s₄ :=
    hs₄def ▸
      FrameBelow.afterAlloca (by omega)
        (hs₃def ▸
          FrameBelow.afterAlloca (by omega)
            (hs₂def ▸
              FrameBelow.afterAlloca (by omega)
                (hs₁def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _))))
  have hS₄ : IsByteBufPtr s₄.mem (sig.withOffset 32) :=
    ⟨fits_of_live?_eq (fb₄ _ (lt_nextFreeBlock_of_fits hwf hS.1)) hS.1, hS.2⟩
  obtain ⟨s₅, hrun₁₂, heq₁₂⟩ :=
    fd_curve25519_scalar_validate_conforms (sig.withOffset 32) s₄ hs₄ hS₄
  peel_call hrun₁₂
  denote_step_reduce v 13 [hv6, ptricmp, Ptr.null]
  have hbuf₄ : readBuf hS₄ = readBuf hS :=
    readBuf_of_live?_eq (fb₄ _ (lt_nextFreeBlock_of_fits hwf hS.1))
  rw [hbuf₄] at hv13
  by_cases hS₁₂ : (readBuf hS).toNat < groupOrder <;>
    simp only [hS₁₂, true_implies, false_implies] at hv13 <;>
    simp [Pointer.withOffset, hsignull] at hv13 <;>
    simp [hv13] <;>
    denote_enter_block
  pick_goal 2
  simp_return
  simp [hv3, FD_ED25519_ERR_SIG, FD_ED25519_ERR_PUBKEY, FD_ED25519_SUCCESS, FD_ED25519_ERR_MSG]
  have hpop₅ := (fb₄.of_equiv heq₁₂).popFrame_equiv hwf
  refine ⟨rfl, fun b _ => hpop₅.live b, hpop₅.symm, ?_⟩
  simp [hS₁₂]
  iterate 2 peel_lifetime
  -- `%14`: `fd_ed25519_point_frombytes_2x( Aprime, public_key, R, r )`
  -- the locals sit at or above `s`'s counter, the caller's blocks below it
  have hlt : ∀ {p : Pointer} {n : Nat}, Fits s.mem p n → p.id.id < s.alloc.nextFreeBlock := fun h =>
    lt_nextFreeBlock_of_fits hwf h
  have hne :
    ∀ (q : Pointer) (b : BlockId),
      s.alloc.nextFreeBlock ≤ q.id.id → b.id < s.alloc.nextFreeBlock → q.id ≠ b :=
    fun q b hq hb h => by
    have := congrArg BlockId.id h; omega
  have hApge : s.alloc.nextFreeBlock ≤ Ap.id.id := by rw [hApdef]
  have hRpge : s.alloc.nextFreeBlock ≤ Rp.id.id := by
    rw [hRpdef]; simp only; omega
  have fb₅ : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → s₅.mem.live? b = s.mem.live? b :=
    fun b hb => (heq₁₂.live b).symm.trans (fb₄ b hb)
  have fbAp : FrameBelow s₁.alloc.nextFreeBlock s₁ s₄ :=
    hs₄def ▸
      FrameBelow.afterAlloca (by omega)
        (hs₃def ▸
          FrameBelow.afterAlloca (by omega)
            (hs₂def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)))
  have fbRp : FrameBelow s₂.alloc.nextFreeBlock s₂ s₄ :=
    hs₄def ▸
      FrameBelow.afterAlloca (by omega)
        (hs₃def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _))
  have hAp₅ : IsQuadPtr s₅.mem Ap :=
    ⟨fits_of_live?_eq
        ((heq₁₂.live _).symm.trans
          (fbAp _
            (by
              rw [hApdef]; simp only; omega)))
        hApfits,
      by
      rw [hApoff]; simp⟩
  have hRp₅ : IsQuadPtr s₅.mem Rp :=
    ⟨fits_of_live?_eq
        ((heq₁₂.live _).symm.trans
          (fbRp _
            (by
              rw [hRpdef]; simp only; omega)))
        hRpfits,
      by
      rw [hRpoff]; simp⟩
  have hpk₅ : IsByteBufPtr s₅.mem pk := ⟨fits_of_live?_eq (fb₅ _ (hlt ha.1)) ha.1, ha.2⟩
  have hsig₅ : IsByteBufPtr s₅.mem sig := ⟨fits_of_live?_eq (fb₅ _ (hlt hr.1)) hr.1, hr.2⟩
  have hwf₅ : s₅.WF := hs₄.of_equiv heq₁₂
  obtain ⟨s₆, ret₁₄, qA, qR, hrun₁₄, hs₆, hok₁₄, hfailA, hfailR⟩ :=
    fd_ed25519_point_frombytes_2x_conforms Ap pk Rp sig s₅ hwf₅ hAp₅ hpk₅ hRp₅ hsig₅
  peel_call hrun₁₄
  denote_step_reduce v 20 [hv2, ptricmp, Ptr.null, LLVM.icmp, LLVM.icmp?, LLVM.icmp']
  have hbufa₅ : readBuf hpk₅ = readBuf ha := readBuf_of_live?_eq (fb₅ _ (hlt ha.1))
  have hbufr₅ : readBuf hsig₅ = readBuf hr := readBuf_of_live?_eq (fb₅ _ (hlt hr.1))
  -- the two decompressions leave `s` alone below its counter, whatever they wrote
  have fb₆ : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → s₆.mem.live? b = s.mem.live? b :=
    fun b hb =>
    (Firedancer.live?_of_equiv_mem' hs₆ b).trans
      ((Ge.live?_writeQuad_ne (hne Rp b hRpge hb)).trans
        ((Ge.live?_writeQuad_ne (hne Ap b hApge hb)).trans (fb₅ b hb)))
  by_cases hdA : Decodable (readWv hpk₅)
  case neg =>
    -- `A` does not decode: `^bb2(-2)`
    obtain ⟨hret, -, -⟩ := hfailA hdA
    simp [hret] at hv20
    simp [hv20]
    denote_enter_block
    denote_step_reduce v 21 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', hv1, hv3, LLVM.select, simp_sllvm,
      hret] fold
    clear hv20
    simp_return
    denote_enter_block
    iterate 2 peel_lifetime
    simp_return
    denote_enter_block
    simp_return
    simp [hv21, FD_ED25519_ERR_SIG, FD_ED25519_ERR_PUBKEY, FD_ED25519_SUCCESS, FD_ED25519_ERR_MSG]
    have hpop := FrameBelow.popFrame_equiv (s' := s₆) hwf fb₆
    refine ⟨rfl, fun b _ => hpop.live b, hpop.symm, ?_⟩
    simp [hS₁₂]
    have hnA : ∀ A, ¬Encodes (readBuf ha) A := fun A hA =>
      hdA
        (decodable_of_encodes hpk₅
          (by
            rw [hbufa₅]; exact hA))
    exact ⟨fun A hA => (hnA A hA).elim, fun A _ hA _ => (hnA A hA).elim⟩
  by_cases hdR : Decodable (readWv hsig₅)
  case neg =>
    -- `R` does not decode: `^bb2(-1)`
    obtain ⟨hret, -, -⟩ := hfailR hdA hdR
    simp [hret] at hv20
    simp [hv20]
    denote_enter_block
    denote_step_reduce v 21 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', hv1, hv3, LLVM.select, simp_sllvm,
      hret] fold
    clear hv20
    simp_return
    denote_enter_block
    iterate 2 peel_lifetime
    simp_return
    denote_enter_block
    simp_return
    simp [hv21, FD_ED25519_ERR_SIG, FD_ED25519_ERR_PUBKEY, FD_ED25519_SUCCESS, FD_ED25519_ERR_MSG]
    have hpop := FrameBelow.popFrame_equiv (s' := s₆) hwf fb₆
    refine ⟨rfl, fun b _ => hpop.live b, hpop.symm, ?_⟩
    simp [hS₁₂]
    have hnR : ∀ R, ¬Encodes (readBuf hr) R := fun R hR =>
      hdR
        (decodable_of_encodes hsig₅
          (by
            rw [hbufr₅]; exact hR))
    obtain ⟨A, hA⟩ := exists_encodes_of_decodable hpk₅ hdA
    exact
      ⟨⟨A, by
          rw [← hbufa₅]; exact hA⟩,
        fun A R _ hR => (hnR R hR).elim⟩
  obtain ⟨hret, decA, decR, bndA, bndR⟩ := hok₁₄ hdA hdR
  replace hv20 : v20 = PoisonOr.value 1#1 := by
    rw [hv20, hret]; rfl
  simp only [hv20, BlockCom.denote_term, Terminator.denote_condBr_value, simp_denote, simp_sllvm,
    hS₁₂, hbuf₄]
  denote_enter_block
  -- `^bb3`: both decoded, `s₆` holding `qA` at `Aprime` and `qR` at `R`
  have hRpAp : Rp.id ≠ Ap.id := by
    rw [hRpdef, hApdef]; simp [hctr₁]
  have hApW : IsQuadPtr (s₅.mem.writeQuad Ap qA) Ap := PointDbln.isQuadPtr_writeQuad hAp₅ qA
  have hRpW : IsQuadPtr (s₅.mem.writeQuad Ap qA) Rp := isQuadPtr_writeQuad_of hRp₅
  have hRpWW : IsQuadPtr ((s₅.mem.writeQuad Ap qA).writeQuad Rp qR) Rp :=
    PointDbln.isQuadPtr_writeQuad hRpW qR
  have hlA₆ : s₆.mem.live? Ap.id = (s₅.mem.writeQuad Ap qA).live? Ap.id :=
    (Firedancer.live?_of_equiv_mem' hs₆ Ap.id).trans (Ge.live?_writeQuad_ne hRpAp)
  have hAp₆ : IsQuadPtr s₆.mem Ap := Ge.isQuadPtr_of_live?_eq hlA₆ hApW
  have hqA₆ : readQuad hAp₆ = qA :=
    (readQuad_of_live?_eq hlA₆ hApW hAp₆).trans (Ge.readQuad_writeQuad hAp₅ hApW)
  have hwf₆ : s₆.WF := GlobalState.WF.of_equiv (wf_writeQuad' (wf_writeQuad' hwf₅)) hs₆.symm
  have hg₆ : s₆.globals = s.globals :=
    hs₆.globals.trans
      (by
        rw [← heq₁₂.globals, hs₄def, hs₃def, hs₂def, hs₁def]; rfl)
  have hg0lt : g0.id.id < s.alloc.nextFreeBlock := hlt hg0.1
  have hg1lt : g1.id.id < s.alloc.nextFreeBlock := hlt hg1.1
  -- the globals, at a state `≈`-reachable from `s₆`
  have globs :
    ∀ t : GlobalState,
      t.globals = s.globals →
        (∀ b : BlockId, b.id < s.alloc.nextFreeBlock → t.mem.live? b = s.mem.live? b) →
        ∃ (h0 : IsVecPtr t.mem g0) (h1 : IsVecPtr t.mem g1),
          GlobalPtr t "fd_ed25519_order8_point_y0" g0 ∧
            GlobalPtr t "fd_ed25519_order8_point_y1" g1 ∧
            readVec h0 = readVec hg0 ∧ readVec h1 = readVec hg1 :=
    fun t hg hl =>
    ⟨⟨fits_of_live?_eq (hl _ hg0lt) hg0.1, hg0.2⟩, ⟨fits_of_live?_eq (hl _ hg1lt) hg1.1, hg1.2⟩, by
      unfold GlobalPtr at hgp0 ⊢; rw [hg]; exact hgp0, by
      unfold GlobalPtr at hgp1 ⊢; rw [hg]; exact hgp1, by
      simp only [readVec, readVec?_of_live?_eq (hl _ hg0lt)], by
      simp only [readVec, readVec?_of_live?_eq (hl _ hg1lt)]⟩
  -- `%18`: `fd_ed25519_affine_is_small_order( A )`
  obtain ⟨hg0₆, hg1₆, hgp0₆, hgp1₆, hgv0₆, hgv1₆⟩ := globs s₆ hg₆ fb₆
  obtain ⟨s₇, hrun₁₈, heq₁₈⟩ :=
    fd_ed25519_affine_is_small_order_conforms Ap g0 g1 s₆ hwf₆ hAp₆ hg0₆ hg1₆
      (by
        rw [hqA₆]; exact decA.2.1)
      (by
        rw [hqA₆]; exact decA.1)
      hgp0₆ hgp1₆
      (by
        rw [hgv0₆]; exact hgv0)
      (by
        rw [hgv1₆]; exact hgv1)
      (by
        rw [hgv0₆]; exact hgr0)
      (by
        rw [hgv1₆]; exact hgr1)
      (by
        rw [hqA₆]; exact folded_of_decodeBounds bndA 0)
      (by
        rw [hqA₆]; exact bits255_of_decodeBounds bndA)
  -- the verdict as an opaque bit: the program's valuation never holds the decoded point
  obtain ⟨bA, hbA⟩ :
    ∃ b,
      (if ((readQuad hAp₆).toPoint.X, (readQuad hAp₆).toPoint.Y) ∈ lowOrder then 1#32 else 0#32) =
        b :=
    ⟨_, rfl⟩
  rw [hbA] at hrun₁₈
  peel_call hrun₁₈
  -- the stepper counts from the entry's depth, MLIR from `%19`
  denote_number_from 19
  denote_step_reduce v 19 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', hv2]
  by_cases hlowA : ((readQuad hAp₆).toPoint.X, (readQuad hAp₆).toPoint.Y) ∈ lowOrder <;>
    simp [hlowA] at hbA <;>
    subst hbA <;>
    simp at hv19 <;>
    simp only [hv19, BlockCom.denote_term, Terminator.denote_condBr_value, simp_denote,
      simp_sllvm] <;>
    denote_enter_block <;>
    rw [hqA₆] at hlowA
  · -- `^bb6(-2)`: `A` has small order
    iterate 2 peel_lifetime
    simp_return
    denote_enter_block
    simp_return
    simp [hv1, FD_ED25519_ERR_SIG, FD_ED25519_ERR_PUBKEY, FD_ED25519_SUCCESS, FD_ED25519_ERR_MSG]
    have hpop := (FrameBelow.of_equiv heq₁₈ fb₆).popFrame_equiv hwf
    refine ⟨rfl, fun b _ => hpop.live b, hpop.symm, ?_⟩
    simp [hS₁₂]
    refine
      ⟨fun _ _ =>
        ⟨_, by
          rw [← hbufr₅]; exact encodes_of_decodes hsig₅ decR⟩,
        fun A R hA _ => ?_⟩
    obtain ⟨hx, hy⟩ :=
      coords_of_encodes hpk₅ decA
        (by
          rw [hbufa₅]; exact hA)
    rw [hx, hy]
    exact ⟨fun h => absurd hlowA h, fun h => absurd hlowA h⟩
  -- `^bb4`: `R` at `s₇`, where the first call left `s₆`'s blocks
  have hlR₇ : s₇.mem.live? Rp.id = ((s₅.mem.writeQuad Ap qA).writeQuad Rp qR).live? Rp.id :=
    (heq₁₈.live Rp.id).symm.trans (Firedancer.live?_of_equiv_mem' hs₆ Rp.id)
  have hRp₇ : IsQuadPtr s₇.mem Rp := Ge.isQuadPtr_of_live?_eq hlR₇ hRpWW
  have hqR₇ : readQuad hRp₇ = qR :=
    (readQuad_of_live?_eq hlR₇ hRpWW hRp₇).trans (Ge.readQuad_writeQuad hRpW hRpWW)
  have fb₇ : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → s₇.mem.live? b = s.mem.live? b :=
    fun b hb => (heq₁₈.live b).symm.trans (fb₆ b hb)
  have hwf₇ : s₇.WF := hwf₆.of_equiv heq₁₈
  -- `%20`: `fd_ed25519_affine_is_small_order( R )`
  obtain ⟨hg0₇, hg1₇, hgp0₇, hgp1₇, hgv0₇, hgv1₇⟩ := globs s₇ (heq₁₈.globals.symm.trans hg₆) fb₇
  obtain ⟨s₈, hrun₂₀, heq₂₀⟩ :=
    fd_ed25519_affine_is_small_order_conforms Rp g0 g1 s₇ hwf₇ hRp₇ hg0₇ hg1₇
      (by
        rw [hqR₇]; exact decR.2.1)
      (by
        rw [hqR₇]; exact decR.1)
      hgp0₇ hgp1₇
      (by
        rw [hgv0₇]; exact hgv0)
      (by
        rw [hgv1₇]; exact hgv1)
      (by
        rw [hgv0₇]; exact hgr0)
      (by
        rw [hgv1₇]; exact hgr1)
      (by
        rw [hqR₇]; exact folded_of_decodeBounds bndR 0)
      (by
        rw [hqR₇]; exact bits255_of_decodeBounds bndR)
  obtain ⟨bR, hbR⟩ :
    ∃ b,
      (if ((readQuad hRp₇).toPoint.X, (readQuad hRp₇).toPoint.Y) ∈ lowOrder then 1#32 else 0#32) =
        b :=
    ⟨_, rfl⟩
  rw [hbR] at hrun₂₀
  peel_call hrun₂₀
  denote_number_from 21
  denote_step_reduce v 21 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', hv2]
  by_cases hlowR : ((readQuad hRp₇).toPoint.X, (readQuad hRp₇).toPoint.Y) ∈ lowOrder <;>
    simp [hlowR] at hbR <;>
    subst hbR <;>
    simp at hv21 <;>
    simp only [hv21, BlockCom.denote_term, Terminator.denote_condBr_value, simp_denote,
      simp_sllvm] <;>
    denote_enter_block <;>
    rw [hqR₇] at hlowR
  · -- `^bb6(-1)`: `R` has small order
    iterate 2 peel_lifetime
    simp_return
    denote_enter_block
    simp_return
    simp [hv3, FD_ED25519_ERR_SIG, FD_ED25519_ERR_PUBKEY, FD_ED25519_SUCCESS, FD_ED25519_ERR_MSG]
    have hpop := (FrameBelow.of_equiv heq₂₀ (FrameBelow.of_equiv heq₁₈ fb₆)).popFrame_equiv hwf
    refine ⟨rfl, fun b _ => hpop.live b, hpop.symm, ?_⟩
    refine
      ⟨⟨_, by
          rw [← hbufa₅]; exact encodes_of_decodes hpk₅ decA⟩,
        fun A R hA hR => ?_⟩
    obtain ⟨hx, hy⟩ :=
      coords_of_encodes hpk₅ decA
        (by
          rw [hbufa₅]; exact hA)
    obtain ⟨hx', hy'⟩ :=
      coords_of_encodes hsig₅ decR
        (by
          rw [hbufr₅]; exact hR)
    rw [hx, hy, hx', hy']
    exact ⟨hlowA, fun _ => hlowR⟩
  -- `^bb5`: neither has small order
  peel_lifetime
  -- `s₈` is `s₅` off the two points, and `s` below its counter
  have fb₈₅ : ∀ b : BlockId, Ap.id ≠ b → Rp.id ≠ b → s₈.mem.live? b = s₅.mem.live? b :=
    fun b hA hR =>
    (heq₂₀.live b).symm.trans
      ((heq₁₈.live b).symm.trans
        ((Firedancer.live?_of_equiv_mem' hs₆ b).trans
          ((Ge.live?_writeQuad_ne hR).trans (Ge.live?_writeQuad_ne hA))))
  have fb₈ : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → s₈.mem.live? b = s.mem.live? b :=
    fun b hb => (fb₈₅ b (hne Ap b hApge hb) (hne Rp b hRpge hb)).trans (fb₅ b hb)
  have hwf₈ : s₈.WF := hwf₇.of_equiv heq₂₀
  have hkpblk₈ : s₈.mem.live? kp.id = s₃.mem.live? kp.id := by
    have fbkp : FrameBelow s₃.alloc.nextFreeBlock s₃ s₄ :=
      hs₄def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
    rw [fb₈₅ _
        (by
          rw [hApdef, hkpdef]; simp [hctr₁, hctr₂]; omega)
        (by
          rw [hRpdef, hkpdef]; simp [hctr₂]),
      ← heq₁₂.live,
      fbkp _
        (by
          rw [hkpdef]; simp only; omega)]
  have hkp₈ : Fits s₈.mem kp (64 * 8) := fits_of_live?_eq hkpblk₈ hkpfits
  -- `%22`: `fd_sha512_init( sha )`
  have hsha₈ : IsSha512Ptr s₈.mem sha := fits_of_live?_eq (fb₈ _ (hlt hsha)) hsha
  obtain ⟨hret₂₂, -⟩ := hInit sha s₈ hwf₈ hsha₈
  rw [fb₈ _ (hlt hsha)] at hret₂₂
  obtain ⟨s₉, hrun₂₂, hwf₉, -, hg₉₈, fr₉, hblk₉⟩ := hret₂₂ b₀ hb₀
  peel_call hrun₂₂
  have hg₉ : s₉.globals = s.globals :=
    hg₉₈.trans (heq₂₀.globals.symm.trans (heq₁₈.globals.symm.trans hg₆))
  have hK₉ : Sha512KHolds s₉ sha kbits :=
    hK.of_live?_eq hwf hg₉ fun b hb hb' => (fr₉ b hb).trans (fb₈ b hb')
  -- `%23`: `fd_sha512_append( sha, r, 32 )`
  have hl₉ : s₉.mem.live? sig.id = s.mem.live? sig.id :=
    (fr₉ _ hshasig.symm).trans (fb₈ _ (hlt hr.1))
  have hw₉ : readWord (fits_of_live?_eq hl₉ hr.1) = readBuf hr := readWord_eq_of_live?_eq hl₉ hr.1
  obtain ⟨hret₂₃, -⟩ :=
    hApp sha sig 32#64 s₉ hwf₉
      (by
        show sig.offset.toNat + 32 ≤ 2 ^ 64; exact hr.2)
      hshasig hK₉ (fits_of_live?_eq hl₉ hr.1)
  rw [hblk₉, hw₉] at hret₂₃
  obtain ⟨s₁₀, hrun₂₃, hwf₁₀, -, hg₁₀, fr₁₀, hblk₁₀⟩ := hret₂₃ b₁ hb₁
  subst hv5
  peel_call hrun₂₃
  have hK₁₀ : Sha512KHolds s₁₀ sha kbits :=
    hK.of_live?_eq hwf (hg₁₀.trans hg₉) fun b hb hb' =>
      (fr₁₀ b hb).trans ((fr₉ b hb).trans (fb₈ b hb'))
  -- `%24`: `fd_sha512_append( sha, public_key, 32 )`
  have hl₁₀ : s₁₀.mem.live? pk.id = s.mem.live? pk.id :=
    (fr₁₀ _ hshapk.symm).trans ((fr₉ _ hshapk.symm).trans (fb₈ _ (hlt ha.1)))
  have hw₁₀ : readWord (fits_of_live?_eq hl₁₀ ha.1) = readBuf ha :=
    readWord_eq_of_live?_eq hl₁₀ ha.1
  obtain ⟨hret₂₄, -⟩ :=
    hApp sha pk 32#64 s₁₀ hwf₁₀
      (by
        show pk.offset.toNat + 32 ≤ 2 ^ 64; exact ha.2)
      hshapk hK₁₀ (fits_of_live?_eq hl₁₀ ha.1)
  rw [hblk₁₀, hw₁₀] at hret₂₄
  obtain ⟨s₁₁, hrun₂₄, hwf₁₁, -, hg₁₁, fr₁₁, hblk₁₁⟩ := hret₂₄ b₂ hb₂
  peel_call hrun₂₄
  have hK₁₁ : Sha512KHolds s₁₁ sha kbits :=
    hK.of_live?_eq hwf (hg₁₁.trans (hg₁₀.trans hg₉)) fun b hb hb' =>
      (fr₁₁ b hb).trans ((fr₁₀ b hb).trans ((fr₉ b hb).trans (fb₈ b hb')))
  -- `%25`: `fd_sha512_append( sha, msg, msg_sz )`
  have hl₁₁ : s₁₁.mem.live? msg.id = s.mem.live? msg.id :=
    (fr₁₁ _ hshamsg.symm).trans
      ((fr₁₀ _ hshamsg.symm).trans ((fr₉ _ hshamsg.symm).trans (fb₈ _ (hlt hmsg))))
  have hw₁₁ : readWord (fits_of_live?_eq hl₁₁ hmsg) = readWord hmsg :=
    readWord_eq_of_live?_eq hl₁₁ hmsg
  obtain ⟨hret₂₅, -⟩ := hApp sha msg sz s₁₁ hwf₁₁ hmsgoff hshamsg hK₁₁ (fits_of_live?_eq hl₁₁ hmsg)
  rw [hblk₁₁, hw₁₁] at hret₂₅
  obtain ⟨s₁₂, hrun₂₅, hwf₁₂, -, hg₁₂, fr₁₂, hblk₁₂⟩ := hret₂₅ b₃ hb₃
  peel_call hrun₂₅
  have hK₁₂ : Sha512KHolds s₁₂ sha kbits :=
    hK.of_live?_eq hwf (hg₁₂.trans (hg₁₁.trans (hg₁₀.trans hg₉))) fun b hb hb' =>
      (fr₁₂ b hb).trans ((fr₁₁ b hb).trans ((fr₁₀ b hb).trans ((fr₉ b hb).trans (fb₈ b hb'))))
  -- `%26`: `fd_sha512_fini( sha, k )`
  have hkpsha : sha.id ≠ kp.id :=
    (hne kp sha.id
        (by
          rw [hkpdef]; simp only; omega)
        (hlt hsha)).symm
  have hkpblk₁₂ : s₁₂.mem.live? kp.id = some { length := 64, bytes := 0#_ } := by
    rw [fr₁₂ _ hkpsha.symm, fr₁₁ _ hkpsha.symm, fr₁₀ _ hkpsha.symm, fr₉ _ hkpsha.symm, hkpblk₈,
      hs₃def, hkpdef]
    exact live?_afterAlloca_self s₂ (64 * 8)
  obtain ⟨hret₂₆, -⟩ :=
    hFini sha kp s₁₂ hwf₁₂
      (fits_of_live?_eq
        ((fr₁₂ _ hkpsha.symm).trans
          ((fr₁₁ _ hkpsha.symm).trans ((fr₁₀ _ hkpsha.symm).trans (fr₉ _ hkpsha.symm))))
        hkp₈)
      (by
        rw [hkpoff]; simp)
      hkpsha hK₁₂
  rw [hblk₁₂, hkpblk₁₂, hkpoff] at hret₂₆
  obtain ⟨s₁₃, hrun₂₆, hwf₁₃, -, hg₁₃, fr₁₃, hshaBlk₁₃, hk⟩ := hret₂₆ dig hfin
  peel_call hrun₂₆
  -- `k` holds the digest
  obtain ⟨hk₁₃, hkval⟩ := hk
  -- `%27`: `fd_curve25519_scalar_reduce( k, k )`
  have hkbuf₁₃ : IsByteBufPtr s₁₃.mem kp :=
    ⟨Fits.mono hk₁₃ (by decide), by
      rw [hkpoff]; simp⟩
  obtain ⟨hret₂₇, -⟩ :=
    hf kp kp s₁₃ hwf₁₃ hkbuf₁₃
      (by
        rw [hkpoff]; simp)
      hk₁₃
  obtain ⟨s₁₄, hrun₂₇, heq₂₇⟩ :=
    hret₂₇ w
      (by
        rw [hkval]; exact hw)
  peel_call hrun₂₇
  peel_lifetime
  -- `%28`: `fd_ed25519_point_neg( Aprime, Aprime )`
  -- `Aprime` at `s₁₄` is as `frombytes_2x` left it: since then only `sha` and `k` were written
  have hwf₁₄ : s₁₄.WF := wf_of_equiv_scalarOutMem hwf₁₃ heq₂₇
  have hkpAp : kp.id ≠ Ap.id := by
    rw [hkpdef, hApdef]; simp only [ne_eq, BlockId.mk.injEq]; omega
  have hshaAp : sha.id ≠ Ap.id := (hne Ap sha.id hApge (hlt hsha)).symm
  have fr₁₄ : ∀ b : BlockId, kp.id ≠ b → s₁₄.mem.live? b = s₁₃.mem.live? b := fun b hb =>
    (Firedancer.live?_of_equiv_mem' heq₂₇ b).trans (live?_scalarOutMem_ne hb)
  have hlA : s₁₄.mem.live? Ap.id = (s₅.mem.writeQuad Ap qA).live? Ap.id :=
    (fr₁₄ _ hkpAp).trans
        ((fr₁₃ _ (not_or.mpr ⟨hshaAp.symm, hkpAp.symm⟩)).trans
          ((fr₁₂ _ hshaAp.symm).trans
            ((fr₁₁ _ hshaAp.symm).trans
              ((fr₁₀ _ hshaAp.symm).trans
                ((fr₉ _ hshaAp.symm).trans ((heq₁₈.trans heq₂₀).live Ap.id).symm))))) |>.trans
      hlA₆
  have hAp₁₄ : IsQuadPtr s₁₄.mem Ap := Ge.isQuadPtr_of_live?_eq hlA hApW
  have hqA₁₄ : readQuad hAp₁₄ = qA :=
    (readQuad_of_live?_eq hlA hApW hAp₁₄).trans (Ge.readQuad_writeQuad hAp₅ hApW)
  obtain ⟨s₁₅, hrun₂₈, qN, heq₂₈, hnval, hnb⟩ :=
    fd_ed25519_point_neg_self_conforms Ap s₁₄ hwf₁₄ hAp₁₄
      (by
        rw [hqA₁₄]; exact negBounds_of_decodeBounds bndA 0)
      (by
        rw [hqA₁₄]; exact negBounds_of_decodeBounds bndA 3)
  peel_call hrun₂₈
  rw [hqA₁₄] at hnval
  -- `%29`: `fd_ed25519_double_scalar_mul_base( Rcmp, k, Aprime, S )`
  have hApN : IsQuadPtr (s₁₄.mem.writeQuad Ap qN) Ap := PointDbln.isQuadPtr_writeQuad hAp₁₄ qN
  have hlN : s₁₅.mem.live? Ap.id = (s₁₄.mem.writeQuad Ap qN).live? Ap.id :=
    (Firedancer.live?_of_equiv_mem' heq₂₈.symm Ap.id).trans (Ge.live?_splice_BV hAp₁₄.2 qN Ap.id)
  have hAp₁₅ : IsQuadPtr s₁₅.mem Ap := Ge.isQuadPtr_of_live?_eq hlN hApN
  have hqN₁₅ : readQuad hAp₁₅ = qN :=
    (readQuad_of_live?_eq hlN hApN hAp₁₅).trans (Ge.readQuad_writeQuad hAp₁₄ hApN)
  have fr₁₅ : ∀ b : BlockId, Ap.id ≠ b → s₁₅.mem.live? b = s₁₄.mem.live? b := fun b hb =>
    (Firedancer.live?_of_equiv_mem' heq₂₈.symm b).trans
      ((Ge.live?_splice_BV hAp₁₄.2 qN b).trans (Ge.live?_writeQuad_ne hb))
  have fl₁₅ :
    ∀ b : BlockId,
      sha.id ≠ b → kp.id ≠ b → Ap.id ≠ b → Rp.id ≠ b → s₁₅.mem.live? b = s₅.mem.live? b :=
    fun b hs hk hA hR =>
    (fr₁₅ b hA).trans
      ((fr₁₄ b hk).trans
        ((fr₁₃ b (not_or.mpr ⟨hs.symm, hk.symm⟩)).trans
          ((fr₁₂ b hs.symm).trans
            ((fr₁₁ b hs.symm).trans
              ((fr₁₀ b hs.symm).trans ((fr₉ b hs.symm).trans (fb₈₅ b hA hR)))))))
  have hkpge : s.alloc.nextFreeBlock ≤ kp.id.id := by
    rw [hkpdef]; simp only; omega
  have hRcge : s.alloc.nextFreeBlock ≤ Rc.id.id := by
    rw [hRcdef]; simp only; omega
  have hwf₁₅ : s₁₅.WF := fun q hq =>
    (Firedancer.live?_of_equiv_mem' heq₂₈.symm q).trans
      (live?_splice_eq_none
        (hwf₁₄ q
          (by
            rw [← heq₂₈.alloc] at hq; exact hq)))
  have hg₁₅ : s₁₅.globals = s.globals :=
    heq₂₈.globals.symm.trans
      (heq₂₇.globals.trans (hg₁₃.trans (hg₁₂.trans (hg₁₁.trans (hg₁₀.trans hg₉)))))
  have hlive₁₅ :
    ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → b ≠ sha.id → s₁₅.mem.live? b = s.mem.live? b :=
    fun b hb hs =>
    (fl₁₅ b hs.symm (hne kp b hkpge hb) (hne Ap b hApge hb) (hne Rp b hRpge hb)).trans (fb₅ b hb)
  have hRc₁₅ : IsQuadPtr s₁₅.mem Rc :=
    Ge.isQuadPtr_of_live?_eq
      ((fl₁₅ _ (hne Rc sha.id hRcge (hlt hsha)).symm
            (by
              rw [hkpdef, hRcdef]; simp only [ne_eq, BlockId.mk.injEq]; omega)
            (by
              rw [hApdef, hRcdef]; simp only [ne_eq, BlockId.mk.injEq]; omega)
            (by
              rw [hRpdef, hRcdef]; simp only [ne_eq, BlockId.mk.injEq]; omega)).trans
        (heq₁₂.live Rc.id).symm)
      ⟨hRcfits, by
        rw [hRcoff]; simp⟩
  have hkbuf₁₅ : IsByteBufPtr s₁₅.mem kp :=
    Ref.isByteBufPtr_of_live?_eq
      ((fr₁₅ _ hkpAp.symm).trans (Firedancer.live?_of_equiv_mem' heq₂₇ kp.id))
      (by
        unfold scalarOutMem;
        exact
          isByteBufPtr_splice
            (isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice hkbuf₁₃))))
  have hS₁₅ : IsByteBufPtr s₁₅.mem (sig.withOffset 32) :=
    Ref.isByteBufPtr_of_live?_eq (hlive₁₅ _ (hlt hS.1) hshasig.symm) hS
  have hTbl₁₅ : BaseTableHolds s₁₅ Rc Bt := by
    obtain ⟨g, hgp, hgsha, hgk⟩ := hTbl
    obtain ⟨h0, -⟩ := hgk 0 (by norm_num)
    have hglt : (g.withOffset (BitVec.ofNat 64 (192 * 0))).id.id < s.alloc.nextFreeBlock := hlt h0.1
    have hid : (g.withOffset (BitVec.ofNat 64 (192 * 0))).id = g.id := rfl
    rw [hid] at hglt
    have hgl : s₁₅.mem.live? g.id = s.mem.live? g.id := hlive₁₅ g.id hglt hgsha
    refine
      ⟨g, by
        unfold GlobalPtr at hgp ⊢; rw [hg₁₅]; exact hgp, (hne Rc g.id hRcge hglt).symm, fun k hk' =>
        ?_⟩
    obtain ⟨hq, hbnd⟩ := hgk k hk'
    have hl :
      s₁₅.mem.live? (g.withOffset (BitVec.ofNat 64 (192 * k))).id =
        s.mem.live? (g.withOffset (BitVec.ofNat 64 (192 * k))).id :=
      hgl
    refine ⟨Ge.isQuadPtr_of_live?_eq hl hq, ?_⟩
    rw [readQuad_of_live?_eq hl hq]
    exact hbnd
  -- `-A` at `s₁₅`: well formed, and within `u44`
  have hwfA : qA.toPoint.WellFormed := wellFormed_of_decodes decA
  have hNeq : (readQuad hAp₁₅).toPoint = qA.toPoint.neg := by
    rw [hqN₁₅, hnval]; rfl
  have hwfN : (readQuad hAp₁₅).toPoint.WellFormed := by
    rw [hNeq]; exact Point.wellFormed_neg hwfA
  have hU := unn_of_negBounds hnb
  obtain ⟨s₁₆, hrun₂₉, qT, heq₂₉, hrep, hT₁, hT₂, hT₃⟩ :=
    fd_ed25519_double_scalar_mul_base_conforms Rc kp Ap (sig.withOffset 32) s₁₅ hwf₁₅ hRc₁₅ hAp₁₅
      hkbuf₁₅ hS₁₅ hwfN
      (by
        rw [hqN₁₅]; exact hU.1)
      (by
        rw [hqN₁₅]; exact hU.2.1)
      (by
        rw [hqN₁₅]; exact hU.2.2)
      Bt hTbl₁₅ hB
  peel_call hrun₂₉
  -- `%30`: `fd_ed25519_point_eq_z1( Rcmp, R )`
  have hRcRp : Rc.id ≠ Rp.id := by
    rw [hRcdef, hRpdef]; simp only [ne_eq, BlockId.mk.injEq]; omega
  have hkpRp : kp.id ≠ Rp.id := by
    rw [hkpdef, hRpdef]; simp only [ne_eq, BlockId.mk.injEq]; omega
  have hRpsha : sha.id ≠ Rp.id := (hne Rp sha.id hRpge (hlt hsha)).symm
  have hRcT : IsQuadPtr (s₁₅.mem.writeQuad Rc qT) Rc := PointDbln.isQuadPtr_writeQuad hRc₁₅ qT
  have hlRc : s₁₆.mem.live? Rc.id = (s₁₅.mem.writeQuad Rc qT).live? Rc.id :=
    Firedancer.live?_of_equiv_mem' heq₂₉.symm Rc.id
  have hRc₁₆ : IsQuadPtr s₁₆.mem Rc := Ge.isQuadPtr_of_live?_eq hlRc hRcT
  have hqT₁₆ : readQuad hRc₁₆ = qT :=
    (readQuad_of_live?_eq hlRc hRcT hRc₁₆).trans (Ge.readQuad_writeQuad hRc₁₅ hRcT)
  have hwf₁₆ : s₁₆.WF := GlobalState.WF.of_equiv (Ge.wf_writeQuad hwf₁₅) heq₂₉
  -- `R` at `s₁₆` is as `s₇` read it: nothing since wrote its block
  have hlR : s₁₆.mem.live? Rp.id = s₇.mem.live? Rp.id :=
    (Firedancer.live?_of_equiv_mem' heq₂₉.symm Rp.id).trans
      ((Ge.live?_writeQuad_ne hRcRp).trans
        ((fr₁₅ _ hRpAp.symm).trans
          ((fr₁₄ _ hkpRp).trans
            ((fr₁₃ _ (not_or.mpr ⟨hRpsha.symm, hkpRp.symm⟩)).trans
              ((fr₁₂ _ hRpsha.symm).trans
                ((fr₁₁ _ hRpsha.symm).trans
                  ((fr₁₀ _ hRpsha.symm).trans
                    ((fr₉ _ hRpsha.symm).trans (heq₂₀.live Rp.id).symm))))))))
  have hRp₁₆ : IsQuadPtr s₁₆.mem Rp := Ge.isQuadPtr_of_live?_eq hlR hRp₇
  have hqR₁₆ : readQuad hRp₁₆ = qR := (readQuad_of_live?_eq hlR hRp₇ hRp₁₆).trans hqR₇
  obtain ⟨s₁₇, hrun₃₀, heq₃₀⟩ :=
    fd_ed25519_point_eq_z1_conforms Rc Rp s₁₆ hwf₁₆ hRc₁₆ hRp₁₆
      (by
        rw [hqT₁₆]; exact u46_of_u44 ⟨hT₁, hT₂, hT₃⟩)
      (by
        rw [hqR₁₆]; exact u46_of_decodeBounds bndR)
      (by
        rw [hqT₁₆]; exact hrep.isUnit_Z)
      (by
        rw [hqR₁₆]; exact decR.2.1)
  obtain ⟨bE, hbE⟩ :
    ∃ b, (if (readQuad hRc₁₆).toPoint.SamePoint (readQuad hRp₁₆).toPoint then 1#32 else 0#32) = b :=
    ⟨_, rfl⟩
  rw [hbE] at hrun₃₀
  peel_call hrun₃₀
  denote_step_reduce v 30 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.select, hv2] fold
  -- the final state agrees with `s` off `sha`
  have hlive₁₇ : ∀ b : BlockId, ¬b = sha.id → (s.popFrame s₁₇.mem).mem.live? b = s.mem.live? b :=
    fun b hb => by
    show (s₁₇.mem.killFrom s.alloc.nextFreeBlock).live? b = _
    by_cases hb' : b.id < s.alloc.nextFreeBlock
    · have hRcb : Rc.id ≠ b := hne Rc b hRcge hb'
      rw [live?_killFrom_of_lt hb', ← heq₃₀.live b, Firedancer.live?_of_equiv_mem' heq₂₉.symm b,
        Ge.live?_writeQuad_ne hRcb, hlive₁₅ b hb' hb]
    · rw [live?_killFrom_of_le (by omega), hwf b (by omega)]
  -- `A`, `R` and the equation `Rcmp = R` decides
  have hwfR : qR.toPoint.WellFormed := wellFormed_of_decodes decR
  have hA : ∀ A, Encodes (readBuf ha) A → A = qA.toPoint.toAffine hwfA := fun A hA =>
    encodes_unique hA
      (by
        rw [← hbufa₅]; exact encodes_of_decodes hpk₅ decA)
  have hR : ∀ R, Encodes (readBuf hr) R → R = qR.toPoint.toAffine hwfR := fun R hR =>
    encodes_unique hR
      (by
        rw [← hbufr₅]; exact encodes_of_decodes hsig₅ decR)
  have hk : readBuf hkbuf₁₅ = packWords w := by
    have e :
      readBuf hkbuf₁₅ =
        readBuf (m := scalarOutMem s₁₃.mem kp _)
          (by
            unfold scalarOutMem
            exact
              isByteBufPtr_splice
                (isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice hkbuf₁₃)))) :=
      readBuf_of_live?_eq ((fr₁₅ _ hkpAp.symm).trans (Firedancer.live?_of_equiv_mem' heq₂₇ kp.id))
    rw [e, readBuf_scalarOutMem hkbuf₁₃]
  have hℓ : groupOrder < 2 ^ 255 := by
    unfold groupOrder; norm_num
  have hSeq : (readBuf hS₁₅).toNat = (readBuf hS).toNat := by
    rw [readBuf_of_live?_eq (hp := hS) (hlive₁₅ _ (hlt hS.1) hshasig.symm)]
  have heqn :
    (readQuad hRc₁₆).toPoint.SamePoint (readQuad hRp₁₆).toPoint ↔
      -(((packWords w).toNat % 2 ^ 255) • qA.toPoint.toAffine hwfA) +
          (readBuf hS).toNat • basePoint.toAffine wellFormed_basePoint =
        qR.toPoint.toAffine hwfR := by
    have hrep' := hrep
    rw [Point.toAffine_congr hNeq hwfN (Point.wellFormed_neg hwfA), Point.toAffine_neg, hk, hSeq,
      Nat.mod_eq_of_lt (hS₁₂.trans hℓ), smul_neg] at hrep'
    rw [hqT₁₆, hqR₁₆]
    exact samePoint_iff_of_represents hrep' hwfR
  have hconds :
    ∀ A R,
      Encodes (readBuf ha) A →
        Encodes (readBuf hr) R →
        ((A.x, A.y) ∉ lowOrder) ∧
          ((R.x, R.y) ∉ lowOrder) ∧ A = qA.toPoint.toAffine hwfA ∧ R = qR.toPoint.toAffine hwfR :=
    fun A R hA' hR' => by
    obtain ⟨hx, hy⟩ :=
      coords_of_encodes hpk₅ decA
        (by
          rw [hbufa₅]; exact hA')
    obtain ⟨hx', hy'⟩ :=
      coords_of_encodes hsig₅ decR
        (by
          rw [hbufr₅]; exact hR')
    exact
      ⟨by
        rw [hx, hy]; exact hlowA, by
        rw [hx', hy']; exact hlowR, hA A hA', hR R hR'⟩
  have hexA : ∃ A, Encodes (readBuf ha) A :=
    ⟨_, by
      rw [← hbufa₅]; exact encodes_of_decodes hpk₅ decA⟩
  have hexR : ∃ R, Encodes (readBuf hr) R :=
    ⟨_, by
      rw [← hbufr₅]; exact encodes_of_decodes hsig₅ decR⟩
  -- `sha`, the one block the hash wrote: nothing since `fini` has touched it
  have hRcsha : Rc.id ≠ sha.id := hne Rc sha.id hRcge (hlt hsha)
  have hsha₁₇ : (s.popFrame s₁₇.mem).mem.live? sha.id = s₁₃.mem.live? sha.id := by
    show (s₁₇.mem.killFrom s.alloc.nextFreeBlock).live? sha.id = _
    rw [live?_killFrom_of_lt (hlt hsha), ← heq₃₀.live sha.id,
      Firedancer.live?_of_equiv_mem' heq₂₉.symm sha.id, Ge.live?_writeQuad_ne hRcsha,
      fr₁₅ _ hshaAp.symm, fr₁₄ _ hkpsha.symm]
  have hshaChain :
    ∀ shaBlk,
      ed25519ShaBlock fInit fApp fFiniBlk (s.mem.live? sha.id) sha.offset (readBuf hr) (readBuf ha)
            (bytesOf (readWord hmsg)) =
          some shaBlk →
        (s.popFrame s₁₇.mem).mem.live? sha.id = shaBlk :=
    fun shaBlk hblk => by
    rw [hsha₁₇, hshaBlk₁₃]
    simpa [ed25519ShaBlock, hb₀, hb₁, hb₂, hb₃] using hblk
  by_cases hsame : (readQuad hRc₁₆).toPoint.SamePoint (readQuad hRp₁₆).toPoint
  on_goal 1 =>
    simp only [hsame, ite_true] at hbE; subst hbE; simp at hv30
  on_goal 2 =>
    simp only [hsame, ite_false] at hbE; subst hbE; simp at hv30
  all_goals
    iterate 2 peel_lifetime
    simp_return
    denote_enter_block
    iterate 2 peel_lifetime
    simp_return
    denote_enter_block
    simp_return
    refine
      ⟨_,
        hv30.trans
          (by
            first
            | exact hv0
            | rfl),
        rfl, hlive₁₇, ?_⟩
    simp [FD_ED25519_SUCCESS, FD_ED25519_ERR_SIG, FD_ED25519_ERR_PUBKEY, FD_ED25519_ERR_MSG, hS₁₂]
    refine ⟨hshaChain, hexA, fun _ _ => hexR, fun A R hA' hR' => ?_⟩
    obtain ⟨hlA', hlR', rfl, rfl⟩ := hconds A R hA' hR'
    refine ⟨hlA', fun _ => hlR', fun _ _ => ?_⟩
  · exact heqn.mp hsame
  · exact fun h => hsame (heqn.mpr h)

end Firedancer.Avx512
