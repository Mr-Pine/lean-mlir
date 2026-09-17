/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.fd_ed25519_verify
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Point
import SSA.Projects.Firedancer.Common.Proof.Scalar.fd_curve25519_scalar_validate
import SSA.Projects.Firedancer.Common.Proof.Scalar.fd_curve25519_scalar_reduce
import SSA.Projects.Firedancer.Common.Proof.SHA.fd_sha512_init
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_frombytes_2x
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_double_scalar_mul_base
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_eq_z1
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_neg_self

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519 Common

attribute [local irreducible] Common.fd_curve25519_scalar_validate
  fd_ed25519_point_frombytes_2x fd_ed25519_affine_is_small_order Common.fd_sha512_init
  Common.fd_sha512_append Common.fd_sha512_fini Common.fd_curve25519_scalar_reduce
  fd_ed25519_point_neg fd_ed25519_double_scalar_mul_base fd_ed25519_point_eq_z1

/-- `run_runFunction'` with the return value existential too, bound before the
state so each path picks its own. -/
theorem run_runFunction_ret {α β : Type} {body : EffectM α} {s : GlobalState} (f : β → α)
    (P : GlobalState → β → Prop)
    (h : ∃ (x : β) (s' : GlobalState),
      StateT.run body s = .value (f x, s') ∧ P (s.popFrame s'.mem) x) :
    ∃ (s' : GlobalState) (x : β), StateT.run (runFunction body) s = .value (f x, s') ∧ P s' x :=
  let ⟨x, t, hrun, hP⟩ := h
  ⟨s.popFrame t.mem, x, run_runFunction hrun, hP⟩

/-- A decompression's four stores keep a state well formed, stated at the shape
`frombytes_2x`'s spec leaves so the match is first-order. -/
theorem wf_pointOutMem {t : GlobalState} {m : MemoryState} {r : Pointer}
    {oX oY oZ oT : Fin 5 → BitVec 64} (ht : ({ t with mem := m } : GlobalState).WF) :
    ({ t with mem := pointOutMem m r oX oY oZ oT } : GlobalState).WF := fun q hq => by
  unfold pointOutMem
  exact live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none
    (live?_splice_eq_none (ht q hq))))

end Firedancer.Ref

/-! ### `fd_sha512_init`'s memory, and the round constants across a call -/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

theorem live?_sha512InitMem_self {m : MemoryState} {sha : Pointer} :
    (sha512InitMem m sha).live? sha.id = sha512InitBlock sha.offset (m.live? sha.id) := by
  simp only [sha512InitMem, Ref.Dbln.live?_splice_of_id (p := sha.withOffset 200) (b := sha.id) rfl,
    Ref.Dbln.live?_splice_of_id (p := sha.withOffset 184) (b := sha.id) rfl,
    Ref.Dbln.live?_splice_of_id (p := sha.withOffset 176) (b := sha.id) rfl,
    Ref.Dbln.live?_splice_of_id (p := sha.withOffset 168) (b := sha.id) rfl,
    Ref.Dbln.live?_splice_of_id (p := sha.withOffset 160) (b := sha.id) rfl,
    Ref.Dbln.live?_splice_of_id (p := sha.withOffset 152) (b := sha.id) rfl,
    Ref.Dbln.live?_splice_of_id (p := sha.withOffset 144) (b := sha.id) rfl,
    Ref.Dbln.live?_splice_of_id (p := sha.withOffset 136) (b := sha.id) rfl,
    Ref.Dbln.live?_splice_of_id (p := sha.withOffset 128) (b := sha.id) rfl, Option.map_map]
  rfl

/-- The round constants survive states that keep the symbol table and every caller block but
`sha`'s. -/
theorem Sha512KHolds.of_live?_eq {s t : GlobalState} {sha : Pointer} (hs : s.WF)
    (h : Sha512KHolds s sha) (hg : t.globals = s.globals)
    (hl : ∀ b : BlockId, b ≠ sha.id → b.id < s.alloc.nextFreeBlock → t.mem.live? b = s.mem.live? b) :
    Sha512KHolds t sha :=
  let ⟨q, ⟨hp, hfit, hval⟩, hne⟩ := h
  ⟨q, ⟨by unfold GlobalPtr at hp ⊢; rw [hg]; exact hp,
    (readWord_of_live?_eq (hl q.id hne (lt_nextFreeBlock_of_fits hs hfit)) hfit).imp
      fun _ hv => hv.trans hval⟩, hne⟩

/-- `readWord` across states that agree on the block. -/
theorem readWord_eq_of_live?_eq {m m' : MemoryState} {p : Pointer} {w : Nat} {h' : Fits m' p w}
    (hl : m'.live? p.id = m.live? p.id) (h : Fits m p w) : readWord h' = readWord h :=
  readWord_eq_of ((readWord?_of_live?_eq hl).trans (readWord?_eq_some h rfl))

theorem live?_sha512InitMem_ne {m : MemoryState} {sha : Pointer} {b : BlockId} (h : sha.id ≠ b) :
    (sha512InitMem m sha).live? b = m.live? b := by
  simp only [sha512InitMem, live?_splice_ne (p := sha.withOffset 128) h,
    live?_splice_ne (p := sha.withOffset 136) h, live?_splice_ne (p := sha.withOffset 144) h,
    live?_splice_ne (p := sha.withOffset 152) h, live?_splice_ne (p := sha.withOffset 160) h,
    live?_splice_ne (p := sha.withOffset 168) h, live?_splice_ne (p := sha.withOffset 176) h,
    live?_splice_ne (p := sha.withOffset 184) h, live?_splice_ne (p := sha.withOffset 200) h]

theorem live?_sha512InitMem_eq_none {m : MemoryState} {sha : Pointer} {q : BlockId}
    (h : m.live? q = none) : (sha512InitMem m sha).live? q = none := by
  unfold sha512InitMem
  iterate 9 refine live?_splice_eq_none ?_
  exact h

/-- Stated across `fd_sha512_init`'s `≈`: against `{ s with mem := sha512InitMem … }`
directly, the kernel unfolds the nine splices. -/
theorem wf_of_equiv_sha512InitMem {s t : GlobalState} {sha : Pointer} (hs : s.WF)
    (he : t ≈ ({ s with mem := sha512InitMem s.mem sha } : GlobalState)) : t.WF := fun q hq =>
  (Ref.live?_of_equiv_mem he q).trans (live?_sha512InitMem_eq_none (hs q (by rw [he.alloc] at hq; exact hq)))

end Firedancer.Common

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519 Common

/-! ### Frames for `scalar_reduce` and the base table

These belong beside `scalarOutMem` and `BaseTableHolds`. -/

/-- The four words `scalar_reduce` stores, read back as its 32-byte output. -/
theorem readBuf_scalarOutMem {m : MemoryState} {r : Pointer} {w : Fin 4 → BitVec 64}
    (hm : IsByteBufPtr m r) (h : IsByteBufPtr (scalarOutMem m r w) r) :
    readBuf h = packWords w := by
  obtain ⟨⟨b, hb, hlen⟩, hoff⟩ := hm
  have hl : m.live? r.id = some b := by simp only [MemoryState.live?, hb]
  have ho : ∀ k : BitVec 64, k.toNat < 32 →
      (r.withOffset k).offsetInBits = r.offsetInBits + 8 * k.toNat := fun k hk => by
    simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add,
      Nat.mod_eq_of_lt (show r.offset.toNat + k.toNat < 2 ^ 64 by omega)]
    omega
  have h4 := splicedLive _ (r.withOffset 24) _ (splicedLive _ (r.withOffset 16) _
    (splicedLive _ (r.withOffset 8) _ (splicedLive m r b hl (w 0)) (w 1)) (w 2)) (w 3)
  rw [ho 8 (by decide), ho 16 (by decide), ho 24 (by decide)] at h4
  have e : (scalarOutMem m r w).live? r.id = _ := h4
  simp only [readBuf, readBuf?, e, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.get_some]
  ext i hi
  have hin : r.offsetInBits + i < 8 * b.length := by
    simp only [LiveBlock.lengthInBits] at hlen; omega
  show _ = (w 3 ++ w 2 ++ w 1 ++ w 0).getLsbD i
  have e8 : (8 : BitVec 64).toNat = 8 := rfl
  have e16 : (16 : BitVec 64).toNat = 16 := rfl
  have e24 : (24 : BitVec 64).toNat = 24 := rfl
  rw [e8, e16, e24]
  clear h4 e ho hb hl h
  simp only [BitVec.getElem_extractLsb', getLsbD_spliceBits, BitVec.getLsbD_append]
  split_ifs <;> first | omega | exact congrArg (BitVec.getLsbD _) (by omega)

theorem live?_scalarOutMem_ne {m : MemoryState} {r : Pointer} {w : Fin 4 → BitVec 64}
    {b : BlockId} (h : r.id ≠ b) : (scalarOutMem m r w).live? b = m.live? b := by
  simp only [scalarOutMem, live?_splice_ne (p := r.withOffset 24) h,
    live?_splice_ne (p := r.withOffset 16) h, live?_splice_ne (p := r.withOffset 8) h,
    live?_splice_ne h]

/-- Across `scalar_reduce`'s `≈`, first-order for the reason `wf_of_equiv_sha512InitMem` is. -/
theorem wf_of_equiv_scalarOutMem {s t : GlobalState} {r : Pointer} {w : Fin 4 → BitVec 64}
    (hs : s.WF) (he : t ≈ ({ s with mem := scalarOutMem s.mem r w } : GlobalState)) : t.WF :=
  fun q hq => (live?_of_equiv_mem he q).trans (by
    unfold scalarOutMem
    iterate 4 refine live?_splice_eq_none ?_
    exact hs q (by rw [he.alloc] at hq; exact hq))

/-- The table carries to a state with the same symbol table and the table's block. -/
theorem BaseTableHolds.of_live?_eq {s s' : GlobalState} {Bt : ℕ → PrecomputedPoint}
    (h : BaseTableHolds s Bt) (hg : s'.globals = s.globals)
    (hl : ∀ q, GlobalPtr s "fd_ed25519_base_point_wnaf_table" q →
      s'.mem.live? q.id = s.mem.live? q.id) : BaseTableHolds s' Bt := fun q hq k hk => by
  have hq' : GlobalPtr s "fd_ed25519_base_point_wnaf_table" q := by
    unfold GlobalPtr at hq ⊢; rwa [hg] at hq
  obtain ⟨hp, hb, hv⟩ := h q hq' k hk
  have hl' : s'.mem.live? (q.withOffset (BitVec.ofNat 64 (160 * k))).id
      = s.mem.live? (q.withOffset (BitVec.ofNat 64 (160 * k))).id := hl q hq'
  refine ⟨isPointPtr_of_live?_eq hl' hp, fun i => carryBnd
    (q := (q.withOffset (BitVec.ofNat 64 (160 * k))).withOffset (i * (5 * 8)))
    (bound := 0x18000000000000) hl' (hb i), ?_⟩
  rw [readPoint_of_live?_eq hl' hp]
  exact hv

/-! ### Encodings -/

theorem sq_mul_den (V : Edwards.Point curve) : V.x ^ 2 * (d * V.y ^ 2 + 1) = V.y ^ 2 - 1 := by
  have h : -V.x ^ 2 + V.y ^ 2 = 1 + d * V.x ^ 2 * V.y ^ 2 := V.on
  linear_combination -h

theorem den_ne_zero (V : Edwards.Point curve) : d * V.y ^ 2 + 1 ≠ 0 := fun h0 => by
  have h := sq_mul_den V
  rw [h0, mul_zero] at h
  have hy : V.y ^ 2 = 1 := by linear_combination -h
  rw [hy, mul_one] at h0
  exact absurd (by linear_combination h0 : d = -1) (by decide)

/-- An encoded point makes the decompression ratio a square. -/
theorem isSquare_of_encodes {b : BitVec 256} {V : Edwards.Point curve} (h : Encodes b V) :
    IsSquare ((decodeBytes b ^ 2 - 1) / (d * decodeBytes b ^ 2 + 1)) := by
  rw [← h.1]
  exact ⟨V.x, by rw [← sq_mul_den, mul_div_assoc, div_self (den_ne_zero V), mul_one, sq]⟩

/-- An encoding names at most one point: `y` fixes `x²`, the sign bit `x`. -/
theorem encodes_unique {b : BitVec 256} {V W : Edwards.Point curve} (hV : Encodes b V)
    (hW : Encodes b W) : V = W := by
  have hy : V.y = W.y := hV.1.trans hW.1.symm
  have hx2 : V.x ^ 2 = W.x ^ 2 := by
    apply mul_right_cancel₀ (den_ne_zero V)
    rw [sq_mul_den, hy, sq_mul_den]
  refine Edwards.Point.ext ?_ hy
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx2 with h | h
  · exact h
  by_cases h0 : W.x = 0
  · rw [h, h0, neg_zero]
  have hV0 : V.x ≠ 0 := by rw [h]; exact neg_ne_zero.mpr h0
  have hpar := (hV.2 hV0).trans (hW.2 h0).symm
  rw [h, ZMod.neg_val, if_neg h0] at hpar
  have hlt := ZMod.val_lt W.x
  have hpos : W.x.val ≠ 0 := (ZMod.val_ne_zero W.x).mpr h0
  have hp : p % 2 = 1 := by decide
  omega

theorem wellFormed_of_isDecoding {P : Point} {b : BitVec 256} (h : IsDecoding P b) :
    P.WellFormed := by
  have hz : P.Z = 1 := h.2.1
  refine ⟨hz ▸ isUnit_one, h.1, ?_⟩
  have ht := h.2.2.2.1
  simp only [Point.x, Point.y, hz, inv_one, mul_one, div_one] at ht
  rw [hz, mul_one, ht]

theorem encodes_toAffine {P : Point} {b : BitVec 256} (h : IsDecoding P b) :
    Encodes b (P.toAffine (wellFormed_of_isDecoding h)) := by
  have hz : P.Z = 1 := h.2.1
  refine ⟨?_, fun hne => ?_⟩
  · show P.Y * P.Z⁻¹ = _; rw [hz, inv_one, mul_one]; exact h.2.2.1
  · change P.X * P.Z⁻¹ ≠ 0 at hne; show (P.X * P.Z⁻¹).val % 2 = 0 ↔ _
    rw [hz, inv_one, mul_one] at hne ⊢; exact h.2.2.2.2 hne

/-- `SamePoint` against a well-formed point is equality of what they stand for. -/
theorem samePoint_iff_of_represents {P Q : Point} {V : Edwards.Point curve} (hP : P.Represents V)
    (hQ : Q.WellFormed) : P.SamePoint Q ↔ V = Q.toAffine hQ :=
  ⟨fun h => Edwards.Point.ext (hP.x_eq.symm.trans h.1) (hP.y_eq.symm.trans h.2),
    fun h => ⟨hP.x_eq.trans (congrArg Edwards.Point.x h), hP.y_eq.trans (congrArg Edwards.Point.y h)⟩⟩

/-- Any point `b` encodes has the decoding's coordinates. -/
theorem coords_of_encodes {P : Point} {b : BitVec 256} {A : Edwards.Point curve}
    (h : IsDecoding P b) (hA : Encodes b A) : A.x = P.X ∧ A.y = P.Y := by
  obtain rfl := encodes_unique hA (encodes_toAffine h)
  have hz : P.Z = 1 := h.2.1
  exact ⟨show P.X * P.Z⁻¹ = _ by rw [hz, inv_one, mul_one],
    show P.Y * P.Z⁻¹ = _ by rw [hz, inv_one, mul_one]⟩

set_option maxHeartbeats 5000000 in
theorem fd_ed25519_verify_conforms (msg : Pointer) (sz : BitVec 64) (sig pk sha : Pointer)
    (s : GlobalState) (hmsg : Fits s.mem msg (sz.toNat * 8)) (hr : IsByteBufPtr s.mem sig)
    (hS : IsByteBufPtr s.mem (sig.withOffset 32)) (ha : IsByteBufPtr s.mem pk)
    (hsignull : sig.id ≠ SLLVM.nullBlock)
    (f : BitVec (64 * 8) → Option (Fin 4 → BitVec 64))
    (fApp : Option LiveBlock → BitVec 64 → List (BitVec 8) → Option (Option LiveBlock))
    (fFini : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option (BitVec 512)) :
    fd_ed25519_verify_spec msg sz sig pk sha s hmsg hr hS ha f fApp fFini := by
  simp only [fd_ed25519_verify_spec, Cfg.denote]
  intro hsigoff hmsgoff hsha hshaoff hK hshasig hshapk hshamsg hm hf hApp hFini Bt hTbl hB
    dig hdig w hw
  -- the digest's chain: three appends and the fini, each of which returned
  simp only [ed25519Digest, Option.bind_eq_some_iff] at hdig
  obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, hfin⟩ := hdig
  refine run_runFunction_ret
    (fun ret : BitVec 32 => ([.value ret]ₕ : HVector toType [SLLVM.Ty.bitvec 32])) _ ?_

  -- `%0`–`%6`: the return codes, `1`, `32` and `NULL`
  denote_step_reduce v 6 [LLVM.const?] fold

  -- `%7`–`%10`: `Aprime`, `R`, `k`, `Rcmp`
  obtain ⟨Ap, s₁, hApdef, hs₁def, hs₁, hApfits, -, hApoff, hctr₁, -⟩ :=
    GlobalState.exists_afterAlloca_facts s hm.wf (4 * (5 * 64))
  obtain ⟨Rp, s₂, hRpdef, hs₂def, hs₂, hRpfits, -, hRpoff, hctr₂, -⟩ :=
    GlobalState.exists_afterAlloca_facts s₁ hs₁ (4 * (5 * 64))
  obtain ⟨kp, s₃, hkpdef, hs₃def, hs₃, hkpfits, -, hkpoff, hctr₃, -⟩ :=
    GlobalState.exists_afterAlloca_facts s₂ hs₂ (64 * 8)
  obtain ⟨Rc, s₄, hRcdef, hs₄def, hs₄, hRcfits, -, hRcoff, hctr₄, -⟩ :=
    GlobalState.exists_afterAlloca_facts s₃ hs₃ (4 * (5 * 64))
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
    hs₄def ▸ FrameBelow.afterAlloca (by omega) (hs₃def ▸ FrameBelow.afterAlloca (by omega)
      (hs₂def ▸ FrameBelow.afterAlloca (by omega)
        (hs₁def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _))))
  have hS₄ : IsByteBufPtr s₄.mem (sig.withOffset 32) :=
    ⟨fits_of_live?_eq (fb₄ _ (lt_nextFreeBlock_of_fits hm.wf hS.1)) hS.1, hS.2⟩
  obtain ⟨s₅, hrun₁₂, heq₁₂⟩ :=
    fd_curve25519_scalar_validate_conforms (sig.withOffset 32) s₄ hs₄ hS₄
  peel_call hrun₁₂

  denote_step_reduce v 13 [hv6, ptricmp, Ptr.null]
  have hbuf₄ : readBuf hS₄ = readBuf hS :=
    readBuf_of_live?_eq (fb₄ _ (lt_nextFreeBlock_of_fits hm.wf hS.1))
  -- v4.34: `simp` no longer matches `readBuf` across the step's `BitVec.ofNat 64 32` offset
  rw [hbuf₄] at hv13
  by_cases hS₁₂ : (readBuf hS).toNat < groupOrder <;>
    simp only [hS₁₂, true_implies, false_implies] at hv13 <;>
    simp [Pointer.withOffset, hsignull] at hv13 <;> simp [hv13] <;> denote_enter_block

  pick_goal 2
  simp_return
  simp [hv3, FD_ED25519_ERR_SIG, FD_ED25519_ERR_PUBKEY, FD_ED25519_SUCCESS, FD_ED25519_ERR_MSG]
  have hpop₅ := (fb₄.of_equiv heq₁₂).popFrame_equiv hm.wf
  refine ⟨rfl, fun b _ => hpop₅.live b, hpop₅.symm, ?_⟩
  simp [hS₁₂]

  iterate 2 peel_lifetime

  -- `%14`: `fd_ed25519_point_frombytes_2x( Aprime, public_key, R, r )`
  -- the locals sit at or above `s`'s counter, the caller's blocks below it
  have hlt : ∀ {p : Pointer} {n : Nat}, Fits s.mem p n → p.id.id < s.alloc.nextFreeBlock :=
    fun h => lt_nextFreeBlock_of_fits hm.wf h
  have hne : ∀ (q : Pointer) (b : BlockId),
      s.alloc.nextFreeBlock ≤ q.id.id → b.id < s.alloc.nextFreeBlock → q.id ≠ b :=
    fun q b hq hb h => by have := congrArg BlockId.id h; omega
  have hApge : s.alloc.nextFreeBlock ≤ Ap.id.id := by rw [hApdef]
  have hRpge : s.alloc.nextFreeBlock ≤ Rp.id.id := by rw [hRpdef]; simp only; omega
  have hnullb : SLLVM.nullBlock.id < s.alloc.nextFreeBlock := by
    have := hlt hr.1; simp only [SLLVM.nullBlock]; omega
  -- `s₅` agrees with `s` below its counter, and each local with its own frame
  have fb₅ : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → s₅.mem.live? b = s.mem.live? b :=
    fun b hb => (heq₁₂.live b).symm.trans (fb₄ b hb)
  have fbAp : FrameBelow s₁.alloc.nextFreeBlock s₁ s₄ :=
    hs₄def ▸ FrameBelow.afterAlloca (by omega) (hs₃def ▸ FrameBelow.afterAlloca (by omega)
      (hs₂def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)))
  have fbRp : FrameBelow s₂.alloc.nextFreeBlock s₂ s₄ :=
    hs₄def ▸ FrameBelow.afterAlloca (by omega)
      (hs₃def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _))
  have hAp₅ : IsPointPtr s₅.mem Ap :=
    ⟨fits_of_live?_eq ((heq₁₂.live _).symm.trans (fbAp _ (by rw [hApdef]; simp only; omega)))
      hApfits, by rw [hApoff]; simp⟩
  have hRp₅ : IsPointPtr s₅.mem Rp :=
    ⟨fits_of_live?_eq ((heq₁₂.live _).symm.trans (fbRp _ (by rw [hRpdef]; simp only; omega)))
      hRpfits, by rw [hRpoff]; simp⟩
  have hpk₅ : IsByteBufPtr s₅.mem pk := ⟨fits_of_live?_eq (fb₅ _ (hlt ha.1)) ha.1, ha.2⟩
  have hsig₅ : IsByteBufPtr s₅.mem sig := ⟨fits_of_live?_eq (fb₅ _ (hlt hr.1)) hr.1, hr.2⟩
  have hm₅ : s₅.RefWF [Ap, Rp] :=
    DoubleScalarMulBase.refWF_widen hm (hs₄.of_equiv heq₁₂)
      (by rw [← heq₁₂.globals, hs₄def, hs₃def, hs₂def, hs₁def]; rfl)
      (fun b hb _ => fb₅ b hb)
      (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact .inl hApge
        · exact .inl hRpge)
  obtain ⟨s₆, ret₁₄, hrun₁₄, hfail₁₄, hok₁₄⟩ :=
    fd_ed25519_point_frombytes_2x_conforms Ap pk Rp sig s₅ hm₅ hAp₅ hpk₅ hRp₅ hsig₅
      (Ne.symm (hne Ap pk.id hApge (hlt ha.1))) (Ne.symm (hne Rp sig.id hRpge (hlt hr.1)))
      (hne Ap _ hApge hnullb) (hne Rp _ hRpge hnullb)
  peel_call hrun₁₄

  denote_step_reduce v 20 [hv2, ptricmp, Ptr.null, LLVM.icmp, LLVM.icmp?, LLVM.icmp']

  have hbufa₅ : readBuf hpk₅ = readBuf ha := readBuf_of_live?_eq (fb₅ _ (hlt ha.1))
  by_cases h : IsSquare ((decodeBytes (readBuf hpk₅) ^ 2 - 1) / (d * decodeBytes (readBuf hpk₅) ^ 2 + 1))

  case neg =>
    -- `A` does not decode: `^bb2(-2)`
    have hret := hfail₁₄ h
    simp [hret] at hv20
    simp [hv20]
    denote_enter_block
    denote_step_reduce v 21 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', hv1, hv3, LLVM.select, simp_sllvm, hret] fold
    clear hv20
    simp_return
    denote_enter_block
    iterate 2 peel_lifetime
    simp_return
    denote_enter_block
    simp_return
    simp [hv21, FD_ED25519_ERR_SIG, FD_ED25519_ERR_PUBKEY, FD_ED25519_SUCCESS, FD_ED25519_ERR_MSG]
    have hpop := ((fb₄.of_equiv heq₁₂).of_equiv hret.2).popFrame_equiv hm.wf
    refine ⟨rfl, fun b _ => hpop.live b, hpop.symm, ?_⟩
    simp [hS₁₂]
    rw [hbufa₅] at h
    exact ⟨fun A hA => (h (isSquare_of_encodes hA)).elim,
      fun A _ hA _ => (h (isSquare_of_encodes hA)).elim⟩

  obtain ⟨oX, oY, oZ, oT, decodes, bndA, hnonsq, hsq⟩ := hok₁₄ h
  rcases (Classical.em _).imp (fun hs => And.intro hs (hsq hs)) (fun hs => And.intro hs (hnonsq hs))
    with ⟨hs, pX, pY, pZ, pT, hret, hs₆, decR, bndR⟩ | ⟨hs, hret, hs₆⟩ <;> clear hsq hnonsq

  case pos.inr =>
    -- `R` does not decode: `^bb2(-1)`, `Aprime` written
    simp [hret] at hv20
    simp [hv20]
    denote_enter_block
    denote_step_reduce v 21 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', hv1, hv3, LLVM.select, simp_sllvm, hret] fold
    clear hv20
    simp_return
    denote_enter_block
    iterate 2 peel_lifetime
    simp_return
    denote_enter_block
    simp_return
    simp [hv21, FD_ED25519_ERR_SIG, FD_ED25519_ERR_PUBKEY, FD_ED25519_SUCCESS, FD_ED25519_ERR_MSG]
    have hpop := FrameBelow.popFrame_equiv (s' := s₆) hm.wf fun b hb =>
      (live?_of_equiv_mem hs₆ b).trans ((live?_pointOutMem_ne (hne Ap b hApge hb)).trans (fb₅ b hb))
    refine ⟨rfl, fun b _ => hpop.live b, hpop.symm, ?_⟩
    simp [hS₁₂]
    -- v4.34: `rw` rejects `hs`'s spec-internal proof of `sig`'s buffer, so restate it
    have hsig₆ : IsByteBufPtr (pointOutMem s₅.mem Ap oX oY oZ oT) sig :=
      isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice hsig₅)))
    replace hs : ¬IsSquare ((decodeBytes (readBuf hsig₆) ^ 2 - 1)
        / (d * decodeBytes (readBuf hsig₆) ^ 2 + 1)) := hs
    rw [readBuf_of_live?_eq (hp := hr) ((live?_pointOutMem_ne (hne Ap sig.id hApge (hlt hr.1))).trans
      (fb₅ _ (hlt hr.1)))] at hs
    exact ⟨⟨_, encodes_toAffine (b := readBuf ha) (by rw [← hbufa₅]; exact decodes)⟩,
      fun A R _ hR => (hs (isSquare_of_encodes hR)).elim⟩

  simp only [hv20, BlockCom.denote_term, Terminator.denote_condBr, simp_denote, simp_sllvm, hret, hS₁₂, hbuf₄]
  denote_enter_block

  -- `^bb3`: both decoded, `s₆` holding `A` at `Aprime` and `R` at `R`
  have hRpAp : Rp.id ≠ Ap.id := by rw [hRpdef, hApdef]; simp [hctr₁]
  have hAp₁ : IsPointPtr (pointOutMem s₅.mem Ap oX oY oZ oT) Ap :=
    isPointPtr_pointOutMem hAp₅ oX oY oZ oT
  have hRp₁ : IsPointPtr (pointOutMem s₅.mem Ap oX oY oZ oT) Rp :=
    isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hRp₅)))
  have hAp₆ : IsPointPtr s₆.mem Ap :=
    isPointPtr_of_equiv hs₆ (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice
      (isPointPtr_splice hAp₁))))
  have hApval : readPoint hAp₆ = readPoint hAp₁ :=
    readPoint_of_live?_eq ((live?_of_equiv_mem hs₆ Ap.id).trans (live?_pointOutMem_ne hRpAp))
      hAp₁ hAp₆
  have hwf₆ : s₆.WF := GlobalState.WF.of_equiv (wf_pointOutMem (wf_pointOutMem hm₅.wf)) hs₆.symm
  have hm₆ : s₆.RefWF [] :=
    (hm₅.untouched hwf₆ hs₆.globals fun b hb =>
      (live?_of_equiv_mem hs₆ b).trans ((live?_pointOutMem_ne (Ne.symm (hb Rp (by simp)))).trans
        (live?_pointOutMem_ne (Ne.symm (hb Ap (by simp)))))).mono (by simp)
  have fb₆ : FrameBelow s.alloc.nextFreeBlock s s₆ := fun b hb =>
    (live?_of_equiv_mem hs₆ b).trans ((live?_pointOutMem_ne (hne Rp b hRpge hb)).trans
      ((live?_pointOutMem_ne (hne Ap b hApge hb)).trans (fb₅ b hb)))
  have decA : IsDecoding (readPoint hAp₆) (readBuf ha) := by rw [hApval, ← hbufa₅]; exact decodes
  have decR' : IsDecoding (readPoint (isPointPtr_pointOutMem hRp₁ pX pY pZ pT)) (readBuf hr) := by
    have e : readBuf (m := pointOutMem s₅.mem Ap oX oY oZ oT) (isByteBufPtr_splice
        (isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice hsig₅)))) = readBuf hr :=
      readBuf_of_live?_eq ((live?_pointOutMem_ne (hne Ap sig.id hApge (hlt hr.1))).trans
        (fb₅ _ (hlt hr.1)))
    rw [← e]; exact decR

  have hZA : (readPoint hAp₆).Z = 1 := by rw [hApval]; exact decodes.2.1
  have hcA : OnCurve (readPoint hAp₆).x (readPoint hAp₆).y := by rw [hApval]; exact decodes.1
  have hlA₆ : s₆.mem.live? Ap.id = (pointOutMem s₅.mem Ap oX oY oZ oT).live? Ap.id :=
    (live?_of_equiv_mem hs₆ Ap.id).trans (live?_pointOutMem_ne hRpAp)
  have hAzero : ZeroRep Ap s₆.mem :=
    ZeroRep.of_readLimb? (fun i => readLimb?_of_live?_eq hlA₆ i) bndA.2.2.2.2
  have hAY : LimbBounds (isCoordPtr hAp₆ 1) :=
    carryBnd (q := Ap.withOffset ((1 : Fin 4) * (5 * 8))) hlA₆ bndA.2.1

  -- `%18`: `fd_ed25519_affine_is_small_order( A )`
  obtain ⟨s₇, hrun₁₈, heq₁₈⟩ :=
      fd_ed25519_affine_is_small_order_conforms' Ap s₆ hAp₆ hm₆ hZA hcA hAzero hAY
  peel_call hrun₁₈

  -- the stepper counts from the entry's depth, MLIR from `%19`
  denote_number_from 19
  denote_step_reduce v 19 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', hv2]
  by_cases hlowA : ((readPoint hAp₆).X, (readPoint hAp₆).Y) ∈ lowOrder <;>
    simp [hlowA] at hv19 <;>
    simp only [hv19, BlockCom.denote_term, Terminator.denote_condBr_value, simp_denote,
      simp_sllvm] <;>
    denote_enter_block
  · -- `^bb6(-2)`: `A` has small order
    iterate 2 peel_lifetime
    simp_return
    denote_enter_block
    simp_return
    simp [hv1, FD_ED25519_ERR_SIG, FD_ED25519_ERR_PUBKEY, FD_ED25519_SUCCESS, FD_ED25519_ERR_MSG]
    have hpop := (fb₆.of_equiv heq₁₈).popFrame_equiv hm.wf
    refine ⟨rfl, fun b _ => hpop.live b, hpop.symm, ?_⟩
    simp [hS₁₂]
    refine ⟨fun _ _ => ⟨_, encodes_toAffine decR'⟩, fun A R hA _ => ?_⟩
    obtain ⟨hx, hy⟩ := coords_of_encodes decA hA
    rw [hx, hy]
    exact ⟨fun h => absurd hlowA h, fun h => absurd hlowA h⟩

  -- `^bb4`: `R` at `s₇`, where the first call left `s₆`'s blocks
  have hRp₆ : IsPointPtr (pointOutMem (pointOutMem s₅.mem Ap oX oY oZ oT) Rp pX pY pZ pT) Rp :=
    isPointPtr_pointOutMem hRp₁ pX pY pZ pT
  have hRp₇ : IsPointPtr s₇.mem Rp := isPointPtr_of_equiv (heq₁₈.symm.trans hs₆) hRp₆
  have hRpval : readPoint hRp₇ = readPoint hRp₆ :=
    readPoint_of_live?_eq (live?_of_equiv_mem (heq₁₈.symm.trans hs₆) Rp.id) hRp₆ hRp₇
  have decR₇ : IsDecoding (readPoint hRp₇) (readBuf hr) := by rw [hRpval]; exact decR'
  have hZR : (readPoint hRp₇).Z = 1 := by rw [hRpval]; exact decR.2.1
  have hcR : OnCurve (readPoint hRp₇).x (readPoint hRp₇).y := by rw [hRpval]; exact decR.1
  have hlR₇ := live?_of_equiv_mem (heq₁₈.symm.trans hs₆) Rp.id
  have hRzero : ZeroRep Rp s₇.mem :=
    ZeroRep.of_readLimb? (fun i => readLimb?_of_live?_eq hlR₇ i) bndR.2.2.2.2
  have hRX : BiasBounds (isCoordPtr hRp₇ 0) :=
    carryBias (q := Rp.withOffset ((0 : Fin 4) * (5 * 8))) hlR₇ bndR.1
  have hRY : LimbBounds (isCoordPtr hRp₇ 1) :=
    carryBnd (q := Rp.withOffset ((1 : Fin 4) * (5 * 8))) hlR₇ bndR.2.1

  -- `%20`: `fd_ed25519_affine_is_small_order( R )`
  obtain ⟨s₈, hrun₂₀, heq₂₀⟩ :=
    fd_ed25519_affine_is_small_order_conforms' Rp s₇ hRp₇ (hm₆.of_equiv heq₁₈) hZR hcR hRzero hRY
  peel_call hrun₂₀

  denote_number_from 21
  denote_step_reduce v 21 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', hv2]
  by_cases hlowR : ((readPoint hRp₇).X, (readPoint hRp₇).Y) ∈ lowOrder <;>
    simp [hlowR] at hv21 <;>
    simp only [hv21, BlockCom.denote_term, Terminator.denote_condBr_value, simp_denote,
      simp_sllvm] <;>
    denote_enter_block
  · -- `^bb6(-1)`: `R` has small order
    iterate 2 peel_lifetime
    simp_return
    denote_enter_block
    simp_return
    simp [hv3, FD_ED25519_ERR_SIG, FD_ED25519_ERR_PUBKEY, FD_ED25519_SUCCESS, FD_ED25519_ERR_MSG]
    have hpop := ((fb₆.of_equiv heq₁₈).of_equiv heq₂₀).popFrame_equiv hm.wf
    refine ⟨rfl, fun b _ => hpop.live b, hpop.symm, ?_⟩
    refine ⟨⟨_, encodes_toAffine decA⟩, fun A R hA hR => ?_⟩
    obtain ⟨hx, hy⟩ := coords_of_encodes decA hA
    obtain ⟨hx', hy'⟩ := coords_of_encodes decR₇ hR
    rw [hx, hy, hx', hy']
    exact ⟨hlowA, fun _ => hlowR⟩

  -- `^bb5`: neither has small order
  peel_lifetime

  -- `s₈` is `s₅` off the two points, and `s` below its counter
  have fb₈₅ : ∀ b : BlockId, Ap.id ≠ b → Rp.id ≠ b → s₈.mem.live? b = s₅.mem.live? b :=
    fun b hA hR => (live?_of_equiv_mem (heq₂₀.symm.trans (heq₁₈.symm.trans hs₆)) b).trans
      ((live?_pointOutMem_ne hR).trans (live?_pointOutMem_ne hA))
  have fb₈ : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → s₈.mem.live? b = s.mem.live? b :=
    fun b hb => (fb₈₅ b (hne Ap b hApge hb) (hne Rp b hRpge hb)).trans (fb₅ b hb)
  have hwf₈ : s₈.WF := (hwf₆.of_equiv heq₁₈).of_equiv heq₂₀
  have hkpblk₈ : s₈.mem.live? kp.id = s₃.mem.live? kp.id := by
    have fbkp : FrameBelow s₃.alloc.nextFreeBlock s₃ s₄ :=
      hs₄def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
    rw [fb₈₅ _ (by rw [hApdef, hkpdef]; simp [hctr₁, hctr₂]; omega)
        (by rw [hRpdef, hkpdef]; simp [hctr₂]),
      ← heq₁₂.live, fbkp _ (by rw [hkpdef]; simp only; omega)]
  have hkp₈ : Fits s₈.mem kp (64 * 8) := fits_of_live?_eq hkpblk₈ hkpfits

  -- `%22`: `fd_sha512_init( sha )`
  have hsha₈ : IsSha512Ptr s₈.mem sha := fits_of_live?_eq (fb₈ _ (hlt hsha)) hsha
  obtain ⟨s₉, hrun₂₂, heq₂₂⟩ := fd_sha512_init_conforms sha s₈ hwf₈ hsha₈
  peel_call hrun₂₂
  have hwf₉ : s₉.WF := wf_of_equiv_sha512InitMem hwf₈ heq₂₂
  have hblk₉ : s₉.mem.live? sha.id = sha512InitBlock sha.offset (s.mem.live? sha.id) := by
    rw [live?_of_equiv_mem heq₂₂ sha.id, live?_sha512InitMem_self, fb₈ _ (hlt hsha)]
  have fr₉ : ∀ b : BlockId, b ≠ sha.id → s₉.mem.live? b = s₈.mem.live? b :=
    fun b hb => (live?_of_equiv_mem heq₂₂ b).trans (live?_sha512InitMem_ne (Ne.symm hb))
  have hg₉ : s₉.globals = s.globals :=
    heq₂₂.globals.trans (heq₂₀.globals.symm.trans (heq₁₈.globals.symm.trans
      (hs₆.globals.trans (by rw [← heq₁₂.globals, hs₄def, hs₃def, hs₂def, hs₁def]; rfl))))
  have hK₉ : Sha512KHolds s₉ sha :=
    hK.of_live?_eq hm.wf hg₉ fun b hb hb' => (fr₉ b hb).trans (fb₈ b hb')

  -- `%23`: `fd_sha512_append( sha, r, 32 )`
  have hl₉ : s₉.mem.live? sig.id = s.mem.live? sig.id :=
    (fr₉ _ hshasig.symm).trans (fb₈ _ (hlt hr.1))
  have hw₉ : readWord (fits_of_live?_eq hl₉ hr.1) = readBuf hr := readWord_eq_of_live?_eq hl₉ hr.1
  obtain ⟨hret₂₃, -⟩ := hApp sha sig 32#64 s₉ hwf₉
    (by show sig.offset.toNat + 32 ≤ 2 ^ 64; exact hr.2) hshasig hK₉ (fits_of_live?_eq hl₉ hr.1)
  rw [hblk₉, hw₉] at hret₂₃
  obtain ⟨s₁₀, hrun₂₃, hwf₁₀, -, hg₁₀, fr₁₀, hblk₁₀⟩ := hret₂₃ b₁ hb₁
  subst hv5
  peel_call hrun₂₃
  have hK₁₀ : Sha512KHolds s₁₀ sha :=
    hK.of_live?_eq hm.wf (hg₁₀.trans hg₉) fun b hb hb' => (fr₁₀ b hb).trans ((fr₉ b hb).trans (fb₈ b hb'))

  -- `%24`: `fd_sha512_append( sha, public_key, 32 )`
  have hl₁₀ : s₁₀.mem.live? pk.id = s.mem.live? pk.id :=
    (fr₁₀ _ hshapk.symm).trans ((fr₉ _ hshapk.symm).trans (fb₈ _ (hlt ha.1)))
  have hw₁₀ : readWord (fits_of_live?_eq hl₁₀ ha.1) = readBuf ha :=
    readWord_eq_of_live?_eq hl₁₀ ha.1
  obtain ⟨hret₂₄, -⟩ := hApp sha pk 32#64 s₁₀ hwf₁₀
    (by show pk.offset.toNat + 32 ≤ 2 ^ 64; exact ha.2) hshapk hK₁₀ (fits_of_live?_eq hl₁₀ ha.1)
  rw [hblk₁₀, hw₁₀] at hret₂₄
  obtain ⟨s₁₁, hrun₂₄, hwf₁₁, -, hg₁₁, fr₁₁, hblk₁₁⟩ := hret₂₄ b₂ hb₂
  peel_call hrun₂₄
  have hK₁₁ : Sha512KHolds s₁₁ sha :=
    hK.of_live?_eq hm.wf (hg₁₁.trans (hg₁₀.trans hg₉)) fun b hb hb' =>
      (fr₁₁ b hb).trans ((fr₁₀ b hb).trans ((fr₉ b hb).trans (fb₈ b hb')))

  -- `%25`: `fd_sha512_append( sha, msg, msg_sz )`
  have hl₁₁ : s₁₁.mem.live? msg.id = s.mem.live? msg.id :=
    (fr₁₁ _ hshamsg.symm).trans ((fr₁₀ _ hshamsg.symm).trans
      ((fr₉ _ hshamsg.symm).trans (fb₈ _ (hlt hmsg))))
  have hw₁₁ : readWord (fits_of_live?_eq hl₁₁ hmsg) = readWord hmsg :=
    readWord_eq_of_live?_eq hl₁₁ hmsg
  obtain ⟨hret₂₅, -⟩ := hApp sha msg sz s₁₁ hwf₁₁ hmsgoff hshamsg hK₁₁
    (fits_of_live?_eq hl₁₁ hmsg)
  rw [hblk₁₁, hw₁₁] at hret₂₅
  obtain ⟨s₁₂, hrun₂₅, hwf₁₂, -, hg₁₂, fr₁₂, hblk₁₂⟩ := hret₂₅ b₃ hb₃
  peel_call hrun₂₅
  have hK₁₂ : Sha512KHolds s₁₂ sha :=
    hK.of_live?_eq hm.wf (hg₁₂.trans (hg₁₁.trans (hg₁₀.trans hg₉))) fun b hb hb' =>
      (fr₁₂ b hb).trans ((fr₁₁ b hb).trans ((fr₁₀ b hb).trans ((fr₉ b hb).trans (fb₈ b hb'))))

  -- `%26`: `fd_sha512_fini( sha, k )`
  have hkpsha : sha.id ≠ kp.id :=
    (hne kp sha.id (by rw [hkpdef]; simp only; omega) (hlt hsha)).symm
  have hkpblk₁₂ : s₁₂.mem.live? kp.id = some { length := 64, bytes := 0#_ } := by
    rw [fr₁₂ _ hkpsha.symm, fr₁₁ _ hkpsha.symm, fr₁₀ _ hkpsha.symm, fr₉ _ hkpsha.symm, hkpblk₈,
      hs₃def, hkpdef]
    exact live?_afterAlloca_self s₂ (64 * 8)
  obtain ⟨hret₂₆, -⟩ := hFini sha kp s₁₂ hwf₁₂ (fits_of_live?_eq
      ((fr₁₂ _ hkpsha.symm).trans ((fr₁₁ _ hkpsha.symm).trans
        ((fr₁₀ _ hkpsha.symm).trans (fr₉ _ hkpsha.symm)))) hkp₈)
      (by rw [hkpoff]; simp) hkpsha hK₁₂
  rw [hblk₁₂, hkpblk₁₂, hkpoff] at hret₂₆
  obtain ⟨s₁₃, hrun₂₆, hwf₁₃, -, hg₁₃, fr₁₃, hk⟩ := hret₂₆ dig hfin
  peel_call hrun₂₆

  -- `k` holds the digest
  obtain ⟨hk₁₃, hkval⟩ := hk

  -- `%27`: `fd_curve25519_scalar_reduce( k, k )`
  have hkbuf₁₃ : IsByteBufPtr s₁₃.mem kp := ⟨Fits.mono hk₁₃ (by decide), by rw [hkpoff]; simp⟩
  obtain ⟨hret₂₇, -⟩ := hf kp kp s₁₃ hwf₁₃ hkbuf₁₃ (by rw [hkpoff]; simp) hk₁₃
  obtain ⟨s₁₄, hrun₂₇, heq₂₇⟩ := hret₂₇ w (by rw [hkval]; exact hw)
  peel_call hrun₂₇

  peel_lifetime

  -- `%28`: `fd_ed25519_point_neg( Aprime, Aprime )`
  -- `Aprime` at `s₁₄` is as `frombytes_2x` left it: since then only `sha` and `k` were written
  have hwf₁₄ : s₁₄.WF := wf_of_equiv_scalarOutMem hwf₁₃ heq₂₇
  have hkpAp : kp.id ≠ Ap.id := by rw [hkpdef, hApdef]; simp only [ne_eq, BlockId.mk.injEq]; omega
  have hshaAp : sha.id ≠ Ap.id := (hne Ap sha.id hApge (hlt hsha)).symm
  have fr₁₄ : ∀ b : BlockId, kp.id ≠ b → s₁₄.mem.live? b = s₁₃.mem.live? b :=
    fun b hb => (live?_of_equiv_mem heq₂₇ b).trans (live?_scalarOutMem_ne hb)
  have hlA : s₁₄.mem.live? Ap.id = (pointOutMem s₅.mem Ap oX oY oZ oT).live? Ap.id :=
    (fr₁₄ _ hkpAp).trans ((fr₁₃ _ (not_or.mpr ⟨hshaAp.symm, hkpAp.symm⟩)).trans
      ((fr₁₂ _ hshaAp.symm).trans ((fr₁₁ _ hshaAp.symm).trans ((fr₁₀ _ hshaAp.symm).trans
        ((fr₉ _ hshaAp.symm).trans ((heq₁₈.trans heq₂₀).live Ap.id).symm)))))
      |>.trans ((live?_of_equiv_mem hs₆ Ap.id).trans (live?_pointOutMem_ne hRpAp))
  have hAp₁₄ : IsPointPtr s₁₄.mem Ap := isPointPtr_of_live?_eq hlA hAp₁
  obtain ⟨s₁₅, hrun₂₈, nX, nY, nZ, nT, heq₂₈, hnval, hnX, hnT, hnY, hnZ⟩ :=
    fd_ed25519_point_neg_self_conforms Ap s₁₄ hwf₁₄ hAp₁₄
      (carryBias (q := Ap.withOffset ((0 : Fin 4) * (5 * 8))) hlA bndA.1)
      (fun i => (carryBnd (q := Ap.withOffset ((2 : Fin 4) * (5 * 8))) hlA bndA.2.2.1 i).trans
        (tight_le_biasLimb i))
  peel_call hrun₂₈

  -- `%29`: `fd_ed25519_double_scalar_mul_base( Rcmp, k, Aprime, S )`
  have hpt₁₅ : IsPointPtr ((((s₁₄.mem.splice Ap nX).splice (Ap.withOffset 40) nY).splice
      (Ap.withOffset 120) nZ).splice (Ap.withOffset 80) nT) Ap :=
    isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hAp₁₄)))
  have fr₁₅ : ∀ b : BlockId, Ap.id ≠ b → s₁₅.mem.live? b = s₁₄.mem.live? b := fun b hb =>
    (live?_of_equiv_mem heq₂₈.symm b).trans ((live?_splice_ne (p := Ap.withOffset 80) hb).trans
      ((live?_splice_ne (p := Ap.withOffset 120) hb).trans
        ((live?_splice_ne (p := Ap.withOffset 40) hb).trans (live?_splice_ne (p := Ap) hb))))
  have fl₁₅ : ∀ b : BlockId, sha.id ≠ b → kp.id ≠ b → Ap.id ≠ b → Rp.id ≠ b →
      s₁₅.mem.live? b = s₅.mem.live? b := fun b hs hk hA hR =>
    (fr₁₅ b hA).trans ((fr₁₄ b hk).trans ((fr₁₃ b (not_or.mpr ⟨hs.symm, hk.symm⟩)).trans
      ((fr₁₂ b hs.symm).trans ((fr₁₁ b hs.symm).trans ((fr₁₀ b hs.symm).trans
        ((fr₉ b hs.symm).trans (fb₈₅ b hA hR)))))))
  have hkpge : s.alloc.nextFreeBlock ≤ kp.id.id := by rw [hkpdef]; simp only; omega
  have hRcge : s.alloc.nextFreeBlock ≤ Rc.id.id := by rw [hRcdef]; simp only; omega
  have hwf₁₅ : s₁₅.WF := fun q hq => (live?_of_equiv_mem heq₂₈.symm q).trans
    (live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none
      (hwf₁₄ q (by rw [← heq₂₈.alloc] at hq; exact hq))))))
  have hg₁₅ : s₁₅.globals = s.globals :=
    heq₂₈.globals.symm.trans (heq₂₇.globals.trans (hg₁₃.trans (hg₁₂.trans (hg₁₁.trans
      (hg₁₀.trans hg₉)))))
  have hlive₁₅ : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → b ≠ sha.id →
      s₁₅.mem.live? b = s.mem.live? b := fun b hb hs =>
    (fl₁₅ b hs.symm (hne kp b hkpge hb) (hne Ap b hApge hb) (hne Rp b hRpge hb)).trans (fb₅ b hb)
  have hm₁₅ : s₁₅.RefWF [Rc] :=
    DoubleScalarMulBase.refWF_widen hm hwf₁₅ hg₁₅
      (fun b hb hs => hlive₁₅ b hb (hs sha (List.mem_singleton_self _)))
      (fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact .inl hRcge)
  have hRc₁₅ : IsPointPtr s₁₅.mem Rc :=
    isPointPtr_of_live?_eq ((fl₁₅ _ (hne Rc sha.id hRcge (hlt hsha)).symm
        (by rw [hkpdef, hRcdef]; simp only [ne_eq, BlockId.mk.injEq]; omega)
        (by rw [hApdef, hRcdef]; simp only [ne_eq, BlockId.mk.injEq]; omega)
        (by rw [hRpdef, hRcdef]; simp only [ne_eq, BlockId.mk.injEq]; omega)).trans
      (heq₁₂.live Rc.id).symm) ⟨hRcfits, by rw [hRcoff]; simp⟩
  have hAp₁₅ : IsPointPtr s₁₅.mem Ap := isPointPtr_of_live?_eq (live?_of_equiv_mem heq₂₈.symm Ap.id) hpt₁₅
  have hkbuf₁₅ : IsByteBufPtr s₁₅.mem kp :=
    isByteBufPtr_of_live?_eq ((fr₁₅ _ hkpAp.symm).trans (live?_of_equiv_mem heq₂₇ kp.id))
      (by unfold scalarOutMem; exact isByteBufPtr_splice (isByteBufPtr_splice
        (isByteBufPtr_splice (isByteBufPtr_splice hkbuf₁₃))))
  have hS₁₅ : IsByteBufPtr s₁₅.mem (sig.withOffset 32) :=
    isByteBufPtr_of_live?_eq (hlive₁₅ _ (hlt hS.1) hshasig.symm) hS
  have hTbl₁₅ : BaseTableHolds s₁₅ Bt := by
    obtain ⟨qt, hsz, hqt⟩ := hm.gtbl
    refine hTbl.of_live?_eq hg₁₅ fun q hq => ?_
    obtain rfl : q = qt := Option.some.inj (hq.symm.trans hsz.addr)
    exact hlive₁₅ _ (hsz.below hm.wf) (hqt sha (List.mem_singleton_self _))
  -- `-A` at `s₁₅`: well formed at `Z = 1`, `Y`/`Z` copied, `T` at the bias bound
  have hlN : s₁₅.mem.live? Ap.id = _ := live?_of_equiv_mem heq₂₈.symm Ap.id
  have hwfA : (readPoint hAp₁).WellFormed := by
    have hz : (readPoint hAp₁).Z = 1 := decodes.2.1
    refine ⟨hz ▸ isUnit_one, decodes.1, ?_⟩
    have ht := decodes.2.2.2.1
    simp only [Point.x, Point.y, hz, inv_one, mul_one, div_one] at ht
    rw [hz, mul_one, ht]
  have hNval : readPoint hAp₁₅ = (readPoint hAp₁).neg := by
    rw [readPoint_of_live?_eq hlN hpt₁₅ hAp₁₅, hnval, readPoint_of_live?_eq hlA hAp₁ hAp₁₄]
  have bY : LimbBounds (isCoordPtr hAp₁₅ 1) :=
    carryBnd (q := Ap.withOffset ((1 : Fin 4) * (5 * 8))) hlN (hq := isCoordPtr hpt₁₅ 1)
      fun i => (hnY i).trans_le (carryBnd (q := Ap.withOffset ((1 : Fin 4) * (5 * 8))) hlA
        (hq := isCoordPtr hAp₁ 1) bndA.2.1 i)
  have bZ : LimbBounds.Loose (isCoordPtr hAp₁₅ 3) :=
    carryBnd (q := Ap.withOffset ((3 : Fin 4) * (5 * 8))) hlN (hq := isCoordPtr hpt₁₅ 3)
      fun i => (hnZ i).trans_le ((carryBnd (q := Ap.withOffset ((3 : Fin 4) * (5 * 8))) hlA
        (hq := isCoordPtr hAp₁ 3) bndA.2.2.2.1).loose i)
  have bT : LimbBounds.Loose (isCoordPtr hAp₁₅ 2) :=
    carryBnd (q := Ap.withOffset ((2 : Fin 4) * (5 * 8))) hlN (hq := isCoordPtr hpt₁₅ 2)
      fun i => le_trans (hnT i) (le_trans (biasLimb_le i) (by norm_num))
  have hwfN : (readPoint hAp₁₅).WellFormed := by rw [hNval]; exact Point.wellFormed_neg hwfA
  have hZN : (readPoint hAp₁₅).Z = 1 := by
    have hz : (readPoint hAp₁).Z = 1 := decodes.2.1
    rw [hNval]
    dsimp only [Point.neg]
    exact hz
  obtain ⟨s₁₆, hrun₂₉, rX, rY, rZ, rT, heq₂₉, hrep, hRcbnd⟩ :=
    fd_ed25519_double_scalar_mul_base_conforms Rc kp Ap (sig.withOffset 32) s₁₅ hm₁₅ hRc₁₅ hAp₁₅
      hkbuf₁₅ hS₁₅
      (carryBias (q := Ap.withOffset ((0 : Fin 4) * (5 * 8))) hlN hnX) bY bZ bT hRc₁₅ hAp₁₅ hkbuf₁₅ hS₁₅ hwfN hZN Bt hTbl₁₅ hB
  peel_call hrun₂₉

  -- `%30`: `fd_ed25519_point_eq_z1( Rcmp, R )`
  have hRcRp : Rc.id ≠ Rp.id := by
    rw [hRcdef, hRpdef]; simp only [ne_eq, BlockId.mk.injEq]; omega
  have hkpRp : kp.id ≠ Rp.id := by
    rw [hkpdef, hRpdef]; simp only [ne_eq, BlockId.mk.injEq]; omega
  have hRpsha : sha.id ≠ Rp.id := (hne Rp sha.id hRpge (hlt hsha)).symm
  have hpt₁₆ : IsPointPtr ((((s₁₅.mem.splice Rc rX).splice (Rc.withOffset 40) rY).splice
      (Rc.withOffset 120) rZ).splice (Rc.withOffset 80) rT) Rc :=
    isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hRc₁₅)))
  have hlRc : s₁₆.mem.live? Rc.id = _ := live?_of_equiv_mem heq₂₉.symm Rc.id
  have hRc₁₆ : IsPointPtr s₁₆.mem Rc := isPointPtr_of_live?_eq hlRc hpt₁₆
  have hwf₁₆ : s₁₆.WF := fun q hq => (live?_of_equiv_mem heq₂₉.symm q).trans
    (live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none
      (hwf₁₅ q (by rw [← heq₂₉.alloc] at hq; exact hq))))))
  -- `R` at `s₁₆` is as `s₇` read it: nothing since wrote its block
  have hlR : s₁₆.mem.live? Rp.id = s₇.mem.live? Rp.id :=
    (live?_of_equiv_mem heq₂₉.symm Rp.id).trans ((live?_splice_ne (p := Rc.withOffset 80) hRcRp).trans
      ((live?_splice_ne (p := Rc.withOffset 120) hRcRp).trans
      ((live?_splice_ne (p := Rc.withOffset 40) hRcRp).trans
      ((live?_splice_ne (p := Rc) hRcRp).trans ((fr₁₅ _ hRpAp.symm).trans ((fr₁₄ _ hkpRp).trans
      ((fr₁₃ _ (not_or.mpr ⟨hRpsha.symm, hkpRp.symm⟩)).trans ((fr₁₂ _ hRpsha.symm).trans
      ((fr₁₁ _ hRpsha.symm).trans ((fr₁₀ _ hRpsha.symm).trans ((fr₉ _ hRpsha.symm).trans
        (heq₂₀.live Rp.id).symm)))))))))))
  have hRp₁₆ : IsPointPtr s₁₆.mem Rp := isPointPtr_of_live?_eq hlR hRp₇
  have hZR₁₆ : (readPoint hRp₁₆).Z = 1 := by
    rw [readPoint_of_live?_eq hlR hRp₇ hRp₁₆]; exact hZR
  have hRX₁₆ : BiasBounds (isCoordPtr hRp₁₆ 0) :=
    carryBias (q := Rp.withOffset ((0 : Fin 4) * (5 * 8))) hlR (hq := isCoordPtr hRp₇ 0) hRX
  have hRY₁₆ : LimbBounds (isCoordPtr hRp₁₆ 1) :=
    carryBnd (q := Rp.withOffset ((1 : Fin 4) * (5 * 8))) hlR (hq := isCoordPtr hRp₇ 1) hRY
  have hRcbnd₁₆ : AllLimbBounds hRc₁₆ := fun i =>
    carryBnd (q := Rc.withOffset (i * (5 * 8))) hlRc (hq := isCoordPtr hpt₁₆ i) (hRcbnd i)
  have hRcZ : IsUnit (readPoint hRc₁₆).Z := by
    rw [readPoint_of_live?_eq hlRc hpt₁₆ hRc₁₆]; exact hrep.isUnit_Z
  obtain ⟨s₁₇, hrun₃₀, heq₃₀⟩ :=
    fd_ed25519_point_eq_z1_conforms' Rc Rp s₁₆ hwf₁₆ hRc₁₆ hRp₁₆ hRcbnd₁₆ hRX₁₆ hRY₁₆ hRcZ hZR₁₆
  peel_call hrun₃₀

  denote_step_reduce v 30 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.select, hv2] fold
  replace hv30 : v30 = if (readPoint hRc₁₆).SamePoint (readPoint hRp₁₆) then .value 0#32 else v0 := by
    rw [hv30]
    by_cases h : (readPoint hRc₁₆).SamePoint (readPoint hRp₁₆) <;> simp [h]

  iterate 2 peel_lifetime
  simp_return
  denote_enter_block
  iterate 2 peel_lifetime
  simp_return
  denote_enter_block
  simp_return
  simp [hv30]

  -- the final state agrees with `s` off `sha`
  have hlive₁₇ : ∀ b : BlockId, ¬b = sha.id → (s.popFrame s₁₇.mem).mem.live? b = s.mem.live? b :=
    fun b hb => by
      show (s₁₇.mem.killFrom s.alloc.nextFreeBlock).live? b = _
      by_cases hb' : b.id < s.alloc.nextFreeBlock
      · have hRcb : Rc.id ≠ b := hne Rc b hRcge hb'
        rw [live?_killFrom_of_lt hb', ← heq₃₀.live b, live?_of_equiv_mem heq₂₉.symm b,
          live?_splice_ne (p := Rc.withOffset 80) hRcb, live?_splice_ne (p := Rc.withOffset 120) hRcb,
          live?_splice_ne (p := Rc.withOffset 40) hRcb, live?_splice_ne (p := Rc) hRcb,
          hlive₁₅ b hb' hb]
      · rw [live?_killFrom_of_le (by omega), hm.wf b (by omega)]
  -- `A`, `R` and the equation `Rcmp = R` decides
  have decR₁₆ : IsDecoding (readPoint hRp₁₆) (readBuf hr) := by
    rw [readPoint_of_live?_eq hlR hRp₇ hRp₁₆]; exact decR₇
  have hwfR := wellFormed_of_isDecoding decR₁₆
  have hA : ∀ A, Encodes (readBuf ha) A → A = (readPoint hAp₁).toAffine hwfA := fun A hA =>
    encodes_unique hA (by
      have e := encodes_toAffine decA
      rwa [Point.toAffine_congr hApval (wellFormed_of_isDecoding decA) hwfA] at e)
  have hR : ∀ R, Encodes (readBuf hr) R → R = (readPoint hRp₁₆).toAffine hwfR := fun R hR =>
    encodes_unique hR (encodes_toAffine decR₁₆)
  have hk : readBuf hkbuf₁₅ = packWords w := by
    have e : readBuf hkbuf₁₅ = readBuf (m := scalarOutMem s₁₃.mem kp _) (by
        unfold scalarOutMem
        exact isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice
          (isByteBufPtr_splice hkbuf₁₃)))) :=
      readBuf_of_live?_eq ((fr₁₅ _ hkpAp.symm).trans (live?_of_equiv_mem heq₂₇ kp.id))
    rw [e, readBuf_scalarOutMem hkbuf₁₃]
  have hℓ : groupOrder < 2 ^ 255 := by unfold groupOrder; norm_num
  have hSeq : (readBuf hS₁₅).toNat = (readBuf hS).toNat := by
    rw [readBuf_of_live?_eq (hp := hS) (hlive₁₅ _ (hlt hS.1) hshasig.symm)]
  have heqn : (readPoint hRc₁₆).SamePoint (readPoint hRp₁₆) ↔
      -(((packWords w).toNat % 2 ^ 255) • (readPoint hAp₁).toAffine hwfA)
        + (readBuf hS).toNat • basePoint.toAffine wellFormed_basePoint
        = (readPoint hRp₁₆).toAffine hwfR := by
    have hrep' := hrep
    rw [Point.toAffine_congr hNval hwfN (Point.wellFormed_neg hwfA), Point.toAffine_neg, hk, hSeq,
      Nat.mod_eq_of_lt (hS₁₂.trans hℓ), smul_neg] at hrep'
    rw [readPoint_of_live?_eq hlRc hpt₁₆ hRc₁₆]
    exact samePoint_iff_of_represents hrep' hwfR
  subst hv0
  by_cases hsame : (readPoint hRc₁₆).SamePoint (readPoint hRp₁₆) <;>
    simp only [hsame, if_true, if_false] <;>
    refine ⟨_, rfl, rfl, hlive₁₇, ?_⟩ <;>
    simp [FD_ED25519_SUCCESS, FD_ED25519_ERR_SIG, FD_ED25519_ERR_PUBKEY, FD_ED25519_ERR_MSG, hS₁₂]
  all_goals
    refine ⟨⟨_, encodes_toAffine decA⟩, fun _ _ => ⟨_, encodes_toAffine decR₁₆⟩,
      fun A R hA' hR' => ?_⟩
    obtain ⟨hx, hy⟩ := coords_of_encodes decA hA'
    obtain ⟨hx', hy'⟩ := coords_of_encodes decR₇ hR'
    refine ⟨by rw [hx, hy]; exact hlowA, fun _ => by rw [hx', hy']; exact hlowR, fun _ _ => ?_⟩
    rw [hA A hA', hR R hR']
  · exact heqn.mp hsame
  · exact fun h => hsame (heqn.mpr h)

end Firedancer.Ref
