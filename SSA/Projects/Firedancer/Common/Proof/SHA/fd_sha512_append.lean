/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.SHA.fd_sha512_append
import SSA.Projects.Firedancer.Common.Proof.SHA.Calls

/-!
# `fd_sha512_append` writes only `sha`

A forward walk, one lemma per block, bottom-up. The region computes its
pointers into the hash state in `^bb1` -- `%9 = &sha->state`, `%10 =
&sha->buf_used` -- and the Cfg lift threads them to later blocks as arguments,
so each block lemma takes those arguments explicitly, with what is known of
them: `%9` is a pointer into `sha`, and `%10` and `%26` are into `sha` if they
are pointers at all. Every write goes through one of them or through `sha`
itself; `data` is only ever read, copied from, or compressed.
-/

set_option linter.unusedSimpArgs false  -- the walks share generic lookup sets

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `^bb10`: the return. -/
theorem app_bb10 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (_hsha : ∀ h : fd_sha512_append.Γout[11]? = some SLLVM.Ty.ptr, Vamb ⟨11, h⟩ = .value sha)
     (h10 : fd_sha512_append.sigs[9]? = some [])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨9, h10, .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  refine walk_ret ⟨_, rfl, fun p t h => ?_⟩
  dsimp only at h
  rw [EffectM.run_pure, PoisonOr.value_inj, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact hI

/-- `^bb9`: record `buf_used`, through `%10`. -/
theorem app_bb9 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[11]? = some SLLVM.Ty.ptr, Vamb ⟨11, h⟩ = .value sha)
    (a41 : LLVM.IntW 64) (a10 : SLLVM.Ptr) (h10 : ∀ q, a10 = .value q → q.id = sha.id)
    (h9 : fd_sha512_append.sigs[8]? = some [SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨8, h9, a41 ::ₕ a10 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s1 ⟨q, b, hq, hs1⟩ => ?_
  simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
  have hI1 : FrameInv s₀ (· = sha.id) s1 := hs1 ▸ hI.splice (.inl (h10 q hq))
  exact walk_br (app_bb10 Vamb s₀ sha hsha _ _ hI1)

/-- `^bb8`: buffer the leftover bytes, into `sha` itself. -/
theorem app_bb8 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[11]? = some SLLVM.Ty.ptr, Vamb ⟨11, h⟩ = .value sha)
    (a10 a32 : SLLVM.Ptr) (a33 a36 : LLVM.IntW 64) (h10 : ∀ q, a10 = .value q → q.id = sha.id)
    (h8 : fd_sha512_append.sigs[7]? = some [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨7, h8, a10 ::ₕ a32 ::ₕ a33 ::ₕ a36 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 38
  denote_step_all v 39
  refine walk_call_single vacuous_poison (memcpy_call_cases _ _ hI.1) fun x40 s40 ⟨q, hq, hwf, hl⟩ => ?_
  simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
  rw [hsha, PoisonOr.value_inj] at hq
  have hI40 : FrameInv s₀ (· = sha.id) s40 := hI.of_call hwf fun b hb => hl b (hq ▸ hb)
  exact walk_br (app_bb9 Vamb s₀ sha hsha _ _ h10 _ _ hI40)

/-- `^bb7`: anything left over? -/
theorem app_bb7 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[11]? = some SLLVM.Ty.ptr, Vamb ⟨11, h⟩ = .value sha)
    (a10 a32 : SLLVM.Ptr) (a33 : LLVM.IntW 64) (h10 : ∀ q, a10 = .value q → q.id = sha.id)
    (h7 : fd_sha512_append.sigs[6]? = some [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨6, h7, a10 ::ₕ a32 ::ₕ a33 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 36
  denote_step_all v 37
  refine walk_condBr vacuous_poison fun b _ => ?_
  by_cases hb : b = 1
  · simp only [hb, ↓reduceIte]
    exact app_bb10 Vamb s₀ sha hsha _ _ hI
  · simp only [hb, ↓reduceIte]
    exact app_bb8 Vamb s₀ sha hsha _ _ _ _ h10 _ _ hI

/-- `^bb6`: compress the whole blocks straight out of `data`. -/
theorem app_bb6 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[11]? = some SLLVM.Ty.ptr, Vamb ⟨11, h⟩ = .value sha)
    (a9 a10 a32 : SLLVM.Ptr) (a33 : LLVM.IntW 64) (st9 : Pointer) (h9 : a9 = .value st9) (h9id : st9.id = sha.id)
    (h10 : ∀ q, a10 = .value q → q.id = sha.id)
    (h6 : fd_sha512_append.sigs[5]? = some [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨5, h6, a9 ::ₕ a10 ::ₕ a32 ::ₕ a33 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 35
  denote_step_all v 35
  refine walk_call_nil vacuous_poison
    (core_ref_call_cases' _ st9 (by simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero]; exact h9) _ hI.1)
    fun s1 ⟨hwf, hl⟩ => ?_
  have hI1 : FrameInv s₀ (· = sha.id) s1 := hI.of_call hwf fun b hb => hl b fun e => hb (e.trans h9id)
  exact walk_br (app_bb7 Vamb s₀ sha hsha _ _ _ h10 _ _ hI1)

/-- `^bb5`: any whole blocks? -/
theorem app_bb5 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[11]? = some SLLVM.Ty.ptr, Vamb ⟨11, h⟩ = .value sha)
    (a32 : SLLVM.Ptr) (a33 : LLVM.IntW 64) (a9 a10 : SLLVM.Ptr) (st9 : Pointer) (h9 : a9 = .value st9) (h9id : st9.id = sha.id)
    (h10 : ∀ q, a10 = .value q → q.id = sha.id)
    (h5 : fd_sha512_append.sigs[4]? = some [SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.ptr])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨4, h5, a32 ::ₕ a33 ::ₕ a9 ::ₕ a10 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 34
  denote_step_all v 34
  refine walk_condBr vacuous_poison fun b _ => ?_
  by_cases hb : b = 1
  · simp only [hb, ↓reduceIte]
    exact app_bb7 Vamb s₀ sha hsha _ _ _ h10 _ _ hI
  · simp only [hb, ↓reduceIte]
    exact app_bb6 Vamb s₀ sha hsha _ _ _ _ st9 h9 h9id h10 _ _ hI

/-- `^bb4`: fill the buffered block, compress it, clear `buf_used`. -/
theorem app_bb4 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[11]? = some SLLVM.Ty.ptr, Vamb ⟨11, h⟩ = .value sha)
    (a9 a10 : SLLVM.Ptr) (a24 : LLVM.IntW 64) (a26 : SLLVM.Ptr) (st9 : Pointer) (h9 : a9 = .value st9) (h9id : st9.id = sha.id)
    (h10 : ∀ q, a10 = .value q → q.id = sha.id)
    (h26 : ∀ q, a26 = .value q → q.id = sha.id)
    (h4 : fd_sha512_append.sigs[3]? = some [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨3, h4, a9 ::ₕ a10 ::ₕ a24 ::ₕ a26 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 29
  refine walk_call_single vacuous_poison (memcpy_call_cases _ _ hI.1) fun x29 s29 ⟨q, hq, hwf, hl⟩ => ?_
  simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
  have hI29 : FrameInv s₀ (· = sha.id) s29 :=
    hI.of_call hwf fun b hb => hl b fun e => hb (e.trans (h26 q hq))
  denote_step_all v 31
  refine walk_call_nil vacuous_poison
    (core_ref_call_cases' _ st9 (by simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero]; exact h9) _ hI29.1)
    fun s1 ⟨hwf1, hl1⟩ => ?_
  have hI1 : FrameInv s₀ (· = sha.id) s1 :=
    hI29.of_call hwf1 fun b hb => hl1 b fun e => hb (e.trans h9id)
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s2 ⟨q2, b2, hq2, hs2⟩ => ?_
  simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq2
  have hI2 : FrameInv s₀ (· = sha.id) s2 := hs2 ▸ hI1.splice (.inl (h10 q2 hq2))
  exact walk_br (app_bb5 Vamb s₀ sha hsha _ _ _ _ st9 h9 h9id h10 _ _ hI2)

/-- `^bb3`: the append fits in the buffer; copy it in. -/
theorem app_bb3 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[11]? = some SLLVM.Ty.ptr, Vamb ⟨11, h⟩ = .value sha)
    (a10 : SLLVM.Ptr) (a11 : LLVM.IntW 64) (a26 : SLLVM.Ptr) (h10 : ∀ q, a10 = .value q → q.id = sha.id)
    (h26 : ∀ q, a26 = .value q → q.id = sha.id)
    (h3 : fd_sha512_append.sigs[2]? = some [SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨2, h3, a10 ::ₕ a11 ::ₕ a26 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 27
  refine walk_call_single vacuous_poison (memcpy_call_cases _ _ hI.1) fun x27 s27 ⟨q, hq, hwf, hl⟩ => ?_
  simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
  have hI27 : FrameInv s₀ (· = sha.id) s27 :=
    hI.of_call hwf fun b hb => hl b fun e => hb (e.trans (h26 q hq))
  denote_step_all v 28
  exact walk_br (app_bb9 Vamb s₀ sha hsha _ _ h10 _ _ hI27)

/-- `^bb2`: bytes are already buffered. -/
theorem app_bb2 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[11]? = some SLLVM.Ty.ptr, Vamb ⟨11, h⟩ = .value sha)
    (a9 a10 : SLLVM.Ptr) (a11 : LLVM.IntW 64) (st9 : Pointer) (h9 : a9 = .value st9) (h9id : st9.id = sha.id)
    (h10 : ∀ q, a10 = .value q → q.id = sha.id)
    (h2 : fd_sha512_append.sigs[1]? = some [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨1, h2, a9 ::ₕ a10 ::ₕ a11 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 24
  denote_step_all v 26
  denote_eval v 26 26
  have h26 : ∀ q, v26 = .value q → q.id = sha.id := fun q hq =>
    id_of_gep_eq hv26 hq fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hsha, PoisonOr.value_inj] at hp'; rw [← hp']
  refine walk_condBr vacuous_poison fun b _ => ?_
  by_cases hb : b = 1
  · simp only [hb, ↓reduceIte]
    exact app_bb3 Vamb s₀ sha hsha _ _ _ h10 h26 _ _ hI
  · simp only [hb, ↓reduceIte]
    exact app_bb4 Vamb s₀ sha hsha _ _ _ _ st9 h9 h9id h10 h26 _ _ hI

/-- `^bb1`: read the counters, update the bit count, and dispatch. -/
theorem app_bb1 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[11]? = some SLLVM.Ty.ptr, Vamb ⟨11, h⟩ = .value sha)
    (h1 : fd_sha512_append.sigs[0]? = some [])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨0, h1, .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 9
  denote_step_all v 10
  denote_eval v 9 10
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x11 s11 hs11 => ?_
  have hI11 : FrameInv s₀ (· = sha.id) s11 := hs11 ▸ hI
  denote_step_all v 12
  denote_eval v 12 12
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x13 s13 hs13 => ?_
  have hI13 : FrameInv s₀ (· = sha.id) s13 := hs13 ▸ hI11
  denote_step_all v 14
  denote_eval v 14 14
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x15 s15 hs15 => ?_
  have hI15 : FrameInv s₀ (· = sha.id) s15 := hs15 ▸ hI13
  denote_step_all v 22
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun sa ⟨qa, ba, hqa, hsa⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hqa
  have hIa : FrameInv s₀ (· = sha.id) sa :=
    hsa ▸ hI15.splice (.inl (id_of_gepConst_eq hv12 hqa fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hsha, PoisonOr.value_inj] at hp'; rw [← hp']))
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun sb ⟨qb, bb, hqb, hsb⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hqb
  have hIb : FrameInv s₀ (· = sha.id) sb :=
    hsb ▸ hIa.splice (.inl (id_of_gepConst_eq hv14 hqb fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hsha, PoisonOr.value_inj] at hp'; rw [← hp']))
  denote_step_all v 23
  have h9 : v9 = .value (sha.withOffset (BitVec.ofNat 64 128)) := by
    rw [hv9]; simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero]; rw [hsha]; exact gepConst_value sha 128
  have h10 : ∀ q, v10 = .value q → q.id = sha.id := fun q hq =>
    id_of_gepConst_eq hv10 hq fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hsha, PoisonOr.value_inj] at hp'; rw [← hp']
  refine walk_condBr vacuous_poison fun b _ => ?_
  by_cases hb : b = 1
  · simp only [hb, ↓reduceIte]
    exact app_bb5 Vamb s₀ sha hsha _ _ _ _ _ h9 rfl h10 _ _ hIb
  · simp only [hb, ↓reduceIte]
    exact app_bb2 Vamb s₀ sha hsha _ _ _ _ h9 rfl h10 _ _ hIb

set_option maxHeartbeats 4000000 in
theorem fd_sha512_append_frame (sha : Pointer) (data : SLLVM.Ptr) (sz : LLVM.IntW 64)
    (s : GlobalState) (hs : s.WF) : fd_sha512_append_frame_spec sha data sz s := by
  simp only [fd_sha512_append_frame_spec, Cfg.denote]
  refine runFunction_frameInv (W := (· = sha.id)) hs ?_
  denote_step_all v 8
  refine walk_condBr vacuous_poison fun b _ => ?_
  by_cases hb : b = 1
  · simp only [hb, ↓reduceIte]
    exact app_bb10 _ s sha (fun _ => rfl) _ _ (FrameInv.refl hs _)
  · simp only [hb, ↓reduceIte]
    exact app_bb1 _ s sha (fun _ => rfl) _ _ (FrameInv.refl hs _)

end Firedancer.Common
