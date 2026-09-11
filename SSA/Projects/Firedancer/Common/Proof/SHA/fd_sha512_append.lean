/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.SHA.fd_sha512_append
import SSA.Projects.Firedancer.Common.Proof.SHA.Calls

/-!
# `fd_sha512_append` writes only `sha`

A forward walk, one lemma per block, bottom-up. The region computes its
pointers into the hash state in `^bb1` -- `%13 = &sha->state`, `%14 =
&sha->buf_used` -- and the Cfg lift threads them to later blocks as arguments,
so each block lemma takes those arguments explicitly, with what is known of
them: `%13` is a pointer into `sha`, and `%14` and `%30` are into `sha` if they
are pointers at all. Every write goes through one of them or through `sha`
itself; `data` is only ever read, copied from, or compressed.
-/

set_option linter.unusedSimpArgs false  -- the walks share generic lookup sets

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `^bb10`: the return. -/
theorem app_bb10 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (_hsha : ∀ h : fd_sha512_append.Γout[15]? = some SLLVM.Ty.ptr, Vamb ⟨15, h⟩ = .value sha)
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

/-- `^bb9`: record `buf_used`, through `%14`. -/
theorem app_bb9 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[15]? = some SLLVM.Ty.ptr, Vamb ⟨15, h⟩ = .value sha)
    (a45 : LLVM.IntW 64) (a14 : SLLVM.Ptr) (h14 : ∀ q, a14 = .value q → q.id = sha.id)
    (h9 : fd_sha512_append.sigs[8]? = some [SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨8, h9, a45 ::ₕ a14 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s1 ⟨q, b, hq, hs1⟩ => ?_
  simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
  have hI1 : FrameInv s₀ (· = sha.id) s1 := hs1 ▸ hI.splice (.inl (h14 q hq))
  exact walk_br (app_bb10 Vamb s₀ sha hsha _ _ hI1)

/-- `^bb8`: buffer the leftover bytes, into `sha` itself. -/
theorem app_bb8 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[15]? = some SLLVM.Ty.ptr, Vamb ⟨15, h⟩ = .value sha)
    (a14 a36 : SLLVM.Ptr) (a37 a40 : LLVM.IntW 64) (h14 : ∀ q, a14 = .value q → q.id = sha.id)
    (h8 : fd_sha512_append.sigs[7]? = some [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨7, h8, a14 ::ₕ a36 ::ₕ a37 ::ₕ a40 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 42
  denote_step_all v 43
  refine walk_call_single vacuous_poison (memcpy_call_cases _ _ hI.1) fun x44 s44 ⟨q, hq, hwf, hl⟩ => ?_
  simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
  rw [hsha, PoisonOr.value_inj] at hq
  have hI44 : FrameInv s₀ (· = sha.id) s44 := hI.of_call hwf fun b hb => hl b (hq ▸ hb)
  exact walk_br (app_bb9 Vamb s₀ sha hsha _ _ h14 _ _ hI44)

/-- `^bb7`: anything left over? -/
theorem app_bb7 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[15]? = some SLLVM.Ty.ptr, Vamb ⟨15, h⟩ = .value sha)
    (a14 a36 : SLLVM.Ptr) (a37 : LLVM.IntW 64) (h14 : ∀ q, a14 = .value q → q.id = sha.id)
    (h7 : fd_sha512_append.sigs[6]? = some [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨6, h7, a14 ::ₕ a36 ::ₕ a37 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 40
  denote_step_all v 41
  refine walk_condBr vacuous_poison fun b _ => ?_
  by_cases hb : b = 1
  · simp only [hb, ↓reduceIte]
    exact app_bb10 Vamb s₀ sha hsha _ _ hI
  · simp only [hb, ↓reduceIte]
    exact app_bb8 Vamb s₀ sha hsha _ _ _ _ h14 _ _ hI

/-- `^bb6`: compress the whole blocks straight out of `data`. -/
theorem app_bb6 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[15]? = some SLLVM.Ty.ptr, Vamb ⟨15, h⟩ = .value sha)
    (a13 a14 a36 : SLLVM.Ptr) (a37 : LLVM.IntW 64) (st13 : Pointer) (h13 : a13 = .value st13) (h13id : st13.id = sha.id)
    (h14 : ∀ q, a14 = .value q → q.id = sha.id)
    (h6 : fd_sha512_append.sigs[5]? = some [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨5, h6, a13 ::ₕ a14 ::ₕ a36 ::ₕ a37 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 39
  denote_step_all v 39
  refine walk_call_nil vacuous_poison
    (core_ref_call_cases' _ st13 (by simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero]; exact h13) _ hI.1)
    fun s1 ⟨hwf, hl⟩ => ?_
  have hI1 : FrameInv s₀ (· = sha.id) s1 := hI.of_call hwf fun b hb => hl b fun e => hb (e.trans h13id)
  exact walk_br (app_bb7 Vamb s₀ sha hsha _ _ _ h14 _ _ hI1)

/-- `^bb5`: any whole blocks? -/
theorem app_bb5 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[15]? = some SLLVM.Ty.ptr, Vamb ⟨15, h⟩ = .value sha)
    (a36 : SLLVM.Ptr) (a37 : LLVM.IntW 64) (a13 a14 : SLLVM.Ptr) (st13 : Pointer) (h13 : a13 = .value st13) (h13id : st13.id = sha.id)
    (h14 : ∀ q, a14 = .value q → q.id = sha.id)
    (h5 : fd_sha512_append.sigs[4]? = some [SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.ptr])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨4, h5, a36 ::ₕ a37 ::ₕ a13 ::ₕ a14 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 38
  denote_step_all v 38
  refine walk_condBr vacuous_poison fun b _ => ?_
  by_cases hb : b = 1
  · simp only [hb, ↓reduceIte]
    exact app_bb7 Vamb s₀ sha hsha _ _ _ h14 _ _ hI
  · simp only [hb, ↓reduceIte]
    exact app_bb6 Vamb s₀ sha hsha _ _ _ _ st13 h13 h13id h14 _ _ hI

/-- `^bb4`: fill the buffered block, compress it, clear `buf_used`. -/
theorem app_bb4 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[15]? = some SLLVM.Ty.ptr, Vamb ⟨15, h⟩ = .value sha)
    (a13 a14 : SLLVM.Ptr) (a28 : LLVM.IntW 64) (a30 : SLLVM.Ptr) (st13 : Pointer) (h13 : a13 = .value st13) (h13id : st13.id = sha.id)
    (h14 : ∀ q, a14 = .value q → q.id = sha.id)
    (h30 : ∀ q, a30 = .value q → q.id = sha.id)
    (h4 : fd_sha512_append.sigs[3]? = some [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨3, h4, a13 ::ₕ a14 ::ₕ a28 ::ₕ a30 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 33
  refine walk_call_single vacuous_poison (memcpy_call_cases _ _ hI.1) fun x33 s33 ⟨q, hq, hwf, hl⟩ => ?_
  simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
  have hI33 : FrameInv s₀ (· = sha.id) s33 :=
    hI.of_call hwf fun b hb => hl b fun e => hb (e.trans (h30 q hq))
  denote_step_all v 35
  refine walk_call_nil vacuous_poison
    (core_ref_call_cases' _ st13 (by simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero]; exact h13) _ hI33.1)
    fun s1 ⟨hwf1, hl1⟩ => ?_
  have hI1 : FrameInv s₀ (· = sha.id) s1 :=
    hI33.of_call hwf1 fun b hb => hl1 b fun e => hb (e.trans h13id)
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s2 ⟨q2, b2, hq2, hs2⟩ => ?_
  simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq2
  have hI2 : FrameInv s₀ (· = sha.id) s2 := hs2 ▸ hI1.splice (.inl (h14 q2 hq2))
  exact walk_br (app_bb5 Vamb s₀ sha hsha _ _ _ _ st13 h13 h13id h14 _ _ hI2)

/-- `^bb3`: the append fits in the buffer; copy it in. -/
theorem app_bb3 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[15]? = some SLLVM.Ty.ptr, Vamb ⟨15, h⟩ = .value sha)
    (a14 : SLLVM.Ptr) (a15 : LLVM.IntW 64) (a30 : SLLVM.Ptr) (h14 : ∀ q, a14 = .value q → q.id = sha.id)
    (h30 : ∀ q, a30 = .value q → q.id = sha.id)
    (h3 : fd_sha512_append.sigs[2]? = some [SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨2, h3, a14 ::ₕ a15 ::ₕ a30 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 31
  refine walk_call_single vacuous_poison (memcpy_call_cases _ _ hI.1) fun x31 s31 ⟨q, hq, hwf, hl⟩ => ?_
  simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
  have hI31 : FrameInv s₀ (· = sha.id) s31 :=
    hI.of_call hwf fun b hb => hl b fun e => hb (e.trans (h30 q hq))
  denote_step_all v 32
  exact walk_br (app_bb9 Vamb s₀ sha hsha _ _ h14 _ _ hI31)

/-- `^bb2`: bytes are already buffered. -/
theorem app_bb2 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[15]? = some SLLVM.Ty.ptr, Vamb ⟨15, h⟩ = .value sha)
    (a13 a14 : SLLVM.Ptr) (a15 : LLVM.IntW 64) (st13 : Pointer) (h13 : a13 = .value st13) (h13id : st13.id = sha.id)
    (h14 : ∀ q, a14 = .value q → q.id = sha.id)
    (h2 : fd_sha512_append.sigs[1]? = some [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨1, h2, a13 ::ₕ a14 ::ₕ a15 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 28
  denote_step_all v 30
  denote_eval v 30 30
  have h30 : ∀ q, v30 = .value q → q.id = sha.id := fun q hq =>
    id_of_gep_eq hv30 hq fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hsha, PoisonOr.value_inj] at hp'; rw [← hp']
  refine walk_condBr vacuous_poison fun b _ => ?_
  by_cases hb : b = 1
  · simp only [hb, ↓reduceIte]
    exact app_bb3 Vamb s₀ sha hsha _ _ _ h14 h30 _ _ hI
  · simp only [hb, ↓reduceIte]
    exact app_bb4 Vamb s₀ sha hsha _ _ _ _ st13 h13 h13id h14 h30 _ _ hI

/-- `^bb1`: read the counters, update the bit count, and dispatch. -/
theorem app_bb1 (Vamb : fd_sha512_append.Γout.Valuation) (s₀ : GlobalState) (sha : Pointer)
    (hsha : ∀ h : fd_sha512_append.Γout[15]? = some SLLVM.Ty.ptr, Vamb ⟨15, h⟩ = .value sha)
    (hzero : ∀ h : fd_sha512_append.Γout[12]? = some (SLLVM.Ty.bitvec 64), Vamb ⟨12, h⟩ = .value 0#64)
    (h1 : fd_sha512_append.sigs[0]? = some [])
    (s : GlobalState) (hI : FrameInv s₀ (· = sha.id) s) :
    ∃ res, StateT.run (fd_sha512_append.blocks.run Vamb ⟨0, h1, .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (· = sha.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 13
  denote_step_all v 14
  denote_eval v 13 14
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x15 s15 hs15 => ?_
  have hI15 : FrameInv s₀ (· = sha.id) s15 := hs15 ▸ hI
  denote_step_all v 16
  denote_eval v 16 16
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x17 s17 hs17 => ?_
  have hI17 : FrameInv s₀ (· = sha.id) s17 := hs17 ▸ hI15
  denote_step_all v 18
  denote_eval v 18 18
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x19 s19 hs19 => ?_
  have hI19 : FrameInv s₀ (· = sha.id) s19 := hs19 ▸ hI17
  denote_step_all v 26
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun sa ⟨qa, ba, hqa, hsa⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hqa
  have hIa : FrameInv s₀ (· = sha.id) sa :=
    hsa ▸ hI19.splice (.inl (id_of_gep_eq hv16 hqa fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hsha, PoisonOr.value_inj] at hp'; rw [← hp']))
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun sb ⟨qb, bb, hqb, hsb⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hqb
  have hIb : FrameInv s₀ (· = sha.id) sb :=
    hsb ▸ hIa.splice (.inl (id_of_gep_eq hv18 hqb fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hsha, PoisonOr.value_inj] at hp'; rw [← hp']))
  denote_step_all v 27
  refine (gep_value_value sha 256 128 0#64).elim fun st13 ⟨e13, h13id⟩ => ?_
  have h13 : v13 = PoisonOr.value st13 := by
    rw [hv13]; simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero]; rw [hsha, hzero]; exact e13
  have h14 : ∀ q, v14 = .value q → q.id = sha.id := fun q hq =>
    id_of_gep_eq hv14 hq fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hsha, PoisonOr.value_inj] at hp'; rw [← hp']
  refine walk_condBr vacuous_poison fun b _ => ?_
  by_cases hb : b = 1
  · simp only [hb, ↓reduceIte]
    exact app_bb5 Vamb s₀ sha hsha _ _ _ _ st13 h13 h13id h14 _ _ hIb
  · simp only [hb, ↓reduceIte]
    exact app_bb2 Vamb s₀ sha hsha _ _ _ st13 h13 h13id h14 _ _ hIb

set_option maxHeartbeats 4000000 in
theorem fd_sha512_append_frame (sha : Pointer) (data : SLLVM.Ptr) (sz : LLVM.IntW 64)
    (s : GlobalState) (hs : s.WF) : fd_sha512_append_frame_spec sha data sz s := by
  simp only [fd_sha512_append_frame_spec, Cfg.denote]
  refine runFunction_frameInv (W := (· = sha.id)) hs ?_
  denote_step_all v 12
  denote_eval v 0 0
  refine walk_condBr vacuous_poison fun b _ => ?_
  by_cases hb : b = 1
  · simp only [hb, ↓reduceIte]
    exact app_bb10 _ s sha (fun _ => rfl) _ _ (FrameInv.refl hs _)
  · simp only [hb, ↓reduceIte]
    exact app_bb1 _ s sha (fun _ => rfl) (fun _ => by simp only [Ctxt.Valuation.cons_succ]; rw [hv0]; rfl)
      _ _ (FrameInv.refl hs _)

end Firedancer.Common
