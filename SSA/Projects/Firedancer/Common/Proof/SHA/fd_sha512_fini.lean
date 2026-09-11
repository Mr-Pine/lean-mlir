/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.SHA.fd_sha512_fini
import SSA.Projects.Firedancer.Common.Proof.SHA.Calls

/-!
# `fd_sha512_fini` writes only `sha` and `hash`

A forward walk: the region has no loop, so each block is a lemma about the walk
*from* it, taking its arguments as they are passed and the entry block's
pointers as hypotheses. `^bb0` branches to `^bb1` or straight to `^bb2`, and
`^bb1` falls through to `^bb2`, so `^bb2` is proved once and used twice.

Every write goes through `sha` or `hash`: the two `memset`s and the byte stores
through geps of `sha`, both `fd_sha512_core_ref` calls through `%5 =
&sha->state`, and the digest stores through `hash` and its geps.
-/

set_option linter.unusedSimpArgs false  -- the walks share generic lookup sets

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

set_option maxHeartbeats 8000000 in
/-- The walk from `^bb2`: the final padding, compression and digest. -/
theorem fini_bb2 (Vamb : fd_sha512_fini.Γout.Valuation) (s₀ : GlobalState) (sha hash st5 : Pointer)
    (hsha : ∀ h : fd_sha512_fini.Γout[16]? = some SLLVM.Ty.ptr, Vamb ⟨16, h⟩ = .value sha)
    (hhash : ∀ h : fd_sha512_fini.Γout[15]? = some SLLVM.Ty.ptr, Vamb ⟨15, h⟩ = .value hash)
    (h5 : ∀ h : fd_sha512_fini.Γout[9]? = some SLLVM.Ty.ptr, Vamb ⟨9, h⟩ = .value st5)
    (h5id : st5.id = sha.id) (a18 : LLVM.IntW 64)
    (h1 : fd_sha512_fini.sigs[1]? = some [SLLVM.Ty.bitvec 64])
    (s : GlobalState) (hI : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s) :
    ∃ res, StateT.run (fd_sha512_fini.blocks.run Vamb ⟨1, h1, a18 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 19
  denote_step_all v 20
  denote_eval v 19 19
  refine walk_call_single vacuous_poison (memset_call_cases _ _ hI.1) fun x_c0 s_c0 ⟨q_c0, hq_c0, hwf_c0, hl_c0⟩ => ?_
  simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq_c0
  have e_c0 := id_of_gep_eq hv19 hq_c0 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hsha, PoisonOr.value_inj] at hp'; rw [← hp']
  have hI_c0 := hI.of_call hwf_c0 fun b hb => hl_c0 b fun e => hb (.inl (e.trans e_c0))
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI_c0.1) fun x22 s22 he22 => ?_
  have hI22 := hI_c0.of_equiv he22
  denote_step_all v 23
  denote_eval v 23 23
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s1 ⟨q_s1, b_s1, hq_s1, hs_s1⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s1
  have hI_s1 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s1 := hs_s1 ▸ hI22.splice (.inl (.inl (id_of_gepConst_eq hv23 hq_s1 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hsha, PoisonOr.value_inj] at hp'; rw [← hp'])))
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI_s1.1) fun x24 s24 he24 => ?_
  have hI24 := hI_s1.of_equiv he24
  denote_step_all v 25
  denote_eval v 25 25
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s2 ⟨q_s2, b_s2, hq_s2, hs_s2⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s2
  have hI_s2 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s2 := hs_s2 ▸ hI24.splice (.inl (.inl (id_of_gepConst_eq hv25 hq_s2 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hsha, PoisonOr.value_inj] at hp'; rw [← hp'])))
  refine walk_call_nil vacuous_poison (core_ref_call_cases' _ st5 (by simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero]; exact h5 _) _ hI_s2.1) fun s_c3 ⟨hwf_c3, hl_c3⟩ => ?_
  have hI_c3 := hI_s2.of_call hwf_c3 fun b hb => hl_c3 b fun e => hb (.inl (e.trans h5id))
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x26 s26 hs26 => ?_
  have hI26 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s26 := hs26 ▸ hI_c3
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI26.1) fun x27 s27 he27 => ?_
  have hI27 := hI26.of_equiv he27
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s4 ⟨q_s4, b_s4, hq_s4, hs_s4⟩ => ?_
  simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq_s4
  rw [hhash, PoisonOr.value_inj] at hq_s4
  have hI_s4 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s4 := hs_s4 ▸ hI27.splice (.inl (.inr (by rw [← hq_s4])))
  denote_step_all v 28
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x29 s29 hs29 => ?_
  have hI29 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s29 := hs29 ▸ hI_s4
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI29.1) fun x30 s30 he30 => ?_
  have hI30 := hI29.of_equiv he30
  denote_step_all v 31
  denote_eval v 31 31
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s5 ⟨q_s5, b_s5, hq_s5, hs_s5⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s5
  have hI_s5 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s5 := hs_s5 ▸ hI30.splice (.inl (.inr (id_of_gepConst_eq hv31 hq_s5 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hhash, PoisonOr.value_inj] at hp'; rw [← hp'])))
  denote_step_all v 32
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x33 s33 hs33 => ?_
  have hI33 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s33 := hs33 ▸ hI_s5
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI33.1) fun x34 s34 he34 => ?_
  have hI34 := hI33.of_equiv he34
  denote_step_all v 35
  denote_eval v 35 35
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s6 ⟨q_s6, b_s6, hq_s6, hs_s6⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s6
  have hI_s6 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s6 := hs_s6 ▸ hI34.splice (.inl (.inr (id_of_gepConst_eq hv35 hq_s6 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hhash, PoisonOr.value_inj] at hp'; rw [← hp'])))
  denote_step_all v 36
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x37 s37 hs37 => ?_
  have hI37 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s37 := hs37 ▸ hI_s6
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI37.1) fun x38 s38 he38 => ?_
  have hI38 := hI37.of_equiv he38
  denote_step_all v 39
  denote_eval v 39 39
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s7 ⟨q_s7, b_s7, hq_s7, hs_s7⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s7
  have hI_s7 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s7 := hs_s7 ▸ hI38.splice (.inl (.inr (id_of_gepConst_eq hv39 hq_s7 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hhash, PoisonOr.value_inj] at hp'; rw [← hp'])))
  denote_step_all v 40
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x41 s41 hs41 => ?_
  have hI41 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s41 := hs41 ▸ hI_s7
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI41.1) fun x42 s42 he42 => ?_
  have hI42 := hI41.of_equiv he42
  denote_step_all v 43
  denote_eval v 43 43
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s8 ⟨q_s8, b_s8, hq_s8, hs_s8⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s8
  have hI_s8 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s8 := hs_s8 ▸ hI42.splice (.inl (.inr (id_of_gepConst_eq hv43 hq_s8 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hhash, PoisonOr.value_inj] at hp'; rw [← hp'])))
  denote_step_all v 44
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x45 s45 hs45 => ?_
  have hI45 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s45 := hs45 ▸ hI_s8
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI45.1) fun x46 s46 he46 => ?_
  have hI46 := hI45.of_equiv he46
  denote_step_all v 47
  denote_eval v 47 47
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s9 ⟨q_s9, b_s9, hq_s9, hs_s9⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s9
  have hI_s9 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s9 := hs_s9 ▸ hI46.splice (.inl (.inr (id_of_gepConst_eq hv47 hq_s9 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hhash, PoisonOr.value_inj] at hp'; rw [← hp'])))
  denote_step_all v 48
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x49 s49 hs49 => ?_
  have hI49 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s49 := hs49 ▸ hI_s9
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI49.1) fun x50 s50 he50 => ?_
  have hI50 := hI49.of_equiv he50
  denote_step_all v 51
  denote_eval v 51 51
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s10 ⟨q_s10, b_s10, hq_s10, hs_s10⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s10
  have hI_s10 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s10 := hs_s10 ▸ hI50.splice (.inl (.inr (id_of_gepConst_eq hv51 hq_s10 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hhash, PoisonOr.value_inj] at hp'; rw [← hp'])))
  denote_step_all v 52
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x53 s53 hs53 => ?_
  have hI53 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s53 := hs53 ▸ hI_s10
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI53.1) fun x54 s54 he54 => ?_
  have hI54 := hI53.of_equiv he54
  denote_step_all v 55
  denote_eval v 55 55
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s11 ⟨q_s11, b_s11, hq_s11, hs_s11⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s11
  have hI_s11 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s11 := hs_s11 ▸ hI54.splice (.inl (.inr (id_of_gepConst_eq hv55 hq_s11 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hhash, PoisonOr.value_inj] at hp'; rw [← hp'])))
  refine walk_ret ⟨_, rfl, fun p t h => ?_⟩
  dsimp only at h
  rw [EffectM.run_pure, PoisonOr.value_inj, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact hI_s11

/-- The walk from `^bb1`: a full buffer is zero-padded and compressed first. -/
theorem fini_bb1 (Vamb : fd_sha512_fini.Γout.Valuation) (s₀ : GlobalState) (sha hash st5 : Pointer)
    (hsha : ∀ h : fd_sha512_fini.Γout[16]? = some SLLVM.Ty.ptr, Vamb ⟨16, h⟩ = .value sha)
    (hhash : ∀ h : fd_sha512_fini.Γout[15]? = some SLLVM.Ty.ptr, Vamb ⟨15, h⟩ = .value hash)
    (h5 : ∀ h : fd_sha512_fini.Γout[9]? = some SLLVM.Ty.ptr, Vamb ⟨9, h⟩ = .value st5)
    (h5id : st5.id = sha.id) (h0 : fd_sha512_fini.sigs[0]? = some [])
    (s : GlobalState) (hI : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s) :
    ∃ res, StateT.run (fd_sha512_fini.blocks.run Vamb ⟨0, h0, .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 15
  denote_step_all v 16
  denote_eval v 15 15
  refine walk_call_single vacuous_poison (memset_call_cases _ _ hI.1) fun x_c0 s_c0 ⟨q_c0, hq_c0, hwf_c0, hl_c0⟩ => ?_
  simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq_c0
  have e_c0 := id_of_gep_eq hv15 hq_c0 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hsha, PoisonOr.value_inj] at hp'; rw [← hp']
  have hI_c0 := hI.of_call hwf_c0 fun b hb => hl_c0 b fun e => hb (.inl (e.trans e_c0))
  refine walk_call_nil vacuous_poison (core_ref_call_cases' _ st5 (by simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero]; exact h5 _) _ hI_c0.1) fun s_c1 ⟨hwf_c1, hl_c1⟩ => ?_
  have hI_c1 := hI_c0.of_call hwf_c1 fun b hb => hl_c1 b fun e => hb (.inl (e.trans h5id))
  exact walk_br (fini_bb2 Vamb s₀ sha hash st5 hsha hhash h5 h5id _ _ _ hI_c1)

set_option maxHeartbeats 4000000 in
theorem fd_sha512_fini_frame (sha hash : Pointer) (s : GlobalState) (hs : s.WF) :
    fd_sha512_fini_frame_spec sha hash s := by
  simp only [fd_sha512_fini_frame_spec, Cfg.denote]
  refine runFunction_frameInv (W := fun b => b = sha.id ∨ b = hash.id) hs ?_
  denote_step_all v 6
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x7 s7 hs7 => ?_
  have hI7 : FrameInv s (fun b => b = sha.id ∨ b = hash.id) s7 := hs7 ▸ FrameInv.refl hs _
  denote_step_all v 8
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x9 s9 hs9 => ?_
  have hI9 : FrameInv s (fun b => b = sha.id ∨ b = hash.id) s9 := hs9 ▸ hI7
  denote_step_all v 10
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x11 s11 hs11 => ?_
  have hI11 : FrameInv s (fun b => b = sha.id ∨ b = hash.id) s11 := hs11 ▸ hI9
  denote_step_all v 12
  denote_eval v 5 5
  denote_eval v 12 12
  -- `buf[ buf_used ] = 0x80`, through `sha`
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s12 ⟨q12, b12, hq12, hs12⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq12
  have hI12 : FrameInv s (fun b => b = sha.id ∨ b = hash.id) s12 :=
    hs12 ▸ hI11.splice (.inl (.inl (id_of_gep_eq hv12 hq12 fun p' hp' => by
      simp only [Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero,
        PoisonOr.value_inj] at hp'
      rw [← hp'])))
  denote_step_all v 14
  -- `%5 = &sha->state`, which both successors pass to `fd_sha512_core_ref`
  have h5 : v5 = .value (sha.withOffset (BitVec.ofNat 64 128)) := by
    rw [hv5]; exact gepConst_value sha 128
  refine walk_condBr vacuous_poison fun b _ => ?_
  by_cases hb : b = 1
  · simp only [hb, ↓reduceIte]
    exact fini_bb1 _ s sha hash (sha.withOffset (BitVec.ofNat 64 128)) (fun _ => rfl) (fun _ => rfl) (fun _ => h5) rfl _ _ hI12
  · simp only [hb, ↓reduceIte]
    exact fini_bb2 _ s sha hash (sha.withOffset (BitVec.ofNat 64 128)) (fun _ => rfl) (fun _ => rfl) (fun _ => h5) rfl _ _ _ hI12

end Firedancer.Common
