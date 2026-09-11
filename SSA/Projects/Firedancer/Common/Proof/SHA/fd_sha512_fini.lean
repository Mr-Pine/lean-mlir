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
through geps of `sha`, both `fd_sha512_core_ref` calls through `%17 =
&sha->state`, and the digest stores through `hash` and its geps.
-/

set_option linter.unusedSimpArgs false  -- the walks share generic lookup sets

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

set_option maxHeartbeats 8000000 in
/-- The walk from `^bb2`: the final padding, compression and digest. -/
theorem fini_bb2 (Vamb : fd_sha512_fini.Γout.Valuation) (s₀ : GlobalState) (sha hash st17 : Pointer)
    (hsha : ∀ h : fd_sha512_fini.Γout[28]? = some SLLVM.Ty.ptr, Vamb ⟨28, h⟩ = .value sha)
    (hhash : ∀ h : fd_sha512_fini.Γout[27]? = some SLLVM.Ty.ptr, Vamb ⟨27, h⟩ = .value hash)
    (h17 : ∀ h : fd_sha512_fini.Γout[9]? = some SLLVM.Ty.ptr, Vamb ⟨9, h⟩ = .value st17)
    (h17id : st17.id = sha.id) (a30 : LLVM.IntW 64)
    (h1 : fd_sha512_fini.sigs[1]? = some [SLLVM.Ty.bitvec 64])
    (s : GlobalState) (hI : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s) :
    ∃ res, StateT.run (fd_sha512_fini.blocks.run Vamb ⟨1, h1, a30 ::ₕ .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 31
  denote_step_all v 32
  denote_eval v 31 31
  refine walk_call_single vacuous_poison (memset_call_cases _ _ hI.1) fun x_c0 s_c0 ⟨q_c0, hq_c0, hwf_c0, hl_c0⟩ => ?_
  simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq_c0
  have e_c0 := id_of_gep_eq hv31 hq_c0 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hsha, PoisonOr.value_inj] at hp'; rw [← hp']
  have hI_c0 := hI.of_call hwf_c0 fun b hb => hl_c0 b fun e => hb (.inl (e.trans e_c0))
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI_c0.1) fun x34 s34 he34 => ?_
  have hI34 := hI_c0.of_equiv he34
  denote_step_all v 35
  denote_eval v 35 35
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s1 ⟨q_s1, b_s1, hq_s1, hs_s1⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s1
  have hI_s1 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s1 := hs_s1 ▸ hI34.splice (.inl (.inl (id_of_gep2_eq hv35 hq_s1 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hsha, PoisonOr.value_inj] at hp'; rw [← hp'])))
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI_s1.1) fun x36 s36 he36 => ?_
  have hI36 := hI_s1.of_equiv he36
  denote_step_all v 37
  denote_eval v 37 37
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s2 ⟨q_s2, b_s2, hq_s2, hs_s2⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s2
  have hI_s2 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s2 := hs_s2 ▸ hI36.splice (.inl (.inl (id_of_gep2_eq hv37 hq_s2 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hsha, PoisonOr.value_inj] at hp'; rw [← hp'])))
  refine walk_call_nil vacuous_poison (core_ref_call_cases' _ st17 (by simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero]; exact h17 _) _ hI_s2.1) fun s_c3 ⟨hwf_c3, hl_c3⟩ => ?_
  have hI_c3 := hI_s2.of_call hwf_c3 fun b hb => hl_c3 b fun e => hb (.inl (e.trans h17id))
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x38 s38 hs38 => ?_
  have hI38 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s38 := hs38 ▸ hI_c3
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI38.1) fun x39 s39 he39 => ?_
  have hI39 := hI38.of_equiv he39
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s4 ⟨q_s4, b_s4, hq_s4, hs_s4⟩ => ?_
  simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq_s4
  rw [hhash, PoisonOr.value_inj] at hq_s4
  have hI_s4 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s4 := hs_s4 ▸ hI39.splice (.inl (.inr (by rw [← hq_s4])))
  denote_step_all v 40
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x41 s41 hs41 => ?_
  have hI41 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s41 := hs41 ▸ hI_s4
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI41.1) fun x42 s42 he42 => ?_
  have hI42 := hI41.of_equiv he42
  denote_step_all v 43
  denote_eval v 43 43
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s5 ⟨q_s5, b_s5, hq_s5, hs_s5⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s5
  have hI_s5 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s5 := hs_s5 ▸ hI42.splice (.inl (.inr (id_of_gep_eq hv43 hq_s5 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hhash, PoisonOr.value_inj] at hp'; rw [← hp'])))
  denote_step_all v 44
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x45 s45 hs45 => ?_
  have hI45 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s45 := hs45 ▸ hI_s5
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI45.1) fun x46 s46 he46 => ?_
  have hI46 := hI45.of_equiv he46
  denote_step_all v 47
  denote_eval v 47 47
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s6 ⟨q_s6, b_s6, hq_s6, hs_s6⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s6
  have hI_s6 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s6 := hs_s6 ▸ hI46.splice (.inl (.inr (id_of_gep_eq hv47 hq_s6 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hhash, PoisonOr.value_inj] at hp'; rw [← hp'])))
  denote_step_all v 48
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x49 s49 hs49 => ?_
  have hI49 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s49 := hs49 ▸ hI_s6
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI49.1) fun x50 s50 he50 => ?_
  have hI50 := hI49.of_equiv he50
  denote_step_all v 51
  denote_eval v 51 51
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s7 ⟨q_s7, b_s7, hq_s7, hs_s7⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s7
  have hI_s7 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s7 := hs_s7 ▸ hI50.splice (.inl (.inr (id_of_gep_eq hv51 hq_s7 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hhash, PoisonOr.value_inj] at hp'; rw [← hp'])))
  denote_step_all v 52
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x53 s53 hs53 => ?_
  have hI53 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s53 := hs53 ▸ hI_s7
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI53.1) fun x54 s54 he54 => ?_
  have hI54 := hI53.of_equiv he54
  denote_step_all v 55
  denote_eval v 55 55
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s8 ⟨q_s8, b_s8, hq_s8, hs_s8⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s8
  have hI_s8 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s8 := hs_s8 ▸ hI54.splice (.inl (.inr (id_of_gep_eq hv55 hq_s8 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hhash, PoisonOr.value_inj] at hp'; rw [← hp'])))
  denote_step_all v 56
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x57 s57 hs57 => ?_
  have hI57 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s57 := hs57 ▸ hI_s8
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI57.1) fun x58 s58 he58 => ?_
  have hI58 := hI57.of_equiv he58
  denote_step_all v 59
  denote_eval v 59 59
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s9 ⟨q_s9, b_s9, hq_s9, hs_s9⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s9
  have hI_s9 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s9 := hs_s9 ▸ hI58.splice (.inl (.inr (id_of_gep_eq hv59 hq_s9 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hhash, PoisonOr.value_inj] at hp'; rw [← hp'])))
  denote_step_all v 60
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x61 s61 hs61 => ?_
  have hI61 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s61 := hs61 ▸ hI_s9
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI61.1) fun x62 s62 he62 => ?_
  have hI62 := hI61.of_equiv he62
  denote_step_all v 63
  denote_eval v 63 63
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s10 ⟨q_s10, b_s10, hq_s10, hs_s10⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s10
  have hI_s10 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s10 := hs_s10 ▸ hI62.splice (.inl (.inr (id_of_gep_eq hv63 hq_s10 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hhash, PoisonOr.value_inj] at hp'; rw [← hp'])))
  denote_step_all v 64
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x65 s65 hs65 => ?_
  have hI65 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s65 := hs65 ▸ hI_s10
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI65.1) fun x66 s66 he66 => ?_
  have hI66 := hI65.of_equiv he66
  denote_step_all v 67
  denote_eval v 67 67
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_s11 ⟨q_s11, b_s11, hq_s11, hs_s11⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_s11
  have hI_s11 : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s_s11 := hs_s11 ▸ hI66.splice (.inl (.inr (id_of_gep_eq hv67 hq_s11 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hhash, PoisonOr.value_inj] at hp'; rw [← hp'])))
  refine walk_ret ⟨_, rfl, fun p t h => ?_⟩
  dsimp only at h
  rw [EffectM.run_pure, PoisonOr.value_inj, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact hI_s11

/-- The walk from `^bb1`: a full buffer is zero-padded and compressed first. -/
theorem fini_bb1 (Vamb : fd_sha512_fini.Γout.Valuation) (s₀ : GlobalState) (sha hash st17 : Pointer)
    (hsha : ∀ h : fd_sha512_fini.Γout[28]? = some SLLVM.Ty.ptr, Vamb ⟨28, h⟩ = .value sha)
    (hhash : ∀ h : fd_sha512_fini.Γout[27]? = some SLLVM.Ty.ptr, Vamb ⟨27, h⟩ = .value hash)
    (h17 : ∀ h : fd_sha512_fini.Γout[9]? = some SLLVM.Ty.ptr, Vamb ⟨9, h⟩ = .value st17)
    (h17id : st17.id = sha.id) (h0 : fd_sha512_fini.sigs[0]? = some [])
    (s : GlobalState) (hI : FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) s) :
    ∃ res, StateT.run (fd_sha512_fini.blocks.run Vamb ⟨0, h0, .nil⟩) s = res
      ∧ ∀ p t, res = .value (p, t) → FrameInv s₀ (fun b => b = sha.id ∨ b = hash.id) t := by
  rw [Blocks.run_step]
  denote_reduce_get
  denote_number_from 27
  denote_step_all v 28
  denote_eval v 27 27
  refine walk_call_single vacuous_poison (memset_call_cases _ _ hI.1) fun x_c0 s_c0 ⟨q_c0, hq_c0, hwf_c0, hl_c0⟩ => ?_
  simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq_c0
  have e_c0 := id_of_gep_eq hv27 hq_c0 fun p' hp' => by simp only [HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hp'; rw [hsha, PoisonOr.value_inj] at hp'; rw [← hp']
  have hI_c0 := hI.of_call hwf_c0 fun b hb => hl_c0 b fun e => hb (.inl (e.trans e_c0))
  refine walk_call_nil vacuous_poison (core_ref_call_cases' _ st17 (by simp only [HVector.map, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero, HVector.reverse_cons, HVector.reverse_nil, HVector.reverseAux_cons, HVector.reverseAux_nil, Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero]; exact h17 _) _ hI_c0.1) fun s_c1 ⟨hwf_c1, hl_c1⟩ => ?_
  have hI_c1 := hI_c0.of_call hwf_c1 fun b hb => hl_c1 b fun e => hb (.inl (e.trans h17id))
  exact walk_br (fini_bb2 Vamb s₀ sha hash st17 hsha hhash h17 h17id _ _ _ hI_c1)

set_option maxHeartbeats 4000000 in
theorem fd_sha512_fini_frame (sha hash : Pointer) (s : GlobalState) (hs : s.WF) :
    fd_sha512_fini_frame_spec sha hash s := by
  simp only [fd_sha512_fini_frame_spec, Cfg.denote]
  refine runFunction_frameInv (W := fun b => b = sha.id ∨ b = hash.id) hs ?_
  denote_step_all v 18
  denote_eval v 0 0
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x19 s19 hs19 => ?_
  have hI19 : FrameInv s (fun b => b = sha.id ∨ b = hash.id) s19 := hs19 ▸ FrameInv.refl hs _
  denote_step_all v 20
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x21 s21 hs21 => ?_
  have hI21 : FrameInv s (fun b => b = sha.id ∨ b = hash.id) s21 := hs21 ▸ hI19
  denote_step_all v 22
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x23 s23 hs23 => ?_
  have hI23 : FrameInv s (fun b => b = sha.id ∨ b = hash.id) s23 := hs23 ▸ hI21
  denote_step_all v 24
  denote_eval v 17 17
  denote_eval v 24 24
  -- `buf[ buf_used ] = 0x80`, through `sha`
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s24 ⟨q24, b24, hq24, hs24⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq24
  have hI24 : FrameInv s (fun b => b = sha.id ∨ b = hash.id) s24 :=
    hs24 ▸ hI23.splice (.inl (.inl (id_of_gep_eq hv24 hq24 fun p' hp' => by
      simp only [Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero,
        PoisonOr.value_inj] at hp'
      rw [← hp'])))
  denote_step_all v 26
  -- `&sha->state`, named for the two blocks that pass it to `fd_sha512_core_ref`
  refine (gep_value_value sha 256 128 0#64).elim fun st17 ⟨e17, h17id⟩ => ?_
  have h17 : v17 = PoisonOr.value st17 := by rw [hv17, hv0]; exact e17
  refine walk_condBr vacuous_poison fun b _ => ?_
  by_cases hb : b = 1
  · simp only [hb, ↓reduceIte]
    exact fini_bb1 _ s sha hash st17 (fun _ => rfl) (fun _ => rfl) (fun _ => h17) h17id _ _ hI24
  · simp only [hb, ↓reduceIte]
    exact fini_bb2 _ s sha hash st17 (fun _ => rfl) (fun _ => rfl) (fun _ => h17) h17id _ _ _ hI24

end Firedancer.Common
