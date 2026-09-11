/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.SHA.fd_sha512_core_ref
import SSA.Projects.Firedancer.Common.Proof.SHA.Walk

/-!
# `fd_sha512_core_ref` writes only the hash state

Partial correctness, so neither termination nor poison freedom is needed. The
invariant is `CoreRefInv`: the state is well formed and every block below the
entry counter other than the hash state's reads as on entry. It holds after the
entry block's `alloca`, and `Blocks.run_inv` carries it through the three
loops, one block at a time:

* loads, lifetime markers and terminators leave the state as it was;
* the `fd_ulong_bswap`/`fd_ulong_rotate_right` calls hand back an equivalent
  state, whatever their arguments;
* the two round-buffer stores go through `X`, the entry block's `alloca`, which
  sits at the entry counter and so below nothing the invariant protects;
* the eight stores after the rounds go through the entry block's pointers into
  the hash state.

The block steps are stated over an arbitrary ambient valuation, with only the
facts about those pointers as hypotheses, so each is checked on its own.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-! ## Callees -/

/-- `fd_ulong_bswap` on any argument, poison included: it returns, and the state
comes back equivalent. -/
theorem bswap_call_cases (W : (Ctxt.ofList [SLLVM.Ty.bitvec 64]).Valuation) (s : GlobalState)
    (hs : s.WF) :
    StateT.run (runFunction (Cfg.denote ⟨fd_ulong_bswap.entry, fd_ulong_bswap.blocks⟩ W)) s
        = .poison
      ∨ ∃ x s₁, StateT.run (runFunction
          (Cfg.denote ⟨fd_ulong_bswap.entry, fd_ulong_bswap.blocks⟩ W)) s = .value ([x]ₕ, s₁)
        ∧ s ≈ s₁ := by
  right
  refine ⟨SLLVM.bswap (W ⟨0, rfl⟩), s.popFrame s.mem, run_runFunction (s' := s) ?_,
    hs.popFrame_equiv⟩
  simp only [Cfg.denote]
  denote_step_all v 0
  denote_eval v 0 0
  subst hv0
  simp_return

/-- ... and `fd_ulong_rotate_right`. -/
theorem rotr_call_cases (W : (Ctxt.ofList [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64]).Valuation)
    (s : GlobalState) (hs : s.WF) :
    StateT.run (runFunction
        (Cfg.denote ⟨fd_ulong_rotate_right.entry, fd_ulong_rotate_right.blocks⟩ W)) s = .poison
      ∨ ∃ x s₁, StateT.run (runFunction
          (Cfg.denote ⟨fd_ulong_rotate_right.entry, fd_ulong_rotate_right.blocks⟩ W)) s
          = .value ([x]ₕ, s₁)
        ∧ s ≈ s₁ := by
  right
  refine ⟨SLLVM.fshr (W ⟨1, rfl⟩) (W ⟨1, rfl⟩) (LLVM.zext 64 (W ⟨0, rfl⟩)), s.popFrame s.mem,
    run_runFunction (s' := s) ?_, hs.popFrame_equiv⟩
  simp only [Cfg.denote]
  denote_step_all v 1
  denote_eval v 0 1
  subst hv0; subst hv1
  simp_return
  rfl

/-! ## The invariant -/

/-- Well formed, and every block below `s₀`'s counter other than `w` reads as
it did in `s₀`. -/
def CoreRefInv (s₀ : GlobalState) (w : BlockId) (s : GlobalState) : Prop :=
  s.WF ∧ ∀ b : BlockId, b.id < s₀.alloc.nextFreeBlock → b ≠ w → s.mem.live? b = s₀.mem.live? b

theorem CoreRefInv.of_equiv {s₀ s s₁ : GlobalState} {w : BlockId} (h : CoreRefInv s₀ w s)
    (he : s ≈ s₁) : CoreRefInv s₀ w s₁ :=
  ⟨h.1.of_equiv he, fun b hb hbw => (he.live b).symm.trans (h.2 b hb hbw)⟩

/-- A store keeps the invariant if it writes `w` or a block at or above the
entry counter. -/
theorem CoreRefInv.splice {s₀ s : GlobalState} {w : BlockId} (h : CoreRefInv s₀ w s)
    {q : Pointer} {n : Nat} {b : BitVec n}
    (hq : q.id = w ∨ s₀.alloc.nextFreeBlock ≤ q.id.id) :
    CoreRefInv s₀ w { s with mem := s.mem.splice q b } := by
  refine ⟨h.1.splice, fun c hc hcw => ?_⟩
  have hne : q.id ≠ c := by
    rintro rfl
    rcases hq with hq | hq
    · exact hcw hq
    · omega
  rw [live?_splice_ne hne]
  exact h.2 c hc hcw

/-! ## The loop blocks -/

set_option maxHeartbeats 2000000 in
/-- `^bb4`: the eight hash-state stores, through the entry block's pointers. -/
theorem core_bb4_step (Vamb : fd_sha512_core_ref.Γout.Valuation) (s₀ : GlobalState)
    (w : BlockId)
    (hst : ∀ (m : Nat) (h : fd_sha512_core_ref.Γout[m]? = some SLLVM.Ty.ptr) (q : Pointer),
      Vamb ⟨m, h⟩ = PoisonOr.value q → m ∈ [8, 9, 10, 11, 12, 13, 14, 39] → q.id = w)
    {ts : List SLLVM.Ty} (hidx : fd_sha512_core_ref.sigs[3]? = some ts)
    (args : HVector TyDenote.toType ts) (s : GlobalState) (hI : CoreRefInv s₀ w s) :
    ∃ res, StateT.run ((fd_sha512_core_ref.blocks.get 3 hidx).2.denote
        (Ctxt.Valuation.ofHVector args.reverse ++ Vamb)) s = res
      ∧ ∀ p s', res = .value (p, s') → CoreRefInv s₀ w s' := by
  have hts : ts = fd_sha512_core_ref.sigs[3]'(by decide) := by
    rw [List.getElem?_eq_getElem (by decide)] at hidx; exact (Option.some.inj hidx).symm
  subst hts
  denote_reduce_get
  refine walk_bare ?_
  denote_number_from 154
  denote_step_all v 154
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s0 ⟨q0, b0, hq0, hs0⟩ => ?_
  simp only [Ctxt.Valuation.cons_succ] at hq0
  rw [valuation_append_right' _ _ _ _ (by decide)] at hq0
  have hI0 : CoreRefInv s₀ w s0 := hs0 ▸ hI.splice (.inl (hst _ _ _ hq0 (by decide)))
  denote_step_all v 155
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s1 ⟨q1, b1, hq1, hs1⟩ => ?_
  simp only [Ctxt.Valuation.cons_succ] at hq1
  rw [valuation_append_right' _ _ _ _ (by decide)] at hq1
  have hI1 : CoreRefInv s₀ w s1 := hs1 ▸ hI0.splice (.inl (hst _ _ _ hq1 (by decide)))
  denote_step_all v 156
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s2 ⟨q2, b2, hq2, hs2⟩ => ?_
  simp only [Ctxt.Valuation.cons_succ] at hq2
  rw [valuation_append_right' _ _ _ _ (by decide)] at hq2
  have hI2 : CoreRefInv s₀ w s2 := hs2 ▸ hI1.splice (.inl (hst _ _ _ hq2 (by decide)))
  denote_step_all v 157
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s3 ⟨q3, b3, hq3, hs3⟩ => ?_
  simp only [Ctxt.Valuation.cons_succ] at hq3
  rw [valuation_append_right' _ _ _ _ (by decide)] at hq3
  have hI3 : CoreRefInv s₀ w s3 := hs3 ▸ hI2.splice (.inl (hst _ _ _ hq3 (by decide)))
  denote_step_all v 158
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s4 ⟨q4, b4, hq4, hs4⟩ => ?_
  simp only [Ctxt.Valuation.cons_succ] at hq4
  rw [valuation_append_right' _ _ _ _ (by decide)] at hq4
  have hI4 : CoreRefInv s₀ w s4 := hs4 ▸ hI3.splice (.inl (hst _ _ _ hq4 (by decide)))
  denote_step_all v 159
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s5 ⟨q5, b5, hq5, hs5⟩ => ?_
  simp only [Ctxt.Valuation.cons_succ] at hq5
  rw [valuation_append_right' _ _ _ _ (by decide)] at hq5
  have hI5 : CoreRefInv s₀ w s5 := hs5 ▸ hI4.splice (.inl (hst _ _ _ hq5 (by decide)))
  denote_step_all v 160
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s6 ⟨q6, b6, hq6, hs6⟩ => ?_
  simp only [Ctxt.Valuation.cons_succ] at hq6
  rw [valuation_append_right' _ _ _ _ (by decide)] at hq6
  have hI6 : CoreRefInv s₀ w s6 := hs6 ▸ hI5.splice (.inl (hst _ _ _ hq6 (by decide)))
  denote_step_all v 161
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s7 ⟨q7, b7, hq7, hs7⟩ => ?_
  simp only [Ctxt.Valuation.cons_succ] at hq7
  rw [valuation_append_right' _ _ _ _ (by decide)] at hq7
  have hI7 : CoreRefInv s₀ w s7 := hs7 ▸ hI6.splice (.inl (hst _ _ _ hq7 (by decide)))
  denote_step_all v 162
  refine walk_var_nil vacuous_poison (lifetime_expr_cases _ _ _ _) fun s8 hs8 => ?_
  denote_step_all v 164
  exact walk_term fun _ => hs8 ▸ hI7

/-- `^bb1`, the outer loop header: a lifetime marker and a branch. -/
theorem core_bb1_step (Vamb : fd_sha512_core_ref.Γout.Valuation) (s₀ : GlobalState) (w : BlockId)
    {ts : List SLLVM.Ty} (hidx : fd_sha512_core_ref.sigs[0]? = some ts)
    (args : HVector TyDenote.toType ts) (s : GlobalState) (hI : CoreRefInv s₀ w s) :
    ∃ res, StateT.run ((fd_sha512_core_ref.blocks.get 0 hidx).2.denote
        (Ctxt.Valuation.ofHVector args.reverse ++ Vamb)) s = res
      ∧ ∀ p s', res = .value (p, s') → CoreRefInv s₀ w s' := by
  have hts : ts = fd_sha512_core_ref.sigs[0]'(by decide) := by
    rw [List.getElem?_eq_getElem (by decide)] at hidx; exact (Option.some.inj hidx).symm
  subst hts
  denote_reduce_get
  refine walk_bare ?_
  refine walk_var_nil vacuous_poison (lifetime_expr_cases _ _ _ _) fun s1 hs1 => ?_
  exact walk_term fun _ => hs1 ▸ hI

/-- `^bb5`, the return. -/
theorem core_bb5_step (Vamb : fd_sha512_core_ref.Γout.Valuation) (s₀ : GlobalState) (w : BlockId)
    {ts : List SLLVM.Ty} (hidx : fd_sha512_core_ref.sigs[4]? = some ts)
    (args : HVector TyDenote.toType ts) (s : GlobalState) (hI : CoreRefInv s₀ w s) :
    ∃ res, StateT.run ((fd_sha512_core_ref.blocks.get 4 hidx).2.denote
        (Ctxt.Valuation.ofHVector args.reverse ++ Vamb)) s = res
      ∧ ∀ p s', res = .value (p, s') → CoreRefInv s₀ w s' := by
  have hts : ts = fd_sha512_core_ref.sigs[4]'(by decide) := by
    rw [List.getElem?_eq_getElem (by decide)] at hidx; exact (Option.some.inj hidx).symm
  subst hts
  denote_reduce_get
  refine walk_bare ?_
  exact walk_term fun _ => hI

/-- A pointer a gep made from a block at or above `n₀` is in that block too. -/
theorem le_id_of_gep {base : SLLVM.Ptr} {sz off : Nat} {i : LLVM.IntW 64} {q : Pointer} {n₀ : Nat}
    (h : SLLVM.gep base sz off i = .value q) (hb : ∀ p', base = .value p' → n₀ ≤ p'.id.id) :
    n₀ ≤ q.id.id := by
  obtain ⟨p', hp', hid⟩ := gep_eq_value h
  rw [hid]; exact hb p' hp'

set_option maxHeartbeats 4000000 in
/-- `^bb2`, rounds 0–15. -/
theorem core_bb2_step (Vamb : fd_sha512_core_ref.Γout.Valuation) (s₀ : GlobalState) (w : BlockId)
    (hX : ∀ (m : Nat) (h : fd_sha512_core_ref.Γout[m]? = some SLLVM.Ty.ptr) (q : Pointer),
      Vamb ⟨m, h⟩ = PoisonOr.value q → m = 15 → s₀.alloc.nextFreeBlock ≤ q.id.id)
    {ts : List SLLVM.Ty} (hidx : fd_sha512_core_ref.sigs[1]? = some ts)
    (args : HVector TyDenote.toType ts) (s : GlobalState) (hI : CoreRefInv s₀ w s) :
    ∃ res, StateT.run ((fd_sha512_core_ref.blocks.get 1 hidx).2.denote
        (Ctxt.Valuation.ofHVector args.reverse ++ Vamb)) s = res
      ∧ ∀ p s', res = .value (p, s') → CoreRefInv s₀ w s' := by
  have hts : ts = fd_sha512_core_ref.sigs[1]'(by decide) := by
    rw [List.getElem?_eq_getElem (by decide)] at hidx; exact (Option.some.inj hidx).symm
  subst hts
  denote_reduce_get
  refine walk_bare ?_
  denote_number_from 56
  denote_step_all v 56
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x57 s57 hs57 => ?_
  have hI57 : CoreRefInv s₀ w s57 := hs57 ▸ hI
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI57.1) fun x58 s58 he58 => ?_
  have hI58 := hI57.of_equiv he58
  denote_step_all v 59
  denote_eval v 59 59
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_st0 ⟨q_st0, b_st0, hq_st0, hs_st0⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero] at hq_st0
  rw [hv59] at hq_st0
  have hI_st0 : CoreRefInv s₀ w s_st0 := hs_st0 ▸ hI58.splice (.inr (le_id_of_gep hq_st0 fun p' hp' => by
    rw [valuation_append_right' _ _ _ _ (by decide)] at hp'
    exact hX _ _ _ hp' (by decide)))
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI_st0.1) fun x60 s60 he60 => ?_
  have hI60 := hI_st0.of_equiv he60
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI60.1) fun x61 s61 he61 => ?_
  have hI61 := hI60.of_equiv he61
  denote_step_all v 62
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI61.1) fun x63 s63 he63 => ?_
  have hI63 := hI61.of_equiv he63
  denote_step_all v 68
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x69 s69 hs69 => ?_
  have hI69 : CoreRefInv s₀ w s69 := hs69 ▸ hI63
  denote_step_all v 74
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI69.1) fun x75 s75 he75 => ?_
  have hI75 := hI69.of_equiv he75
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI75.1) fun x76 s76 he76 => ?_
  have hI76 := hI75.of_equiv he76
  denote_step_all v 77
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI76.1) fun x78 s78 he78 => ?_
  have hI78 := hI76.of_equiv he78
  denote_step_all v 88
  exact walk_term fun _ => hI78

set_option maxHeartbeats 8000000 in
/-- `^bb3`, rounds 16–79: the message schedule's store goes through `X` too. -/
theorem core_bb3_step (Vamb : fd_sha512_core_ref.Γout.Valuation) (s₀ : GlobalState) (w : BlockId)
    (hX : ∀ (m : Nat) (h : fd_sha512_core_ref.Γout[m]? = some SLLVM.Ty.ptr) (q : Pointer),
      Vamb ⟨m, h⟩ = PoisonOr.value q → m = 15 → s₀.alloc.nextFreeBlock ≤ q.id.id)
    {ts : List SLLVM.Ty} (hidx : fd_sha512_core_ref.sigs[2]? = some ts)
    (args : HVector TyDenote.toType ts) (s : GlobalState) (hI : CoreRefInv s₀ w s) :
    ∃ res, StateT.run ((fd_sha512_core_ref.blocks.get 2 hidx).2.denote
        (Ctxt.Valuation.ofHVector args.reverse ++ Vamb)) s = res
      ∧ ∀ p s', res = .value (p, s') → CoreRefInv s₀ w s' := by
  have hts : ts = fd_sha512_core_ref.sigs[2]'(by decide) := by
    rw [List.getElem?_eq_getElem (by decide)] at hidx; exact (Option.some.inj hidx).symm
  subst hts
  denote_reduce_get
  refine walk_bare ?_
  denote_number_from 98
  denote_step_all v 100
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x101 s101 hs101 => ?_
  have hI101 : CoreRefInv s₀ w s101 := hs101 ▸ hI
  denote_step_all v 104
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x105 s105 hs105 => ?_
  have hI105 : CoreRefInv s₀ w s105 := hs105 ▸ hI101
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI105.1) fun x106 s106 he106 => ?_
  have hI106 := hI105.of_equiv he106
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI106.1) fun x107 s107 he107 => ?_
  have hI107 := hI106.of_equiv he107
  denote_step_all v 110
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI107.1) fun x111 s111 he111 => ?_
  have hI111 := hI107.of_equiv he111
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI111.1) fun x112 s112 he112 => ?_
  have hI112 := hI111.of_equiv he112
  denote_step_all v 118
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x119 s119 hs119 => ?_
  have hI119 : CoreRefInv s₀ w s119 := hs119 ▸ hI112
  denote_step_all v 121
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x122 s122 hs122 => ?_
  have hI122 : CoreRefInv s₀ w s122 := hs122 ▸ hI119
  denote_step_all v 125
  denote_eval v 121 121
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_st0 ⟨q_st0, b_st0, hq_st0, hs_st0⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_st0
  rw [hv121] at hq_st0
  have hI_st0 : CoreRefInv s₀ w s_st0 := hs_st0 ▸ hI122.splice (.inr (le_id_of_gep hq_st0 fun p' hp' => by
    rw [valuation_append_right' _ _ _ _ (by decide)] at hp'
    exact hX _ _ _ hp' (by decide)))
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI_st0.1) fun x126 s126 he126 => ?_
  have hI126 := hI_st0.of_equiv he126
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI126.1) fun x127 s127 he127 => ?_
  have hI127 := hI126.of_equiv he127
  denote_step_all v 128
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI127.1) fun x129 s129 he129 => ?_
  have hI129 := hI127.of_equiv he129
  denote_step_all v 134
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x135 s135 hs135 => ?_
  have hI135 : CoreRefInv s₀ w s135 := hs135 ▸ hI129
  denote_step_all v 140
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI135.1) fun x141 s141 he141 => ?_
  have hI141 := hI135.of_equiv he141
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI141.1) fun x142 s142 he142 => ?_
  have hI142 := hI141.of_equiv he142
  denote_step_all v 143
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI142.1) fun x144 s144 he144 => ?_
  have hI144 := hI142.of_equiv he144
  denote_step_all v 153
  exact walk_term fun _ => hI144

/-- All five loop blocks at once, in exactly `Blocks.run_inv`'s step shape. -/
theorem core_loop_step (Vamb : fd_sha512_core_ref.Γout.Valuation) (s₀ : GlobalState) (w : BlockId)
    (hX : ∀ (m : Nat) (h : fd_sha512_core_ref.Γout[m]? = some SLLVM.Ty.ptr) (q : Pointer),
      Vamb ⟨m, h⟩ = PoisonOr.value q → m = 15 → s₀.alloc.nextFreeBlock ≤ q.id.id)
    (hst : ∀ (m : Nat) (h : fd_sha512_core_ref.Γout[m]? = some SLLVM.Ty.ptr) (q : Pointer),
      Vamb ⟨m, h⟩ = PoisonOr.value q → m ∈ [8, 9, 10, 11, 12, 13, 14, 39] → q.id = w) :
    ∀ (t : SuccArgs fd_sha512_core_ref.sigs) (s : GlobalState), CoreRefInv s₀ w s →
      ∀ p s', StateT.run ((fd_sha512_core_ref.blocks.get t.idx t.hidx).2.denote
          (Ctxt.Valuation.ofHVector t.args.reverse ++ Vamb)) s = .value (p, s') →
        (∀ res, p.2 = .inl res → CoreRefInv s₀ w s') ∧ (∀ t', p.2 = .inr t' → CoreRefInv s₀ w s') := by
  rintro ⟨idx, hidx, args⟩ s hI p s' h
  have key : ∃ res, StateT.run ((fd_sha512_core_ref.blocks.get idx hidx).2.denote
      (Ctxt.Valuation.ofHVector args.reverse ++ Vamb)) s = res
        ∧ ∀ p s', res = .value (p, s') → CoreRefInv s₀ w s' := by
    match idx, hidx with
    | 0, hidx => exact core_bb1_step Vamb s₀ w hidx args s hI
    | 1, hidx => exact core_bb2_step Vamb s₀ w hX hidx args s hI
    | 2, hidx => exact core_bb3_step Vamb s₀ w hX hidx args s hI
    | 3, hidx => exact core_bb4_step Vamb s₀ w hst hidx args s hI
    | 4, hidx => exact core_bb5_step Vamb s₀ w hidx args s hI
    | _ + 5, hidx => exact absurd hidx (by simp [fd_sha512_core_ref])
  obtain ⟨res, rfl, hpost⟩ := key
  exact ⟨fun _ _ => hpost p s' h, fun _ _ => hpost p s' h⟩

/-! ## The whole call -/

/-- The invariant holds right after the entry block's `alloca`. -/
theorem CoreRefInv.afterAlloca {s : GlobalState} (hs : s.WF) (w : BlockId) (n : Nat) :
    CoreRefInv s w (s.afterAlloca n) :=
  ⟨hs.afterAlloca n, fun _ hb _ => live?_afterAlloca_of_lt hb⟩

set_option maxHeartbeats 4000000 in
theorem fd_sha512_core_ref_frame (st : Pointer) (blk : SLLVM.Ptr) (cnt : LLVM.IntW 64)
    (s : GlobalState) (hs : s.WF) : fd_sha512_core_ref_frame_spec st blk cnt s := by
  simp only [fd_sha512_core_ref_frame_spec, Cfg.denote]
  generalize hw : st.id = w
  refine runFunction_frameInv (W := (· = w)) hs ?_
  denote_step_all v 19
  refine walk_var_single vacuous_poison (addressof_expr_cases _ _ _) fun x20 s20 hs20 => ?_
  refine walk_var_single vacuous_poison (alloca_expr_cases _ _ _) fun x21 s21 ⟨hx21, hs21⟩ => ?_
  have hI21 : CoreRefInv s w s21 := by rw [hs21, hs20]; exact CoreRefInv.afterAlloca hs w _
  denote_step_all v 28
  denote_eval v 22 28
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x29 s29 hs29 => ?_
  have hI29 : CoreRefInv s w s29 := hs29 ▸ hI21
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x30 s30 hs30 => ?_
  have hI30 : CoreRefInv s w s30 := hs30 ▸ hI29
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x31 s31 hs31 => ?_
  have hI31 : CoreRefInv s w s31 := hs31 ▸ hI30
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x32 s32 hs32 => ?_
  have hI32 : CoreRefInv s w s32 := hs32 ▸ hI31
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x33 s33 hs33 => ?_
  have hI33 : CoreRefInv s w s33 := hs33 ▸ hI32
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x34 s34 hs34 => ?_
  have hI34 : CoreRefInv s w s34 := hs34 ▸ hI33
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x35 s35 hs35 => ?_
  have hI35 : CoreRefInv s w s35 := hs35 ▸ hI34
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x36 s36 hs36 => ?_
  have hI36 : CoreRefInv s w s36 := hs36 ▸ hI35
  -- the branch into `^bb1`: from here the walk is `Blocks.run`, and the loop rule
  refine ⟨_, rfl, fun p t h => ?_⟩
  simp only [BlockCom.denote_term, Terminator.denote_br, pure_bind] at h
  refine Blocks.run_inv (CoreRefInv s w) (fun _ t => CoreRefInv s w t)
    (core_loop_step _ s w ?_ ?_) hI36 p t h
  · -- `%21`, the round buffer, sits at the entry counter
    intro m hm q hq he
    subst he
    simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
    rw [hx21, PoisonOr.value_inj] at hq
    rw [← hq, hs20]
  · -- the hash-state pointers: `%arg0` and its seven geps `%22`–`%28`
    intro m hm q hq he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
      rw [hv28] at hq
      obtain ⟨p', hp', hid⟩ := gepConst_eq_value hq
      rw [PoisonOr.value_inj] at hp'
      rw [hid, ← hp', hw]
    · simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
      rw [hv27] at hq
      obtain ⟨p', hp', hid⟩ := gepConst_eq_value hq
      rw [PoisonOr.value_inj] at hp'
      rw [hid, ← hp', hw]
    · simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
      rw [hv26] at hq
      obtain ⟨p', hp', hid⟩ := gepConst_eq_value hq
      rw [PoisonOr.value_inj] at hp'
      rw [hid, ← hp', hw]
    · simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
      rw [hv25] at hq
      obtain ⟨p', hp', hid⟩ := gepConst_eq_value hq
      rw [PoisonOr.value_inj] at hp'
      rw [hid, ← hp', hw]
    · simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
      rw [hv24] at hq
      obtain ⟨p', hp', hid⟩ := gepConst_eq_value hq
      rw [PoisonOr.value_inj] at hp'
      rw [hid, ← hp', hw]
    · simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
      rw [hv23] at hq
      obtain ⟨p', hp', hid⟩ := gepConst_eq_value hq
      rw [PoisonOr.value_inj] at hp'
      rw [hid, ← hp', hw]
    · simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
      rw [hv22] at hq
      obtain ⟨p', hp', hid⟩ := gepConst_eq_value hq
      rw [PoisonOr.value_inj] at hp'
      rw [hid, ← hp', hw]
    · simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero,
        Ctxt.Valuation.ofHVector_cons] at hq
      rw [PoisonOr.value_inj] at hq
      rw [← hq, hw]

end Firedancer.Common
