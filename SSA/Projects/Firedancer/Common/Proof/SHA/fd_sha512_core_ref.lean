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
      Vamb ⟨m, h⟩ = PoisonOr.value q → m ∈ [8, 9, 10, 11, 12, 13, 14, 44] → q.id = w)
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
  denote_number_from 159
  denote_step_all v 159
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s0 ⟨q0, b0, hq0, hs0⟩ => ?_
  simp only [Ctxt.Valuation.cons_succ] at hq0
  rw [valuation_append_right' _ _ _ _ (by decide)] at hq0
  have hI0 : CoreRefInv s₀ w s0 := hs0 ▸ hI.splice (.inl (hst _ _ _ hq0 (by decide)))
  denote_step_all v 160
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s1 ⟨q1, b1, hq1, hs1⟩ => ?_
  simp only [Ctxt.Valuation.cons_succ] at hq1
  rw [valuation_append_right' _ _ _ _ (by decide)] at hq1
  have hI1 : CoreRefInv s₀ w s1 := hs1 ▸ hI0.splice (.inl (hst _ _ _ hq1 (by decide)))
  denote_step_all v 161
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s2 ⟨q2, b2, hq2, hs2⟩ => ?_
  simp only [Ctxt.Valuation.cons_succ] at hq2
  rw [valuation_append_right' _ _ _ _ (by decide)] at hq2
  have hI2 : CoreRefInv s₀ w s2 := hs2 ▸ hI1.splice (.inl (hst _ _ _ hq2 (by decide)))
  denote_step_all v 162
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s3 ⟨q3, b3, hq3, hs3⟩ => ?_
  simp only [Ctxt.Valuation.cons_succ] at hq3
  rw [valuation_append_right' _ _ _ _ (by decide)] at hq3
  have hI3 : CoreRefInv s₀ w s3 := hs3 ▸ hI2.splice (.inl (hst _ _ _ hq3 (by decide)))
  denote_step_all v 163
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s4 ⟨q4, b4, hq4, hs4⟩ => ?_
  simp only [Ctxt.Valuation.cons_succ] at hq4
  rw [valuation_append_right' _ _ _ _ (by decide)] at hq4
  have hI4 : CoreRefInv s₀ w s4 := hs4 ▸ hI3.splice (.inl (hst _ _ _ hq4 (by decide)))
  denote_step_all v 164
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s5 ⟨q5, b5, hq5, hs5⟩ => ?_
  simp only [Ctxt.Valuation.cons_succ] at hq5
  rw [valuation_append_right' _ _ _ _ (by decide)] at hq5
  have hI5 : CoreRefInv s₀ w s5 := hs5 ▸ hI4.splice (.inl (hst _ _ _ hq5 (by decide)))
  denote_step_all v 165
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s6 ⟨q6, b6, hq6, hs6⟩ => ?_
  simp only [Ctxt.Valuation.cons_succ] at hq6
  rw [valuation_append_right' _ _ _ _ (by decide)] at hq6
  have hI6 : CoreRefInv s₀ w s6 := hs6 ▸ hI5.splice (.inl (hst _ _ _ hq6 (by decide)))
  denote_step_all v 166
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s7 ⟨q7, b7, hq7, hs7⟩ => ?_
  simp only [Ctxt.Valuation.cons_succ] at hq7
  rw [valuation_append_right' _ _ _ _ (by decide)] at hq7
  have hI7 : CoreRefInv s₀ w s7 := hs7 ▸ hI6.splice (.inl (hst _ _ _ hq7 (by decide)))
  denote_step_all v 167
  refine walk_var_nil vacuous_poison (lifetime_expr_cases _ _ _ _) fun s8 hs8 => ?_
  denote_step_all v 169
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
  denote_number_from 61
  denote_step_all v 61
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x62 s62 hs62 => ?_
  have hI62 : CoreRefInv s₀ w s62 := hs62 ▸ hI
  refine walk_call_single vacuous_poison (bswap_call_cases _ _ hI62.1) fun x63 s63 he63 => ?_
  have hI63 := hI62.of_equiv he63
  denote_step_all v 64
  denote_eval v 64 64
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_st0 ⟨q_st0, b_st0, hq_st0, hs_st0⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero] at hq_st0
  rw [hv64] at hq_st0
  have hI_st0 : CoreRefInv s₀ w s_st0 := hs_st0 ▸ hI63.splice (.inr (le_id_of_gep hq_st0 fun p' hp' => by
    rw [valuation_append_right' _ _ _ _ (by decide)] at hp'
    exact hX _ _ _ hp' (by decide)))
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI_st0.1) fun x65 s65 he65 => ?_
  have hI65 := hI_st0.of_equiv he65
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI65.1) fun x66 s66 he66 => ?_
  have hI66 := hI65.of_equiv he66
  denote_step_all v 67
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI66.1) fun x68 s68 he68 => ?_
  have hI68 := hI66.of_equiv he68
  denote_step_all v 73
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x74 s74 hs74 => ?_
  have hI74 : CoreRefInv s₀ w s74 := hs74 ▸ hI68
  denote_step_all v 79
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI74.1) fun x80 s80 he80 => ?_
  have hI80 := hI74.of_equiv he80
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI80.1) fun x81 s81 he81 => ?_
  have hI81 := hI80.of_equiv he81
  denote_step_all v 82
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI81.1) fun x83 s83 he83 => ?_
  have hI83 := hI81.of_equiv he83
  denote_step_all v 93
  exact walk_term fun _ => hI83

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
  denote_number_from 103
  denote_step_all v 105
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x106 s106 hs106 => ?_
  have hI106 : CoreRefInv s₀ w s106 := hs106 ▸ hI
  denote_step_all v 109
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x110 s110 hs110 => ?_
  have hI110 : CoreRefInv s₀ w s110 := hs110 ▸ hI106
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI110.1) fun x111 s111 he111 => ?_
  have hI111 := hI110.of_equiv he111
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI111.1) fun x112 s112 he112 => ?_
  have hI112 := hI111.of_equiv he112
  denote_step_all v 115
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI112.1) fun x116 s116 he116 => ?_
  have hI116 := hI112.of_equiv he116
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI116.1) fun x117 s117 he117 => ?_
  have hI117 := hI116.of_equiv he117
  denote_step_all v 123
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x124 s124 hs124 => ?_
  have hI124 : CoreRefInv s₀ w s124 := hs124 ▸ hI117
  denote_step_all v 126
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x127 s127 hs127 => ?_
  have hI127 : CoreRefInv s₀ w s127 := hs127 ▸ hI124
  denote_step_all v 130
  denote_eval v 126 126
  refine walk_var_nil vacuous_poison (store_expr_cases _ _ _ _ _) fun s_st0 ⟨q_st0, b_st0, hq_st0, hs_st0⟩ => ?_
  simp only [Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_succ] at hq_st0
  rw [hv126] at hq_st0
  have hI_st0 : CoreRefInv s₀ w s_st0 := hs_st0 ▸ hI127.splice (.inr (le_id_of_gep hq_st0 fun p' hp' => by
    rw [valuation_append_right' _ _ _ _ (by decide)] at hp'
    exact hX _ _ _ hp' (by decide)))
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI_st0.1) fun x131 s131 he131 => ?_
  have hI131 := hI_st0.of_equiv he131
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI131.1) fun x132 s132 he132 => ?_
  have hI132 := hI131.of_equiv he132
  denote_step_all v 133
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI132.1) fun x134 s134 he134 => ?_
  have hI134 := hI132.of_equiv he134
  denote_step_all v 139
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x140 s140 hs140 => ?_
  have hI140 : CoreRefInv s₀ w s140 := hs140 ▸ hI134
  denote_step_all v 145
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI140.1) fun x146 s146 he146 => ?_
  have hI146 := hI140.of_equiv he146
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI146.1) fun x147 s147 he147 => ?_
  have hI147 := hI146.of_equiv he147
  denote_step_all v 148
  refine walk_call_single vacuous_poison (rotr_call_cases _ _ hI147.1) fun x149 s149 he149 => ?_
  have hI149 := hI147.of_equiv he149
  denote_step_all v 158
  exact walk_term fun _ => hI149

/-- All five loop blocks at once, in exactly `Blocks.run_inv`'s step shape. -/
theorem core_loop_step (Vamb : fd_sha512_core_ref.Γout.Valuation) (s₀ : GlobalState) (w : BlockId)
    (hX : ∀ (m : Nat) (h : fd_sha512_core_ref.Γout[m]? = some SLLVM.Ty.ptr) (q : Pointer),
      Vamb ⟨m, h⟩ = PoisonOr.value q → m = 15 → s₀.alloc.nextFreeBlock ≤ q.id.id)
    (hst : ∀ (m : Nat) (h : fd_sha512_core_ref.Γout[m]? = some SLLVM.Ty.ptr) (q : Pointer),
      Vamb ⟨m, h⟩ = PoisonOr.value q → m ∈ [8, 9, 10, 11, 12, 13, 14, 44] → q.id = w) :
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
  denote_step_all v 13
  refine walk_var_single vacuous_poison (addressof_expr_cases _ _ _) fun x14 s14 hs14 => ?_
  denote_step_all v 25
  refine walk_var_single vacuous_poison (alloca_expr_cases _ _ _) fun x26 s26 ⟨hx26, hs26⟩ => ?_
  have hI26 : CoreRefInv s w s26 := by rw [hs26, hs14]; exact CoreRefInv.afterAlloca hs w _
  denote_step_all v 33
  denote_eval v 27 33
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x34 s34 hs34 => ?_
  have hI34 : CoreRefInv s w s34 := hs34 ▸ hI26
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x35 s35 hs35 => ?_
  have hI35 : CoreRefInv s w s35 := hs35 ▸ hI34
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x36 s36 hs36 => ?_
  have hI36 : CoreRefInv s w s36 := hs36 ▸ hI35
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x37 s37 hs37 => ?_
  have hI37 : CoreRefInv s w s37 := hs37 ▸ hI36
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x38 s38 hs38 => ?_
  have hI38 : CoreRefInv s w s38 := hs38 ▸ hI37
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x39 s39 hs39 => ?_
  have hI39 : CoreRefInv s w s39 := hs39 ▸ hI38
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x40 s40 hs40 => ?_
  have hI40 : CoreRefInv s w s40 := hs40 ▸ hI39
  refine walk_var_single vacuous_poison (load_expr_cases _ _ _ _) fun x41 s41 hs41 => ?_
  have hI41 : CoreRefInv s w s41 := hs41 ▸ hI40
  -- the branch into `^bb1`: from here the walk is `Blocks.run`, and the loop rule
  refine ⟨_, rfl, fun p t h => ?_⟩
  simp only [BlockCom.denote_term, Terminator.denote_br, pure_bind] at h
  refine Blocks.run_inv (CoreRefInv s w) (fun _ t => CoreRefInv s w t)
    (core_loop_step _ s w ?_ ?_) hI41 p t h
  · -- `%26`, the round buffer, sits at the entry counter
    intro m hm q hq he
    subst he
    simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
    rw [hx26, PoisonOr.value_inj] at hq
    rw [← hq, hs14]
  · -- the hash-state pointers: `%arg0` and its seven geps `%27`–`%33`
    intro m hm q hq he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
      rw [hv33] at hq
      obtain ⟨p', hp', hid⟩ := gep_eq_value hq
      rw [PoisonOr.value_inj] at hp'
      rw [hid, ← hp', hw]
    · simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
      rw [hv32] at hq
      obtain ⟨p', hp', hid⟩ := gep_eq_value hq
      rw [PoisonOr.value_inj] at hp'
      rw [hid, ← hp', hw]
    · simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
      rw [hv31] at hq
      obtain ⟨p', hp', hid⟩ := gep_eq_value hq
      rw [PoisonOr.value_inj] at hp'
      rw [hid, ← hp', hw]
    · simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
      rw [hv30] at hq
      obtain ⟨p', hp', hid⟩ := gep_eq_value hq
      rw [PoisonOr.value_inj] at hp'
      rw [hid, ← hp', hw]
    · simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
      rw [hv29] at hq
      obtain ⟨p', hp', hid⟩ := gep_eq_value hq
      rw [PoisonOr.value_inj] at hp'
      rw [hid, ← hp', hw]
    · simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
      rw [hv28] at hq
      obtain ⟨p', hp', hid⟩ := gep_eq_value hq
      rw [PoisonOr.value_inj] at hp'
      rw [hid, ← hp', hw]
    · simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero] at hq
      rw [hv27] at hq
      obtain ⟨p', hp', hid⟩ := gep_eq_value hq
      rw [PoisonOr.value_inj] at hp'
      rw [hid, ← hp', hw]
    · simp only [Ctxt.Valuation.cons_succ, Ctxt.Valuation.cons_zero,
        Ctxt.Valuation.ofHVector_cons] at hq
      rw [PoisonOr.value_inj] at hq
      rw [← hq, hw]

end Firedancer.Common
