/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_sub_with_opts
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_neg_precomputed
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_add_with_opts
import SSA.Projects.Firedancer.Proof.WriteChain

/-!
# `fd_ed25519_point_sub_with_opts` conformance (AVX-512)

`b_is_precomputed = 1`: `fd_ed25519_point_neg_precomputed` into the local `t`,
then `fd_ed25519_point_add_with_opts( r, a, t )`, then `t`'s frame is popped.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

namespace PointSub

theorem negPre_step {t b : Pointer} {w : GlobalState} (hw : w.WF) (hne : t.id ≠ b.id)
    (ht : IsQuadPtr w.mem t) (hb : IsQuadPtr w.mem b) (h03 : R43x6.U44 (readQuad hb).v03)
    (h14 : R43x6.U44 (readQuad hb).v14) (h25 : R43x6.U44 (readQuad hb).v25)
    (hn : (readQuad hb).NegBounds 3) {P : Prop}
    (k : ∀ w' q, StateT.run (runFunction (fd_ed25519_point_neg_precomputed.denote
        (Ctxt.Valuation.ofHVector [.value b, .value t]ₕ))) w = .value ([.value t]ₕ, w') →
      ({ w with mem := w.mem.writeQuad t q } : GlobalState) ≈ w' →
      PrecomputedPoint.ofSlots q.toPoint = (PrecomputedPoint.ofSlots (readQuad hb).toPoint).neg →
      R43x6.U44 q.v03 → R43x6.U44 q.v14 → R43x6.U44 q.v25 → P) : P := by
  obtain ⟨w', hrun, q, he, hpt, hu03, hu14, hu25⟩ :=
    fd_ed25519_point_neg_precomputed_conforms t b w hw hne ht hb h03 h14 h25 hn
  exact k w' q hrun he hpt hu03 hu14 hu25

theorem add_step {r a b : Pointer} {w : GlobalState} (hw : w.WF) (hr : IsQuadPtr w.mem r)
    (ha : IsQuadPtr w.mem a) (hb : IsQuadPtr w.mem b)
    (ha03 : R43x6.U44 (readQuad ha).v03) (ha14 : R43x6.U44 (readQuad ha).v14)
    (ha25 : R43x6.U44 (readQuad ha).v25) (hb03 : R43x6.U44 (readQuad hb).v03)
    (hb14 : R43x6.U44 (readQuad hb).v14) (hb25 : R43x6.U44 (readQuad hb).v25) {P : Prop}
    (k : ∀ w' q, StateT.run (runFunction (fd_ed25519_point_add_with_opts.denote
        (Ctxt.Valuation.ofHVector [.value 1, .value b, .value a, .value r]ₕ))) w
        = .value ([.value r]ₕ, w') →
      ({ w with mem := w.mem.writeQuad r q } : GlobalState) ≈ w' →
      q.toPoint = (readQuad ha).toPoint.addPrecomputed (PrecomputedPoint.ofSlots (readQuad hb).toPoint) →
      R43x6.U44 q.v03 → R43x6.U44 q.v14 → R43x6.U44 q.v25 → P) : P := by
  obtain ⟨w', hrun, q, he, hpt, hu03, hu14, hu25⟩ :=
    fd_ed25519_point_add_with_opts_conforms r a b 1 w hw hr ha hb rfl ha03 ha14 ha25 hb03 hb14 hb25
  exact k w' q hrun he hpt hu03 hu14 hu25

end PointSub

open PointSub Ge in
theorem fd_ed25519_point_sub_with_opts_conforms (r a b : Pointer) (bPre : BitVec 32)
    (s : GlobalState) (hs : s.WF) (hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a)
    (hb : IsQuadPtr s.mem b) :
    fd_ed25519_point_sub_with_opts_spec r a b bPre s hr ha hb := by
  simp only [fd_ed25519_point_sub_with_opts_spec, Cfg.denote]
  intro hpre ha03 ha14 ha25 hb03 hb14 hb25 hbn
  subst hpre
  refine run_runFunction' _ ?_
  denote_step_reduce v 1 [LLVM.const?] fold

  -- `%2`: `t`, on the entry counter
  refine name_of (s.afterAlloca (3 * 8 * 64)) fun sA hsA => ?_
  peel_alloca from s as sA with hsA.symm
  peel_lifetime

  -- `%3`: `b_is_precomputed == 0`
  denote_step_reduce v 3 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', hv1]
  simp only [BlockCom.denote_term]
  rw [Terminator.denote_condBr_value (by exact hv3)]
  simp only [simp_denote, simp_sllvm]
  rw [if_neg (by decide : ¬ ((0#1 : BitVec 1) = 1))]

  -- `^bb1`: `t = -b`
  denote_enter_block
  denote_number_from 4
  have hnb := lt_nextFreeBlock_of_fits hs hb.1
  have hlA : ∀ c : BlockId, c.id < s.alloc.nextFreeBlock → sA.mem.live? c = s.mem.live? c :=
    fun _ hc => hsA ▸ live?_afterAlloca_of_lt hc
  have htn : ∀ c : BlockId, c.id < s.alloc.nextFreeBlock →
      (⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ : Pointer).id ≠ c :=
    fun c hc h => by subst h; simp at hc
  have hwA : sA.WF := hsA ▸ hs.afterAlloca _
  have htA : IsQuadPtr sA.mem ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ :=
    hsA ▸ ⟨fits_afterAlloca s _, by simp⟩
  have hbA : IsQuadPtr sA.mem b := ⟨fits_of_live?_eq (hlA _ hnb) hb.1, hb.2⟩
  have eb : readQuad hbA = readQuad hb := readQuad_of_live?_eq (hlA _ hnb) hb hbA
  refine negPre_step hwA (htn _ hnb) htA hbA (eb ▸ hb03) (eb ▸ hb14) (eb ▸ hb25) (eb ▸ hbn)
    fun s₁ qn hrun₁ he₁ hpt₁ hn03 hn14 hn25 => ?_
  set_option backward.isDefEq.respectTransparency false in peel_call hrun₁
  simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]

  -- `^bb3`: `r = a + t`
  denote_enter_block
  denote_number_from 6
  have hnr := lt_nextFreeBlock_of_fits hs hr.1
  have hna := lt_nextFreeBlock_of_fits hs ha.1
  have hl₁ : ∀ c : BlockId, c.id < s.alloc.nextFreeBlock → s₁.mem.live? c = s.mem.live? c :=
    fun c hc => (live?_of_equiv_mem' (GlobalState.Equiv.symm he₁) c).trans
      ((live?_writeQuad_ne (htn c hc)).trans (hlA c hc))
  have htW : IsQuadPtr (sA.mem.writeQuad ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ qn)
      ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ :=
    ⟨fits_splice (fits_splice (fits_splice htA.1)), htA.2⟩
  have hwW : ({ sA with mem := sA.mem.writeQuad ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ qn }
      : GlobalState).WF := fun c hc => by
    simp only [MemoryState.writeQuad]
    exact live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none (hwA c hc)))
  have hr₁ : IsQuadPtr s₁.mem r := ⟨fits_of_live?_eq (hl₁ _ hnr) hr.1, hr.2⟩
  have ha₁ : IsQuadPtr s₁.mem a := ⟨fits_of_live?_eq (hl₁ _ hna) ha.1, ha.2⟩
  have ht₁ : IsQuadPtr s₁.mem ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ :=
    ⟨fits_of_live?_eq (live?_of_equiv_mem' (GlobalState.Equiv.symm he₁) _) htW.1, htA.2⟩
  have ea : readQuad ha₁ = readQuad ha := readQuad_of_live?_eq (hl₁ _ hna) ha ha₁
  have et : readQuad ht₁ = qn :=
    (readQuad_of_live?_eq (live?_of_equiv_mem' (GlobalState.Equiv.symm he₁) _) htW ht₁).trans
      (readQuad_writeQuad htA htW)
  refine add_step (hwW.of_equiv he₁) hr₁ ha₁ ht₁ (ea ▸ ha03) (ea ▸ ha14) (ea ▸ ha25)
    (et ▸ hn03) (et ▸ hn14) (et ▸ hn25) fun s₂ qo hrun₂ he₂ hpt₂ ho03 ho14 ho25 => ?_
  peel_call hrun₂
  peel_lifetime
  refine ⟨s₂, by simp_return, ?_⟩

  /- The region has returned: `r`'s block as `add_with_opts` left it, `t`'s popped. -/
  have hpop := popFrame_equiv_block hs hnr
    (fun c hc hcr => (live?_of_equiv_mem' (GlobalState.Equiv.symm he₂) c).trans
      ((live?_writeQuad_ne (Ne.symm hcr)).trans (hl₁ c hc)))
    (fun _ hcr => live?_writeQuad_ne (Ne.symm hcr))
    ((live?_of_equiv_mem' (GlobalState.Equiv.symm he₂) r.id).trans
      (live?_writeQuad_congr qo (hl₁ _ hnr)))
  refine ⟨qo, GlobalState.Equiv.symm hpop, by rw [hpt₂, ea, et, hpt₁, eb], ho03, ho14, ho25⟩

end Firedancer.Avx512
