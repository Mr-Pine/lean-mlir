/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Proof.SHA.fd_sha512_core_ref
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_memset
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_memcpy

/-!
# What the SHA-512 callees do to memory, whatever their arguments

The outcome of each callee as the walk combinators consume it: UB, or a
returned state that is well formed and differs from the caller's only in the
block the callee writes. Unlike the conformance theorems these take arbitrary
argument valuations -- a caller's operands are registers that may be poison --
and say nothing about the values written.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `fd_sha512_core_ref`: only the hash state's block changes. -/
theorem core_ref_call_cases (cnt : LLVM.IntW 64) (blk : SLLVM.Ptr) (st : Pointer)
    (s : GlobalState) (hs : s.WF) :
    StateT.run (runFunction (Cfg.denote ⟨fd_sha512_core_ref.entry, fd_sha512_core_ref.blocks⟩
        (Ctxt.Valuation.ofHVector [cnt, blk, .value st]ₕ))) s = .poison
      ∨ ∃ s₁, StateT.run (runFunction (Cfg.denote ⟨fd_sha512_core_ref.entry, fd_sha512_core_ref.blocks⟩
          (Ctxt.Valuation.ofHVector [cnt, blk, .value st]ₕ))) s = .value (.nil, s₁)
        ∧ s₁.WF ∧ ∀ b : BlockId, b ≠ st.id → s₁.mem.live? b = s.mem.live? b := by
  obtain ⟨res, hres, h⟩ := fd_sha512_core_ref_frame st blk cnt s hs
  cases res with
  | poison => exact .inl hres
  | value p =>
      obtain ⟨r, s₁⟩ := p
      obtain ⟨hwf, -, -, hlive⟩ := h r s₁ rfl
      cases r
      exact .inr ⟨s₁, hres, hwf, hlive⟩

/-- A three-argument valuation is the `ofHVector` of its entries. -/
theorem valuation_eq_ofHVector3 {a b c : SLLVM.Ty} (W : (Ctxt.ofList [a, b, c]).Valuation) :
    W = Ctxt.Valuation.ofHVector [W ⟨0, rfl⟩, W ⟨1, rfl⟩, W ⟨2, rfl⟩]ₕ := by
  funext t v
  rcases v with ⟨_ | _ | _ | n, h⟩
  · simp at h; subst h; rfl
  · simp at h; subst h; rfl
  · simp at h; subst h; rfl
  · simp at h

/-- `core_ref_call_cases` for any argument valuation whose state entry is a
known pointer: the form a call site's operands come in. -/
theorem core_ref_call_cases' (W : (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.ptr]).Valuation)
    (st : Pointer) (hW : W ⟨2, rfl⟩ = .value st) (s : GlobalState) (hs : s.WF) :
    StateT.run (runFunction (Cfg.denote ⟨fd_sha512_core_ref.entry, fd_sha512_core_ref.blocks⟩ W)) s
        = .poison
      ∨ ∃ s₁, StateT.run (runFunction
          (Cfg.denote ⟨fd_sha512_core_ref.entry, fd_sha512_core_ref.blocks⟩ W)) s = .value (.nil, s₁)
        ∧ s₁.WF ∧ ∀ b : BlockId, b ≠ st.id → s₁.mem.live? b = s.mem.live? b := by
  rw [valuation_eq_ofHVector3 W, hW]
  exact core_ref_call_cases _ _ st s hs

/-- `fd_memset`: only the destination's block changes. -/
theorem memset_call_cases (W : (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr]).Valuation)
    (s : GlobalState) (hs : s.WF) :
    StateT.run (runFunction (Cfg.denote ⟨fd_memset.entry, fd_memset.blocks⟩ W)) s = .poison
      ∨ ∃ x s₁, StateT.run (runFunction (Cfg.denote ⟨fd_memset.entry, fd_memset.blocks⟩ W)) s
          = .value ([x]ₕ, s₁)
        ∧ ∃ q : Pointer, W ⟨1, rfl⟩ = .value q ∧ s₁.WF
          ∧ ∀ b : BlockId, b ≠ q.id → s₁.mem.live? b = s.mem.live? b := by
  have key : ∃ res, StateT.run (Cfg.denote ⟨fd_memset.entry, fd_memset.blocks⟩ W) s = res
      ∧ ∀ p t, res = .value (p, t) →
        ∃ q : Pointer, W ⟨1, rfl⟩ = .value q ∧ FrameInv s (· = q.id) t := by
    simp only [Cfg.denote]
    denote_step_all v 0
    refine walk_var_nil vacuous_poison (memset_expr_cases _ _ _ _ _) fun s1 ⟨q, n, x, hq, hs1⟩ => ?_
    refine walk_ret ⟨_, rfl, fun p t h => ?_⟩
    dsimp only at h
    rw [EffectM.run_pure, PoisonOr.value_inj, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp only [Ctxt.Valuation.cons_succ] at hq
    exact ⟨q, hq, hs1 ▸ (FrameInv.refl hs _).splice (.inl rfl)⟩
  obtain ⟨res, hres, hpost⟩ := key
  cases res with
  | poison => exact .inl (run_runFunction_poison hres)
  | value pt =>
      obtain ⟨p, t⟩ := pt
      obtain ⟨q, hq, hI⟩ := hpost p t rfl
      obtain ⟨hwf, -, -, hlive⟩ := popFrame_frameInv hs hI
      cases p with
      | cons x rest =>
          cases rest
          exact .inr ⟨x, _, run_runFunction hres, q, hq, hwf, hlive⟩

/-- `fd_memcpy`: only the destination's block changes. -/
theorem memcpy_call_cases
    (W : (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.ptr]).Valuation)
    (s : GlobalState) (hs : s.WF) :
    StateT.run (runFunction (Cfg.denote ⟨fd_memcpy.entry, fd_memcpy.blocks⟩ W)) s = .poison
      ∨ ∃ x s₁, StateT.run (runFunction (Cfg.denote ⟨fd_memcpy.entry, fd_memcpy.blocks⟩ W)) s
          = .value ([x]ₕ, s₁)
        ∧ ∃ q : Pointer, W ⟨2, rfl⟩ = .value q ∧ s₁.WF
          ∧ ∀ b : BlockId, b ≠ q.id → s₁.mem.live? b = s.mem.live? b := by
  have key : ∃ res, StateT.run (Cfg.denote ⟨fd_memcpy.entry, fd_memcpy.blocks⟩ W) s = res
      ∧ ∀ p t, res = .value (p, t) →
        ∃ q : Pointer, W ⟨2, rfl⟩ = .value q ∧ FrameInv s (· = q.id) t := by
    simp only [Cfg.denote]
    refine walk_var_nil vacuous_poison (memcpy_expr_cases _ _ _ _ _) fun s1 ⟨q, n, x, hq, hs1⟩ => ?_
    refine walk_ret ⟨_, rfl, fun p t h => ?_⟩
    dsimp only at h
    rw [EffectM.run_pure, PoisonOr.value_inj, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨q, hq, hs1 ▸ (FrameInv.refl hs _).splice (.inl rfl)⟩
  obtain ⟨res, hres, hpost⟩ := key
  cases res with
  | poison => exact .inl (run_runFunction_poison hres)
  | value pt =>
      obtain ⟨p, t⟩ := pt
      obtain ⟨q, hq, hI⟩ := hpost p t rfl
      obtain ⟨hwf, -, -, hlive⟩ := popFrame_frameInv hs hI
      cases p with
      | cons x rest =>
          cases rest
          exact .inr ⟨x, _, run_runFunction hres, q, hq, hwf, hlive⟩

end Firedancer.Common
