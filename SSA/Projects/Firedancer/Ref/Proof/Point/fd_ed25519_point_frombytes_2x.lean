/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_point_frombytes_2x
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_frombytes

/-!
# `fd_ed25519_point_frombytes_2x` conforms to its spec

Two calls, each null-checked. Everything the points satisfy comes from
`fd_ed25519_point_frombytes_conforms`; what is proved here is the
short-circuit -- which of `0`, `-1`, `-2` comes back, and that a failing first
call writes nothing.

The three `run_*` lemmas are the region's three paths. They are separate
declarations because each walks the whole CFG, and the walks share no work.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/- Scaffolding for the `fd_ed25519_point_frombytes_2x` derivation. -/
namespace PointFromBytes2x

section Run
variable {s w₁ w₂ : GlobalState} {r₁ buf₁ r₂ buf₂ : Pointer} {ret₁ ret₂ : SLLVM.Ptr}

/-- The first call's run equation, in the shape both paths take it. -/
abbrev Ran (r buf : Pointer) (ret : SLLVM.Ptr) (u u' : GlobalState) : Prop :=
  StateT.run (runFunction (fd_ed25519_point_frombytes.denote
    (Ctxt.Valuation.ofHVector [.value buf, .value r]ₕ))) u = .value ([ret]ₕ, u')

/-- `NULL` from the first call: `-1`, and the second call never runs. -/
theorem run_fail₁ (hrun₁ : Ran r₁ buf₁ ret₁ s w₁) (hret₁ : ret₁ = SLLVM.Ptr.null) :
    ∃ t : GlobalState,
      StateT.run (runFunction (fd_ed25519_point_frombytes_2x.denote
          (Ctxt.Valuation.ofHVector
            [.value buf₂, .value r₂, .value buf₁, .value r₁]ₕ))) s
        = .value ([(.value (-1 : BitVec 32) : LLVM.IntW 32)]ₕ, t)
      ∧ t = s.popFrame w₁.mem := by
  simp only [Cfg.denote]
  refine run_runFunction' _ ?_
  denote_step_reduce v 3 [LLVM.const?] fold
  peel_call hrun₁
  denote_step_reduce v 5 [hv3, hret₁]
  simp only [SLLVM.null_eq_value, SLLVM.ptricmp_value, beq_self_eq_true, if_pos] at hv5
  simp only [hv5, BlockCom.denote_term, Terminator.denote_condBr_value,
    simp_denote, simp_sllvm]
  denote_enter_block
  simp_return
  exact hv2

/-- Both calls made, the second returning `NULL`: `-2`. -/
theorem run_fail₂ (hrun₁ : Ran r₁ buf₁ ret₁ s w₁) (hret₁ : ret₁ = .value r₁)
    (hnull₁ : r₁.id ≠ SLLVM.nullBlock)
    (hrun₂ : Ran r₂ buf₂ ret₂ w₁ w₂) (hret₂ : ret₂ = SLLVM.Ptr.null) :
    ∃ t : GlobalState,
      StateT.run (runFunction (fd_ed25519_point_frombytes_2x.denote
          (Ctxt.Valuation.ofHVector
            [.value buf₂, .value r₂, .value buf₁, .value r₁]ₕ))) s
        = .value ([(.value (-2 : BitVec 32) : LLVM.IntW 32)]ₕ, t)
      ∧ t = s.popFrame w₂.mem := by
  simp only [Cfg.denote]
  refine run_runFunction' _ ?_
  denote_step_reduce v 3 [LLVM.const?] fold
  peel_call hrun₁
  denote_step_reduce v 5 [hv3, hret₁]
  have hrnull : ¬ (r₁ = (⟨SLLVM.nullBlock, 0#64⟩ : Pointer)) := fun h => hnull₁ (by rw [h])
  simp only [SLLVM.null_eq_value, SLLVM.ptricmp_value, beq_iff_eq, hrnull, if_false] at hv5
  simp only [hv5, BlockCom.denote_term, Terminator.denote_condBr_value,
    simp_denote, simp_sllvm]
  denote_enter_block
  peel_call hrun₂
  -- the stepper counts the entry block's four arguments, so `^bb1`'s
  -- `%6 … %8` are `v10 … v12`
  denote_step_reduce v 11 [hv3, hret₂]
  denote_step_reduce v 12 [hv11, hv1, hv0]
  simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
  denote_enter_block
  simp_return
  exact hv12

/-- Both calls decoding: `0`. -/
theorem run_ok (hrun₁ : Ran r₁ buf₁ ret₁ s w₁) (hret₁ : ret₁ = .value r₁)
    (hnull₁ : r₁.id ≠ SLLVM.nullBlock)
    (hrun₂ : Ran r₂ buf₂ ret₂ w₁ w₂) (hret₂ : ret₂ = .value r₂)
    (hnull₂ : r₂.id ≠ SLLVM.nullBlock) :
    ∃ t : GlobalState,
      StateT.run (runFunction (fd_ed25519_point_frombytes_2x.denote
          (Ctxt.Valuation.ofHVector
            [.value buf₂, .value r₂, .value buf₁, .value r₁]ₕ))) s
        = .value ([(.value (0 : BitVec 32) : LLVM.IntW 32)]ₕ, t)
      ∧ t = s.popFrame w₂.mem := by
  simp only [Cfg.denote]
  refine run_runFunction' _ ?_
  denote_step_reduce v 3 [LLVM.const?] fold
  peel_call hrun₁
  denote_step_reduce v 5 [hv3, hret₁]
  have hrnull₁ : ¬ (r₁ = (⟨SLLVM.nullBlock, 0#64⟩ : Pointer)) := fun h => hnull₁ (by rw [h])
  simp only [SLLVM.null_eq_value, SLLVM.ptricmp_value, beq_iff_eq, hrnull₁, if_false] at hv5
  simp only [hv5, BlockCom.denote_term, Terminator.denote_condBr_value,
    simp_denote, simp_sllvm]
  denote_enter_block
  peel_call hrun₂
  have hrnull₂ : ¬ (r₂ = (⟨SLLVM.nullBlock, 0#64⟩ : Pointer)) := fun h => hnull₂ (by rw [h])
  denote_step_reduce v 11 [hv3, hret₂]
  simp only [SLLVM.null_eq_value, SLLVM.ptricmp_value, beq_iff_eq, hrnull₂, if_false] at hv11
  denote_step_reduce v 12 [hv11, hv1, hv0]
  simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
  denote_enter_block
  simp_return
  exact hv12

end Run

/-- `DecodesTo` looks only at `r`'s and `buf`'s blocks, so it carries between
a callee's returned state and the memory the caller states it over. -/
theorem decodesTo_of_equiv {w s : GlobalState} {m : MemoryState} {r buf : Pointer}
    {oX oY oZ oT : Fin 5 → BitVec 64}
    (he : w ≈ ({ s with mem := m } : GlobalState))
    {hr : IsPointPtr w.mem r} {hbuf : IsByteBufPtr w.mem buf}
    {hr' : IsPointPtr m r} {hbuf' : IsByteBufPtr m buf}
    (h : DecodesTo w.mem r buf hr hbuf oX oY oZ oT) :
    DecodesTo m r buf hr' hbuf' oX oY oZ oT := by
  have hlive := live?_pointOutMem_congr (oX := oX) (oY := oY) (oZ := oZ) (oT := oT)
    (live?_of_equiv_mem he r.id)
  have hpoint := readPoint_of_live?_eq hlive (isPointPtr_pointOutMem hr' oX oY oZ oT)
    (isPointPtr_pointOutMem hr oX oY oZ oT)
  have hbytes := readBuf_of_equiv (h := hbuf) (h' := hbuf') he
  unfold DecodesTo at h ⊢
  rw [← hpoint, ← hbytes]
  exact h

/-- ... and so does `DecodedBounds`. -/
theorem decodedBounds_of_equiv {w s : GlobalState} {m : MemoryState} {r : Pointer}
    {oX oY oZ oT : Fin 5 → BitVec 64}
    (he : w ≈ ({ s with mem := m } : GlobalState))
    {hr : IsPointPtr w.mem r} {hr' : IsPointPtr m r}
    (h : DecodedBounds w.mem r hr oX oY oZ oT) : DecodedBounds m r hr' oX oY oZ oT := by
  have hlive : ∀ o : BitVec 64, (pointOutMem m r oX oY oZ oT).live? (r.withOffset o).id
      = (pointOutMem w.mem r oX oY oZ oT).live? (r.withOffset o).id := fun o => by
    rw [withOffset_id]
    exact (live?_pointOutMem_congr (live?_of_equiv_mem he r.id)).symm
  exact ⟨PointFromBytes.copyBound rfl (hlive _) (fun _ => rfl) h.1,
    PointFromBytes.copyBound rfl (hlive _) (fun _ => rfl) h.2.1,
    PointFromBytes.copyBound rfl (hlive _) (fun _ => rfl) h.2.2.1,
    PointFromBytes.copyBound rfl (hlive _) (fun _ => rfl) h.2.2.2.1,
    ZeroRep.of_readLimb? (fun i => readLimb?_of_live?_eq
      (live?_pointOutMem_congr (live?_of_equiv_mem he r.id)).symm i) h.2.2.2.2⟩

/-- Only the first call wrote: the popped state is the entry state with `r₁`'s
four stores. The side conditions are named `have`s -- left as `refine`
placeholders they elaborate against a metavariable, and the four splices are
walked twice over. -/
theorem out_fail₂ {s w₁ w₂ : GlobalState} {r₁ : Pointer} {oX oY oZ oT : Fin 5 → BitVec 64}
    (hs : s.WF) (hn₁ : r₁.id.id < s.alloc.nextFreeBlock)
    (heq₁ : w₁ ≈ ({ s with mem := pointOutMem s.mem r₁ oX oY oZ oT } : GlobalState))
    (heq₂ : w₁ ≈ w₂) :
    s.popFrame w₂.mem
      ≈ ({ s with mem := pointOutMem s.mem r₁ oX oY oZ oT } : GlobalState) := by
  have hfm : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → b ≠ r₁.id →
      w₂.mem.live? b = s.mem.live? b := fun b _ hb =>
    (live?_of_equiv_mem heq₂ b).symm.trans ((live?_of_equiv_mem heq₁ b).trans (live?_pointOutMem_ne (Ne.symm hb)))
  have hfn : ∀ b : BlockId, b ≠ r₁.id →
      (pointOutMem s.mem r₁ oX oY oZ oT).live? b = s.mem.live? b :=
    fun b hb => live?_pointOutMem_ne (Ne.symm hb)
  exact popFrame_equiv_block hs hn₁ hfm hfn
    ((heq₂.live r₁.id).symm.trans (live?_of_equiv_mem heq₁ r₁.id))

/-- Both calls wrote: `r₂`'s stores land on top of `r₁`'s. The two may be the
same block, which is why the readback goes by cases on `b = r₂.id` rather than
on which write a block belongs to. -/
theorem out_ok {s w₁ w₂ : GlobalState} {r₁ r₂ : Pointer}
    {oX oY oZ oT pX pY pZ pT : Fin 5 → BitVec 64}
    (hs : s.WF) (hn₁ : r₁.id.id < s.alloc.nextFreeBlock)
    (hn₂ : r₂.id.id < s.alloc.nextFreeBlock)
    (heq₁ : w₁ ≈ ({ s with mem := pointOutMem s.mem r₁ oX oY oZ oT } : GlobalState))
    (heq₂ : w₂ ≈ ({ w₁ with mem := pointOutMem w₁.mem r₂ pX pY pZ pT } : GlobalState)) :
    s.popFrame w₂.mem ≈ ({ s with
      mem := pointOutMem (pointOutMem s.mem r₁ oX oY oZ oT) r₂ pX pY pZ pT }
        : GlobalState) := by
  have hm₁ : ∀ b : BlockId, b ≠ r₁.id → w₁.mem.live? b = s.mem.live? b := fun b hb =>
    (live?_of_equiv_mem heq₁ b).trans (live?_pointOutMem_ne (Ne.symm hb))
  have hbelow : ∀ b : BlockId, (b = r₁.id ∨ b = r₂.id) → b.id < s.alloc.nextFreeBlock :=
    fun b hb => by rcases hb with rfl | rfl <;> assumption
  have hfm : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → ¬ (b = r₁.id ∨ b = r₂.id) →
      w₂.mem.live? b = s.mem.live? b := fun b _ hb =>
    ((live?_of_equiv_mem heq₂ b).trans (live?_pointOutMem_ne (Ne.symm (fun h => hb (Or.inr h))))).trans
      (hm₁ b (fun h => hb (Or.inl h)))
  have hfn : ∀ b : BlockId, ¬ (b = r₁.id ∨ b = r₂.id) →
      (pointOutMem (pointOutMem s.mem r₁ oX oY oZ oT) r₂ pX pY pZ pT).live? b
        = s.mem.live? b := fun b hb =>
    (live?_pointOutMem_ne (Ne.symm (fun h => hb (Or.inr h)))).trans
      (live?_pointOutMem_ne (Ne.symm (fun h => hb (Or.inl h))))
  have hval : ∀ b : BlockId, (b = r₁.id ∨ b = r₂.id) → w₂.mem.live? b
      = (pointOutMem (pointOutMem s.mem r₁ oX oY oZ oT) r₂ pX pY pZ pT).live? b := by
    intro b _
    rw [live?_of_equiv_mem heq₂ b]
    by_cases hb₂ : b = r₂.id
    · subst hb₂
      exact live?_pointOutMem_congr (live?_of_equiv_mem heq₁ r₂.id)
    · rw [live?_pointOutMem_ne (Ne.symm hb₂), live?_pointOutMem_ne (Ne.symm hb₂)]
      exact live?_of_equiv_mem heq₁ b
  exact popFrame_equiv_written _ hs hbelow hfm hfn hval

/-- The `sq₁` half of the conformance theorem: its own declaration, since the
two paths through `^bb1` do not share a heartbeat budget with the `^bb0`
one. -/
theorem conforms_of_isSquare (r₁ buf₁ r₂ buf₂ : Pointer) (s : GlobalState)
    (hm : s.RefWF [r₁, r₂])
    (hr₁ : IsPointPtr s.mem r₁) (hbuf₁ : IsByteBufPtr s.mem buf₁)
    (hr₂ : IsPointPtr s.mem r₂) (hbuf₂ : IsByteBufPtr s.mem buf₂)
    (hbufr₁ : buf₁.id ≠ r₁.id) (hbufr₂ : buf₂.id ≠ r₂.id)
    (hnull₁ : r₁.id ≠ SLLVM.nullBlock) (hnull₂ : r₂.id ≠ SLLVM.nullBlock)
    (sq₁ : IsSquare ((decodeBytes (readBuf hbuf₁) ^ 2 - 1)
      / (d * decodeBytes (readBuf hbuf₁) ^ 2 + 1))) :
    fd_ed25519_point_frombytes_2x_spec r₁ buf₁ r₂ buf₂ s hr₁ hbuf₁ hr₂ hbuf₂ := by
  simp only [fd_ed25519_point_frombytes_2x_spec]
  obtain ⟨w₁, ret₁, hrun₁, oX, oY, oZ, oT, hfail₁, hok₁⟩ :=
    fd_ed25519_point_frombytes_conforms r₁ buf₁ s (hm.mono (by simp)) hr₁ hbuf₁ hbufr₁
  have hn₁ : r₁.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hm.wf hr₁.left
  have hn₂ : r₂.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hm.wf hr₂.left

  -- `^bb1`: the first point decoded, so the second call runs on what it left
  obtain ⟨hret₁, heq₁, hdec₁, hbnd₁⟩ := hok₁ sq₁
  have hlive₁ : ∀ b : BlockId, b ≠ r₁.id → w₁.mem.live? b = s.mem.live? b := fun b hb =>
    (live?_of_equiv_mem heq₁ b).trans (live?_pointOutMem_ne (Ne.symm hb))
  -- `r₂` and `buf₂` at the state the second call is entered in. `r₂` may be
  -- `r₁` -- the spec reads the second point off `m₁` -- so nothing needs them
  -- apart.
  have hr₂m : IsPointPtr (pointOutMem s.mem r₁ oX oY oZ oT) r₂ :=
    isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr₂)))
  have hbuf₂m : IsByteBufPtr (pointOutMem s.mem r₁ oX oY oZ oT) buf₂ :=
    isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice hbuf₂)))
  have hr₂' : IsPointPtr w₁.mem r₂ := isPointPtr_of_equiv heq₁ hr₂m
  have hbuf₂' : IsByteBufPtr w₁.mem buf₂ := isByteBufPtr_of_equiv heq₁ hbuf₂m
  have hwf₁ : w₁.WF := GlobalState.WF.of_equiv hm.wf.splice.splice.splice.splice heq₁.symm
  have hm₁ : w₁.RefWF [r₂] :=
    (hm.untouched hwf₁ heq₁.globals (fun b hb => hlive₁ b (hb r₁ (by simp)))).mono (by simp)

  obtain ⟨w₂, ret₂, hrun₂, pX, pY, pZ, pT, hfail₂, hok₂⟩ :=
    fd_ed25519_point_frombytes_conforms r₂ buf₂ w₁ hm₁ hr₂' hbuf₂' hbufr₂
  -- the second buffer as the spec reads it: at `m₁`, where the call read it
  rw [show readBuf hbuf₂' = readBuf hbuf₂m from readBuf_of_equiv heq₁] at hfail₂ hok₂

  by_cases sq₂ : IsSquare ((decodeBytes (readBuf hbuf₂m) ^ 2 - 1)
      / (d * decodeBytes (readBuf hbuf₂m) ^ 2 + 1))
  case neg =>
    -- only `r₁` was written
    obtain ⟨hret₂, heq₂⟩ := hfail₂ sq₂
    obtain ⟨t, hrun, rfl⟩ := run_fail₂ hrun₁ hret₁ hnull₁ hrun₂ hret₂
    refine ⟨_, _, hrun, fun h => absurd sq₁ h,
      fun _ => ⟨oX, oY, oZ, oT, hdec₁, hbnd₁, fun _ => ⟨rfl, ?_⟩, fun h => absurd h sq₂⟩⟩
    exact out_fail₂ hm.wf hn₁ heq₁ heq₂

  -- both points decoded: `r₁`'s writes, then `r₂`'s on top
  obtain ⟨hret₂, heq₂, hdec₂, hbnd₂⟩ := hok₂ sq₂
  obtain ⟨t, hrun, rfl⟩ := run_ok hrun₁ hret₁ hnull₁ hrun₂ hret₂ hnull₂
  exact ⟨_, _, hrun, fun h => absurd sq₁ h,
    fun _ => ⟨oX, oY, oZ, oT, hdec₁, hbnd₁, fun h => absurd sq₂ h,
      fun _ => ⟨pX, pY, pZ, pT, rfl, out_ok hm.wf hn₁ hn₂ heq₁ heq₂,
        decodesTo_of_equiv heq₁ hdec₂, decodedBounds_of_equiv heq₁ hbnd₂⟩⟩⟩

end PointFromBytes2x

open PointFromBytes2x in
/-- `hnull₁`/`hnull₂`: the region null-checks what it is handed back, so the
out-parameters must not be the block `llvm.mlir.zero` names. Nothing in
`GlobalState.WF` says so -- `SLLVM.nullBlock` is reserved by construction of
the loader, not by the model -- so the caller carries it. -/
theorem fd_ed25519_point_frombytes_2x_conforms (r₁ buf₁ r₂ buf₂ : Pointer) (s : GlobalState)
    (hm : s.RefWF [r₁, r₂])
    (hr₁ : IsPointPtr s.mem r₁) (hbuf₁ : IsByteBufPtr s.mem buf₁)
    (hr₂ : IsPointPtr s.mem r₂) (hbuf₂ : IsByteBufPtr s.mem buf₂)
    (hbufr₁ : buf₁.id ≠ r₁.id) (hbufr₂ : buf₂.id ≠ r₂.id)
    (hnull₁ : r₁.id ≠ SLLVM.nullBlock) (hnull₂ : r₂.id ≠ SLLVM.nullBlock) :
    fd_ed25519_point_frombytes_2x_spec r₁ buf₁ r₂ buf₂ s hr₁ hbuf₁ hr₂ hbuf₂ := by
  by_cases sq₁ : IsSquare ((decodeBytes (readBuf hbuf₁) ^ 2 - 1)
      / (d * decodeBytes (readBuf hbuf₁) ^ 2 + 1))
  case pos =>
    exact conforms_of_isSquare r₁ buf₁ r₂ buf₂ s hm hr₁ hbuf₁ hr₂ hbuf₂ hbufr₁ hbufr₂
      hnull₁ hnull₂ sq₁
  -- nothing was written: the region returns before the second call
  simp only [fd_ed25519_point_frombytes_2x_spec]
  obtain ⟨w₁, ret₁, hrun₁, oX, oY, oZ, oT, hfail₁, hok₁⟩ :=
    fd_ed25519_point_frombytes_conforms r₁ buf₁ s (hm.mono (by simp)) hr₁ hbuf₁ hbufr₁
  obtain ⟨hret₁, heq₁⟩ := hfail₁ sq₁
  obtain ⟨t, hrun, rfl⟩ := run_fail₁ (r₂ := r₂) (buf₂ := buf₂) hrun₁ hret₁
  exact ⟨_, _, hrun, fun _ => ⟨rfl, (GlobalState.killFrom_equiv w₁.mem hm.wf
    (fun q _ => (live?_of_equiv_mem heq₁ q).symm)).symm⟩, fun h => absurd h sq₁⟩

end Firedancer.Ref
