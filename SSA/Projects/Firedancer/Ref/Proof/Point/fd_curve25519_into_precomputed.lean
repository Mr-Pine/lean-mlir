/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Ref.Spec.Point.fd_curve25519_into_precomputed
public import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_add_with_opts
public import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_set
public import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_mul

/-!
# `fd_curve25519_into_precomputed` conformance (ref)

Locals `add` and `sub` are copied into `r->Y` and `r->X`, then `r->T` is multiplied
by `k` in place; `Wrote.holds` carries `r->T` and `k` past the two stores to
`r`'s block.
-/

@[expose] public section

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

attribute [local irreducible] fd_f25519_add_nr fd_f25519_sub_nr fd_f25519_set fd_f25519_mul

namespace IntoPrecomputed
open AddWithOpts

/-- The locals `add, sub`. -/
abbrev precompLocal (s : GlobalState) : Fin 2 → Pointer := fieldLocal s

/-- A call that wrote `d` leaves what any `q` apart from it holds. -/
theorem _root_.Firedancer.Ref.Wrote.holds {d q : Pointer} {w w' : GlobalState}
    {v : ZMod _root_.p} {B : ℕ} (st : Wrote d w w') (h : Holds w.mem q v B)
    (hap : FieldApart d q) : Holds w'.mem q v B := by
  by_cases hid : d.id = q.id
  · obtain ⟨x, hx⟩ := st.splice
    exact (h.splice (x := x) hap).carry (by rw [← hid]; exact hx)
  · exact h.carry (st.live _ hid)

theorem set_step {dst src : Pointer} {w : GlobalState} (hw : w.WF)
    (hd : IsFieldElemPtr w.mem dst) {v : ZMod _root_.p} {B : ℕ} (h : Holds w.mem src v B)
    (hne : dst.id ≠ src.id) {P : Prop}
    (k : ∀ w', StateT.run (runFunction (fd_f25519_set.denote
        (Ctxt.Valuation.ofHVector [.value src, .value dst]ₕ))) w
        = .value ([.value dst]ₕ, w') →
      Wrote dst w w' → Holds w'.mem dst v B → P) : P := by
  obtain ⟨out, ⟨w', hrun, heq⟩, hcopy⟩ := fd_f25519_set_conforms dst src w hw hne hd h.ptr
  have st := Wrote.of_splice hw hd heq
  have hl : ∀ i, readLimb? dst i w'.mem = readLimb? src i w.mem := fun i =>
    (readLimb?_of_equiv heq dst i).symm.trans (hcopy i)
  exact k w' hrun st ⟨st.ptr,
    (readFieldElem_eq_of_readLimb fun i => readLimb_eq_of_readLimb? (hl i)).trans h.val,
    limbBounds_of_readLimb? _ fun i l hi =>
      limbBounds_readLimb? h.ptr h.bnd i l ((hl i).symm.trans hi)⟩

/-- `addNr_step` with `src₁` below `0xffffffffffffe`, as a bias-bounded `X` is. -/
theorem addNr_step' {dst src₀ src₁ : Pointer} {w : GlobalState} (hw : w.WF)
    (hd : IsFieldElemPtr w.mem dst) {x₀ x₁ : ZMod _root_.p}
    (h₀ : Holds w.mem src₀ x₀ 0x8000000000000) (h₁ : Holds w.mem src₁ x₁ 0xffffffffffffe)
    {P : Prop}
    (k : ∀ w', StateT.run (runFunction (fd_f25519_add_nr.denote
        (Ctxt.Valuation.ofHVector [.value src₁, .value src₀, .value dst]ₕ))) w
        = .value ([.value dst]ₕ, w') →
      Wrote dst w w' → Holds w'.mem dst (x₀ + x₁) 0x18000000000000 → P) : P := by
  obtain ⟨out, hval, hbnd, w', hrun, heq⟩ :=
    fd_f25519_add_nr_conforms dst src₀ src₁ w hw (limbBounds_readLimb? h₀.ptr h₀.bnd)
      (limbBounds_readLimb? h₁.ptr h₁.bnd) hd h₀.ptr h₁.ptr
  have st := Wrote.of_splice hw hd heq
  exact k w' hrun st ⟨st.ptr, (readFieldElem_eq_splice hd heq).trans
    (hval.trans (by rw [h₀.val, h₁.val])), limbBounds_of_splice heq (limbBounds_readLimb? _ hbnd)⟩

/-- `subNr_step` with `src₁` bias-bounded. -/
theorem subNr_step' {dst src₀ src₁ : Pointer} {w : GlobalState} (hw : w.WF)
    (hd : IsFieldElemPtr w.mem dst) {x₀ x₁ : ZMod _root_.p}
    (h₀ : Holds w.mem src₀ x₀ 0x8000000000000) (h₁ : Holds w.mem src₁ x₁ 0xffffffffffffe)
    (hb₁ : BiasBounds h₁.ptr) {P : Prop}
    (k : ∀ w', StateT.run (runFunction (fd_f25519_sub_nr.denote
        (Ctxt.Valuation.ofHVector [.value src₁, .value src₀, .value dst]ₕ))) w
        = .value ([.value dst]ₕ, w') →
      Wrote dst w w' → Holds w'.mem dst (x₀ - x₁) 0x18000000000000 → P) : P := by
  obtain ⟨out, hval, hbnd, w', hrun, heq⟩ :=
    fd_f25519_sub_nr_conforms dst src₀ src₁ w hw (limbBounds_readLimb? h₀.ptr h₀.bnd)
      (biasBounds_readLimb? h₁.ptr hb₁) hd h₀.ptr h₁.ptr
  have st := Wrote.of_splice hw hd heq
  exact k w' hrun st ⟨st.ptr, (readFieldElem_eq_splice hd heq).trans
    (hval.trans (by rw [h₀.val, h₁.val])), limbBounds_of_splice heq (limbBounds_readLimb? _ hbnd)⟩

theorem mul_step' {dst src₀ src₁ : Pointer} {w : GlobalState} (hw : w.WF)
    (hd : IsFieldElemPtr w.mem dst) {x₀ x₁ : ZMod _root_.p}
    (h₀ : Holds w.mem src₀ x₀ 0x18000000000000) (h₁ : Holds w.mem src₁ x₁ 0x18000000000000)
    {P : Prop}
    (k : ∀ w', StateT.run (runFunction (fd_f25519_mul.denote
        (Ctxt.Valuation.ofHVector [.value src₁, .value src₀, .value dst]ₕ))) w
        = .value ([.value dst]ₕ, w') →
      Wrote dst w w' → Holds w'.mem dst (x₀ * x₁) 0x8000000000000 → P) : P := by
  obtain ⟨out, hval, hbnd, w', hrun, heq⟩ :=
    fd_f25519_mul_conforms dst src₀ src₁ w hw hd h₀.ptr h₁.ptr
      (limbBounds_readLimb? h₀.ptr h₀.bnd) (limbBounds_readLimb? h₁.ptr h₁.bnd)
  have st := Wrote.of_splice hw hd heq
  exact k w' hrun st ⟨st.ptr, (readFieldElem_eq_splice hd heq).trans
    (hval.trans (by rw [h₀.val, h₁.val])), limbBounds_of_splice heq (limbBounds_readLimb? _ hbnd)⟩

end IntoPrecomputed

open AddWithOpts IntoPrecomputed in
theorem fd_curve25519_into_precomputed_conforms (r : Pointer) (s : GlobalState)
    (hr : IsPointPtr s.mem r) : fd_curve25519_into_precomputed_spec r s hr := by
  simp only [fd_curve25519_into_precomputed_spec, Cfg.denote]
  intro hm hbX hbY hbT
  have hs := hm.wf
  obtain ⟨pk, hgk, hka⟩ := hm.gk
  refine run_runFunction' _ ?_
  denote_step_reduce v 0 [LLVM.const?] fold
  peel_addressof hgk.addr

  have hnr : r.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hr.left
  have hnk : pk.id.id < s.alloc.nextFreeBlock := hgk.below hs
  have fb : FrameBelow s.alloc.nextFreeBlock s (s.allocaChain fieldW 2) :=
    FrameBelow.allocaChain (le_refl _) (FrameBelow.refl _ _) 2
  have hwf : (s.allocaChain fieldW 2).WF := GlobalState.WF.allocaChain hs 2
  have hlf : ∀ k : Fin 2, IsFieldElemPtr (s.allocaChain fieldW 2).mem (precompLocal s k) :=
    fun k => ⟨GlobalState.fits_chainPtr k.isLt, by simp [precompLocal, fieldLocal]⟩
  set sL : GlobalState := s.allocaChain fieldW 2 with hsL
  clear_value sL

  -- `%2`, `%3`: `add`, `sub`
  peel_alloca_chain s, fieldW, 2
  fold_cells s, fieldW, precompLocal, 2
  rw [← hsL]
  iterate 2 peel_lifetime

  -- `%4`: `r->Y`
  denote_step_reduce v 4 [gepConst, ptradd, LLVM.const?]
  have e4 : v4 = .value (r.withOffset 40) := hv4
  subst e4
  clear hv4
  -- `r`'s coordinates and `@fd_f25519_k`, in `sL`
  have hcr : IsFieldElemPtr s.mem r := coordPtr_zero r ▸ isCoordPtr hr 0
  have hP := readPoint_eq_of hr (h0 := hcr) (h1 := isCoordPtr hr 1)
    (h2 := isCoordPtr hr 2) (h3 := isCoordPtr hr 3) rfl rfl rfl rfl
  have hX : Holds sL.mem r (readPoint hr).X 0xffffffffffffe :=
    Holds.carry ⟨hcr, (congrArg Point.X hP).symm, fun i => (hbX i).trans (biasLimb_le i)⟩
      (fb r.id hnr)
  have hXb : BiasBounds hX.ptr := carryBias (fb r.id hnr) hbX
  have hY : Holds sL.mem (r.withOffset 40) (readPoint hr).Y 0x8000000000000 :=
    Holds.carry ⟨_, (congrArg Point.Y hP).symm, hbY⟩ (fb r.id hnr)
  have hT : Holds sL.mem (r.withOffset 80) (readPoint hr).T 0x18000000000000 :=
    Holds.carry ⟨_, (congrArg Point.T hP).symm, hbT⟩ (fb r.id hnr)
  have hK : Holds sL.mem pk (2 * d) 0x18000000000000 :=
    Holds.carry ⟨hgk.ptr, hgk.value, hgk.bnd.loose⟩ (fb pk.id hnk)

  -- `%5`: `add = r->Y + r->X`
  refine addNr_step' hwf (hlf 0) hY hX fun u₁ hrun₁ st₁ HA => ?_
  peel_call hrun₁

  -- `%6`: `sub = r->Y - r->X`
  refine subNr_step' st₁.wf (st₁.isFieldElemPtr (hlf 1))
    (st₁.holds hY (.inl (fieldLocal_ne_below hnr))) (st₁.holds hX (.inl (fieldLocal_ne_below hnr)))
    (carryBias (st₁.live _ (fieldLocal_ne_below hnr)) hXb) fun u₂ hrun₂ st₂ HS => ?_
  peel_call hrun₂

  -- `%7`: `r->X = sub`
  refine set_step st₂.wf (st₂.isFieldElemPtr (st₁.isFieldElemPtr hX.ptr)) HS
    (fieldLocal_ne_below hnr).symm fun u₃ hrun₃ st₃ HX => ?_
  peel_call hrun₃

  -- `%8`: `r->Y = add`
  refine set_step st₃.wf (st₃.isFieldElemPtr (st₂.isFieldElemPtr (st₁.isFieldElemPtr hY.ptr)))
    (st₃.holds (st₂.holds HA (.inl (fieldLocal_ne (by decide))))
      (.inl (fieldLocal_ne_below hnr).symm))
    (fieldLocal_ne_below hnr).symm fun u₄ hrun₄ st₄ HY => ?_
  peel_call hrun₄

  -- `%9`, `%10`: `r->T = r->T * k`
  denote_step_reduce v 9 [gepConst, ptradd, LLVM.const?]
  have e9 : v9 = .value (r.withOffset 80) := hv9
  subst e9
  clear hv9
  have h40 : (r.withOffset 40).offsetInBits = r.offsetInBits + 320 := by
    simpa using withOffset_offsetInBits (off := 40) (by have := hr.2; simp; omega)
  have h80 : (r.withOffset 80).offsetInBits = r.offsetInBits + 640 := by
    simpa using withOffset_offsetInBits (off := 80) (by have := hr.2; simp; omega)
  have hkr : r.id ≠ pk.id := (hka r (List.mem_singleton_self r)).symm
  have hT₄ := st₄.holds (st₃.holds (st₂.holds (st₁.holds hT (.inl (fieldLocal_ne_below hnr)))
    (.inl (fieldLocal_ne_below hnr))) (.inr (.inl (by omega)))) (.inr (.inl (by omega)))
  have hK₄ := st₄.holds (st₃.holds (st₂.holds (st₁.holds hK (.inl (fieldLocal_ne_below hnk)))
    (.inl (fieldLocal_ne_below hnk))) (.inl hkr)) (.inl hkr)
  refine mul_step' st₄.wf hT₄.ptr hT₄ hK₄ fun u₅ hrun₅ st₅ HT => ?_
  peel_call hrun₅

  iterate 2 peel_lifetime
  refine ⟨u₅, by simp_return, ?_⟩

  /- The region has returned: `r`'s block as the three stores left it. -/
  have h120 : (r.withOffset 120).offsetInBits = r.offsetInBits + 960 := by
    simpa using withOffset_offsetInBits (off := 120) (by have := hr.2; simp; omega)
  obtain ⟨xX, hxX⟩ := st₃.splice
  obtain ⟨xY, hxY⟩ := st₄.splice
  obtain ⟨xT, hxT⟩ := st₅.splice
  have k3 : u₃.mem.live? r.id = (s.mem.splice r xX).live? r.id :=
    hxX.trans (live?_splice_congr (p := r) (x := xX)
      ((st₂.live _ (fieldLocal_ne_below hnr)).trans
        ((st₁.live _ (fieldLocal_ne_below hnr)).trans (fb r.id hnr))))
  have k4 : u₄.mem.live? r.id = ((s.mem.splice r xX).splice (r.withOffset 40) xY).live? r.id :=
    hxY.trans (live?_splice_congr (p := r.withOffset 40) (x := xY) k3)
  have k5 : u₅.mem.live? r.id = (((s.mem.splice r xX).splice (r.withOffset 40) xY).splice
      (r.withOffset 80) xT).live? r.id :=
    hxT.trans (live?_splice_congr (p := r.withOffset 80) (x := xT) k4)
  have hpop := popFrame_equiv_block hs hnr
    (fun b hb hbr =>
      have h : r.id ≠ b := fun h => hbr h.symm
      (st₅.live b h).trans ((st₄.live b h).trans ((st₃.live b h).trans
        ((st₂.live b (fieldLocal_ne_below hb)).trans
          ((st₁.live b (fieldLocal_ne_below hb)).trans (fb b hb))))))
    (fun b hbr =>
      have h : r.id ≠ b := fun h => hbr h.symm
      (live?_splice_ne (p := r.withOffset 80) h).trans
        ((live?_splice_ne (p := r.withOffset 40) h).trans (live?_splice_ne (p := r) h)))
    k5
  have OX := ((HX.carry k3.symm).splice (d := r.withOffset 40) (x := xY)
    (.inr (.inr (by omega)))).splice (d := r.withOffset 80) (x := xT) (.inr (.inr (by omega)))
  have OY := (HY.carry k4.symm).splice (d := r.withOffset 80) (x := xT) (.inr (.inr (by omega)))
  have OT := HT.carry k5.symm
  refine ⟨xX, xY, xT, GlobalState.Equiv.symm hpop, ?_, OX.bnd, OY.bnd, OT.bnd⟩
  have hZ : readFieldElem (m := ((s.mem.splice r xX).splice (r.withOffset 40) xY).splice
      (r.withOffset 80) xT) (isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice
        (coordPtr_three r ▸ isCoordPtr hr 3)))) = (readPoint hr).Z :=
    (readFieldElem_eq_of_readLimb?_eq (h' := coordPtr_three r ▸ isCoordPtr hr 3) fun i =>
      (readLimb?_splice_of_fieldApart (.inr (.inl (by omega))) i).trans
        ((readLimb?_splice_of_fieldApart (.inr (.inl (by omega))) i).trans
          (readLimb?_splice_of_fieldApart (.inr (.inl (by omega))) i))).trans
      (congrArg Point.Z hP).symm
  rw [readPoint_eq_of _ OX.val OY.val OT.val hZ]
  simp only [PrecomputedPoint.ofSlots, Point.toPrecomputed, mul_comm]

end Firedancer.Ref
