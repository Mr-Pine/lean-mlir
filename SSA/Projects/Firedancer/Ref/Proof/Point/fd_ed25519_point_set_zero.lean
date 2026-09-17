/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_point_set_zero
public import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_add_with_opts
public import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_set

/-!
# `fd_ed25519_point_set_zero` conformance (ref)

Four `fd_f25519_set`s from the two globals into `r`'s block. `Apart` carries the
globals past each write; the readback follows `AddWithOpts.tail_run`.
-/

@[expose] public section

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

attribute [local irreducible] fd_f25519_set

namespace SetZero
open AddWithOpts

theorem set_step {dst src : Pointer} {w : GlobalState} (hw : w.WF) (hne : dst.id ≠ src.id)
    (hd : IsFieldElemPtr w.mem dst) {v : ZMod _root_.p} {B : ℕ} (h : Holds w.mem src v B)
    {P : Prop}
    (k : ∀ w', StateT.run (runFunction (fd_f25519_set.denote
        (Ctxt.Valuation.ofHVector [.value src, .value dst]ₕ))) w
        = .value ([.value dst]ₕ, w') →
      Wrote dst w w' → Holds w'.mem dst v B → P) : P := by
  obtain ⟨out, ⟨w', hrun, heq⟩, hcopy⟩ := fd_f25519_set_conforms dst src w hw hne hd h.ptr
  have st := Wrote.of_splice hw hd heq
  have e : ∀ i, readLimb? dst i w'.mem = readLimb? src i w.mem := fun i =>
    (readLimb?_of_equiv heq dst i).symm.trans (hcopy i)
  exact k w' hrun st ⟨st.ptr,
    (readFieldElem_eq_of_readLimb fun i => readLimb_eq_of_readLimb? (e i)).trans h.val,
    limbBounds_of_readLimb? _ fun i l hl => limbBounds_readLimb? _ h.bnd i l ((e i).symm.trans hl)⟩

end SetZero

open AddWithOpts SetZero in
theorem fd_ed25519_point_set_zero_conforms (r : Pointer) (s : GlobalState)
    (hr : IsPointPtr s.mem r) :
    fd_ed25519_point_set_zero_spec r s hr := by
  simp only [fd_ed25519_point_set_zero_spec, Cfg.denote]
  intro hm
  have hs := hm.wf
  obtain ⟨q0, hg0, hq0⟩ := hm.gzero
  obtain ⟨q1, hg1, hq1⟩ := hm.gone
  refine run_runFunction' _ ?_
  denote_expose
  peel_addressof hg0.addr
  peel_addressof hg1.addr
  have hnr : r.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hr.left
  have hr0 : r.id ≠ q0.id := (hq0 r (List.mem_singleton_self r)).symm
  have hr1 : r.id ≠ q1.id := (hq1 r (List.mem_singleton_self r)).symm
  have G0 : Holds s.mem q0 0 0x8000000000000 := ⟨hg0.ptr, hg0.value, hg0.bnd⟩
  have G1 : Holds s.mem q1 1 0x8000000000000 := ⟨hg1.ptr, hg1.value, hg1.bnd⟩

  -- `%2`: `X = 0`
  refine set_step hs hr0 (coordPtr_zero r ▸ isCoordPtr hr 0) G0 fun w₁ hrun₁ st₁ HX => ?_
  peel_call hrun₁

  -- `%3`, `%4`: `Y = 1`
  denote_step_reduce v 3 [gepConst, ptradd, LLVM.const?]
  have e3 : v3 = .value (r.withOffset 40) := hv3
  subst e3
  clear hv3
  refine set_step (dst := r.withOffset 40) st₁.wf hr1 (st₁.isFieldElemPtr (isCoordPtr hr 1))
    (G1.carry (st₁.live _ hr1)) fun w₂ hrun₂ st₂ HY => ?_
  peel_call hrun₂

  -- `%5`, `%6`: `Z = 1`
  denote_step_reduce v 5 [gepConst, ptradd, LLVM.const?]
  have e5 : v5 = .value (r.withOffset 120) := hv5
  subst e5
  clear hv5
  refine set_step (dst := r.withOffset 120) st₂.wf hr1
    (st₂.isFieldElemPtr (st₁.isFieldElemPtr (isCoordPtr hr 3)))
    ((G1.carry (st₁.live _ hr1)).carry (st₂.live _ hr1)) fun w₃ hrun₃ st₃ HZ => ?_
  peel_call hrun₃

  -- `%7`, `%8`: `T = 0`
  denote_step_reduce v 7 [gepConst, ptradd, LLVM.const?]
  have e7 : v7 = .value (r.withOffset 80) := hv7
  subst e7
  clear hv7
  refine set_step (dst := r.withOffset 80) st₃.wf hr0
    (st₃.isFieldElemPtr (st₂.isFieldElemPtr (st₁.isFieldElemPtr (isCoordPtr hr 2))))
    (((G0.carry (st₁.live _ hr0)).carry (st₂.live _ hr0)).carry (st₃.live _ hr0))
    fun w₄ hrun₄ st₄ HT => ?_
  peel_call hrun₄
  refine ⟨w₄, by simp_return, ?_⟩

  /- The region has returned: `r`'s block as the four stores left it. -/
  have h40 : (r.withOffset 40).offsetInBits = r.offsetInBits + 320 := by
    simpa using withOffset_offsetInBits (off := 40) (by have := hr.2; simp; omega)
  have h80 : (r.withOffset 80).offsetInBits = r.offsetInBits + 640 := by
    simpa using withOffset_offsetInBits (off := 80) (by have := hr.2; simp; omega)
  have h120 : (r.withOffset 120).offsetInBits = r.offsetInBits + 960 := by
    simpa using withOffset_offsetInBits (off := 120) (by have := hr.2; simp; omega)
  obtain ⟨xX, k1⟩ := st₁.splice
  obtain ⟨xY, hxY⟩ := st₂.splice
  obtain ⟨xZ, hxZ⟩ := st₃.splice
  obtain ⟨xT, hxT⟩ := st₄.splice
  have k2 : w₂.mem.live? r.id = ((s.mem.splice r xX).splice (r.withOffset 40) xY).live? r.id :=
    hxY.trans (live?_splice_congr (p := r.withOffset 40) (x := xY) k1)
  have k3 : w₃.mem.live? r.id = (((s.mem.splice r xX).splice (r.withOffset 40) xY).splice
      (r.withOffset 120) xZ).live? r.id :=
    hxZ.trans (live?_splice_congr (p := r.withOffset 120) (x := xZ) k2)
  have k4 : w₄.mem.live? r.id = ((((s.mem.splice r xX).splice (r.withOffset 40) xY).splice
      (r.withOffset 120) xZ).splice (r.withOffset 80) xT).live? r.id :=
    hxT.trans (live?_splice_congr (p := r.withOffset 80) (x := xT) k3)
  have hpop := popFrame_equiv_block hs hnr
    (fun b _ hbr =>
      have h : r.id ≠ b := fun h => hbr h.symm
      (st₄.live b h).trans ((st₃.live b h).trans ((st₂.live b h).trans (st₁.live b h))))
    (fun b hbr =>
      have h : r.id ≠ b := fun h => hbr h.symm
      (live?_splice_ne (p := r.withOffset 80) h).trans
        ((live?_splice_ne (p := r.withOffset 120) h).trans
          ((live?_splice_ne (p := r.withOffset 40) h).trans (live?_splice_ne (p := r) h))))
    k4
  have OX := (((HX.carry k1.symm).splice (d := r.withOffset 40) (x := xY)
    (.inr (.inr (by omega)))).splice (d := r.withOffset 120) (x := xZ)
    (.inr (.inr (by omega)))).splice (d := r.withOffset 80) (x := xT) (.inr (.inr (by omega)))
  have OY := ((HY.carry k2.symm).splice (d := r.withOffset 120) (x := xZ)
    (.inr (.inr (by omega)))).splice (d := r.withOffset 80) (x := xT) (.inr (.inr (by omega)))
  have OZ := (HZ.carry k3.symm).splice (d := r.withOffset 80) (x := xT) (.inr (.inl (by omega)))
  have OT := HT.carry k4.symm
  refine ⟨xX, xY, xZ, xT, GlobalState.Equiv.symm hpop,
    readPoint_eq_of _ OX.val OY.val OT.val OZ.val, fun i => ?_⟩
  fin_cases i
  · exact limbBounds_congr' (coordPtr_zero r).symm OX.bnd
  · exact OY.bnd
  · exact OT.bnd
  · exact OZ.bnd

end Firedancer.Ref
