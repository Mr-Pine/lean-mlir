/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_sqrt_ratio
import SSA.Projects.Firedancer.Ref.Spec.Bias
import SSA.Projects.Firedancer.Ref.Proof.Globals
import SSA.Projects.Firedancer.Ref.Proof.Locals
import SSA.Projects.Firedancer.Ref.Proof.Step.fd_f25519_abs
import SSA.Projects.Firedancer.Ref.Proof.Step.fd_f25519_neg
import SSA.Projects.Firedancer.Ref.Proof.Step.fd_f25519_if
import SSA.Projects.Firedancer.Ref.Proof.Step.fd_f25519_eq
import SSA.Projects.Firedancer.Ref.Proof.Step.fd_f25519_pow22523

import SSA.Projects.Firedancer.Prime

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Algebra.Group.Even

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `%28`/`%31`: the region ors two 0/1 flags, which is the flag of their
disjunction. -/
theorem or_flag {A B : Prop} [Decidable A] [Decidable B] :
    ((if A then 1#32 else 0#32) ||| (if B then 1#32 else 0#32)) = if A ∨ B then 1#32 else 0#32 := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

/-- Two writes at the same pointer collapse to the second: the shape the
ending needs, since the region writes `r` four times. -/
private theorem splice_trans (s₀ : GlobalState) {m₁ m₂ : MemoryState} {q : Pointer}
    {x y : BitVec (5 * 64)}
    (h₁ : m₁.live? q.id = (s₀.mem.splice q x).live? q.id)
    (h₂ : m₂.live? q.id = (m₁.splice q y).live? q.id) :
    m₂.live? q.id = (s₀.mem.splice q y).live? q.id :=
  h₂.trans ((live?_splice_congr h₁).trans ((splice_splice_equiv (s := s₀) x y).live q.id))

/-- The ten `fd_f25519_t` locals `%2 … %11` allocate. In allocation order --
`%2 … %11` of the region -- they are the locals `fd_f25519.c` declares:

    0 v2      1 v3      2 uv3          3 v6              4 v7
    5 uv7     6 check   7 u_neg        8 u_neg_sqrtm1    9 r_prime -/
abbrev sqrtRatioLocal (s : GlobalState) : Fin 10 → Pointer := fieldLocal s

open Pow22523 in
/-- What holds at every point of the walk: the ten locals and the
out-parameter are addressable, and every other block the caller holds reads as
it did on entry. `r` is the one caller block the region writes (`%18`/`%19`),
so it is carried separately from the frame clause. -/
structure Frame (s₀ : GlobalState) (r : Pointer) (w : GlobalState) : Prop where
  wf : w.WF
  locals : ∀ k : Fin 10, IsFieldElemPtr w.mem (sqrtRatioLocal s₀ k)
  ptr : IsFieldElemPtr w.mem r
  live : ∀ b : BlockId, b.id < s₀.alloc.nextFreeBlock → b ≠ r.id →
    w.mem.live? b = s₀.mem.live? b

namespace Frame

open Pow22523

variable {s₀ w w' : GlobalState} {r : Pointer} {x : ZMod p}

/-- A caller's field element, at any point of the walk: it is not `r`, and the
locals are above it, so nothing the region wrote reached it. -/
theorem caller (hf : Frame s₀ r w) {q : Pointer} {bound : ℕ} (hq : IsFieldElemPtr s₀.mem q)
    (hb : q.id.id < s₀.alloc.nextFreeBlock) (hqr : q.id ≠ r.id) (hbnd : LimbBounds hq bound) :
    ∃ hq' : IsFieldElemPtr w.mem q, readFieldElem hq' = readFieldElem hq ∧ LimbBounds hq' bound :=
  carry (hf.live q.id hb hqr) hq hbnd

/-- A step that writes one of the locals. -/
theorem stepLocal (hf : Frame s₀ r w) (hr : r.id.id < s₀.alloc.nextFreeBlock) {k : Fin 10}
    (st : Wrote (sqrtRatioLocal s₀ k) w w') : Frame s₀ r w' where
  wf := st.wf
  locals := fun j =>
    if h : j = k then h ▸ st.ptr
    else isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (Ne.symm h))) (hf.locals j)
  ptr := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne_below hr)) hf.ptr
  live := fun b hb hbr => (st.live b (fieldLocal_ne_below hb)).trans (hf.live b hb hbr)

/-- A step that writes the out-parameter. -/
theorem stepOut (hf : Frame s₀ r w) (hr : r.id.id < s₀.alloc.nextFreeBlock)
    (st : Wrote r w w') : Frame s₀ r w' where
  wf := st.wf
  locals := fun j =>
    isFieldElemPtr_of_live?_eq (st.live _ (Ne.symm (fieldLocal_ne_below hr))) (hf.locals j)
  ptr := st.ptr
  live := fun b hb hbr => (st.live b (Ne.symm hbr)).trans (hf.live b hb hbr)

/-- A call that only reads -- `fd_f25519_eq` -- moves nothing. -/
theorem of_equiv (hf : Frame s₀ r w) (he : w ≈ w') : Frame s₀ r w' where
  wf := GlobalState.WF.of_equiv hf.wf he
  locals := fun k => isFieldElemPtr_of_live?_eq (he.live _).symm (hf.locals k)
  ptr := isFieldElemPtr_of_live?_eq (he.live _).symm hf.ptr
  live := fun b hb hbr => (he.live b).symm.trans (hf.live b hb hbr)

end Frame

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 100000 in
open Pow22523 in
/-- The spec, assembled: the walk says what is at `o`, the field theory says
what that value is worth.

`hsqrtm1` packs everything the region needs of `@fd_f25519_sqrtm1`: `%1` reads
its address, `%23`/`%27` multiply through it, and `%18`/`%19` write through `r`
before either -- so the value, the limb bound and `q.id ≠ r.id` all come in
together. `decodeFieldElem_sqrtm1` is what discharges the value half for a
state loaded from `fd_f25519_sqrtm1_init`. -/
theorem fd_f25519_sqrt_ratio_conforms (r u v : Pointer) (s : GlobalState)
    (hs : s.WF)
    (hsqrtm1 : ∃ q : Pointer, ∃ hq : IsFieldElemPtr s.mem q,
      GlobalPtr s "fd_f25519_sqrtm1" q ∧ readFieldElem hq = sqrtm1
        ∧ LimbBounds hq ∧ q.id ≠ r.id)
    (hr : IsFieldElemPtr s.mem r)
    (hu : IsFieldElemPtr s.mem u)
    (hv : IsFieldElemPtr s.mem v)
    (hulimb : LimbBounds hu)
    (hvlimb : LimbBounds hv)
    -- `%18`/`%19` write `r` before `%21`/`%22` read `v` and `u`, so a spec
    -- stated over the entry values needs the out-parameter kept apart
    (hur : u.id ≠ r.id)
    (hvr : v.id ≠ r.id) :
    fd_f25519_sqrt_ratio_spec r u v s hr hu hv := by
  simp only [fd_f25519_sqrt_ratio_spec]

  suffices h : ∃ s' : GlobalState,
      StateT.run (runFunction (fd_f25519_sqrt_ratio.denote
          (Ctxt.Valuation.ofHVector [.value v, .value u, .value r]ₕ))) s
        = .value ([(.value (if ∃ x : ZMod p, x ^ 2 * readFieldElem hv = readFieldElem hu
            then 1#32 else 0#32) : LLVM.IntW 32)]ₕ, s')
      ∧ ∃ out : Fin 5 → BitVec 64,
          (readFieldElem (m := s.mem.splice r (packLimbs out))
              (isFieldElemPtr_splice hr)).val % 2 = 0
          ∧ ((∃ x : ZMod p, x ^ 2 * readFieldElem hv = readFieldElem hu) →
              readFieldElem (m := s.mem.splice r (packLimbs out)) (isFieldElemPtr_splice hr) ^ 2
                * readFieldElem hv = readFieldElem hu)
          ∧ (readFieldElem hv = 0 →
              readFieldElem (m := s.mem.splice r (packLimbs out)) (isFieldElemPtr_splice hr) = 0)
          ∧ BiasBounds (m := s.mem.splice r (packLimbs out)) (isFieldElemPtr_splice hr)
          ∧ limbSum (m := s.mem.splice r (packLimbs out)) (isFieldElemPtr_splice hr)
              < 2 ^ 256 - 38
          ∧ ({ s with mem := s.mem.splice r (packLimbs out) } : GlobalState) ≈ s' by
    obtain ⟨s', hrun, out, heven, hsquare, hzero, hbnd, hsum, heqv⟩ := h
    exact ⟨out, heven, hsquare, hzero, hbnd, hsum, s', hrun, heqv⟩

  refine run_runFunction' _ ?_
  simp only [Cfg.denote]

  denote_step_reduce v 0 [LLVM.const?]
  obtain ⟨psqrtm1, hpsqrtm1, hglobal, hsqrtm1, hsqrtm1limbs, hglobne⟩ := hsqrtm1

  peel_addressof hglobal

  -- Everything the caller can address predates the frame, so no `alloca` of
  -- the chain touches it.
  have hnr : r.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hr.left
  have hnu : u.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hu.left
  have hnv : v.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hv.left
  have hng : psqrtm1.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hpsqrtm1.left

  -- The frame, and everything the walk needs of it, while it is still
  -- transparent: `s.allocaChain fieldW 10` unfolds into ten `HashMap`
  -- inserts, so left exposed it makes defeq walk the buckets on every `live?`.
  have fb : FrameBelow s.alloc.nextFreeBlock s (s.allocaChain fieldW 10) :=
    FrameBelow.allocaChain (le_refl _) (FrameBelow.refl _ _) 10
  have hwf : (s.allocaChain fieldW 10).WF := GlobalState.WF.allocaChain hs 10
  have hlf : ∀ k : Fin 10,
      Fits (s.allocaChain fieldW 10).mem (sqrtRatioLocal s k) 320 :=
    fun k => GlobalState.fits_chainPtr k.isLt
  have hrc : IsFieldElemPtr (s.allocaChain fieldW 10).mem r :=
    isFieldElemPtr_of_live?_eq (fb r.id hnr) hr

  -- The locals are the blocks this frame allocated, so they miss everything the
  -- caller holds, and they are consecutive, so they miss each other.

  set sLocals : GlobalState := s.allocaChain fieldW 10 with hsLocals
  clear_value sLocals

  -- %2 … %11, folded to `sqrtRatioLocal s k` and sealed as `sLocals`
  peel_alloca_chain s, fieldW, 10
  fold_cells s, fieldW, sqrtRatioLocal, 10
  rw [← hsLocals]

  -- the stepper's `v0`: the alloca count
  denote_clear v 0 0

  -- `fd_f25519.c`'s names for the ten locals
  set v2 := sqrtRatioLocal s 0 with hv2ptr
  set v3 := sqrtRatioLocal s 1 with hv3ptr
  set uv3 := sqrtRatioLocal s 2 with huv3ptr
  set v6 := sqrtRatioLocal s 3 with hv6ptr
  set v7 := sqrtRatioLocal s 4 with hv7ptr
  set uv7 := sqrtRatioLocal s 5 with huv7ptr
  set check := sqrtRatioLocal s 6 with hcheckptr
  set u_neg := sqrtRatioLocal s 7 with hu_negptr
  set u_neg_sqrtm1 := sqrtRatioLocal s 8 with hu_neg_sqrtm1ptr
  set r_prime := sqrtRatioLocal s 9 with hr_primeptr

  peel_lifetime

  -- the frame on entry: ten fresh locals, `r` and everything the caller holds
  -- exactly as it was
  have F₀ : Frame s r sLocals :=
    { wf := hwf
      locals := fun k => ⟨hlf k, by simp [fieldLocal]⟩
      ptr := hrc
      live := fun b hb _ => fb b hb }

  -- `u` and `v` at any point of the walk: the region writes neither
  have vAt : ∀ {w : GlobalState}, Frame s r w →
      ∃ h : IsFieldElemPtr w.mem v, readFieldElem h = readFieldElem hv ∧ LimbBounds h :=
    fun F => F.caller hv hnv hvr hvlimb
  have uAt : ∀ {w : GlobalState}, Frame s r w →
      ∃ h : IsFieldElemPtr w.mem u, readFieldElem h = readFieldElem hu ∧ LimbBounds h :=
    fun F => F.caller hu hnu hur hulimb

  -- %12 `fd_f25519_sqr( v2, v )`
  obtain ⟨pv₀, hval₀, hbnd₀⟩ := vAt F₀
  have pv2₀ : IsFieldElemPtr sLocals.mem v2 := by rw [hv2ptr]; exact F₀.locals 0
  obtain ⟨s₁, hrun₁, f₁⟩ := sqr_step F₀.wf pv2₀ pv₀ hval₀ hbnd₀.loose
  peel_call hrun₁
  clear hrun₁
  have F₁ : Frame s r s₁ := F₀.stepLocal hnr (hv2ptr ▸ f₁.wrote)
  clear pv2₀ pv₀ hval₀ hbnd₀ hrc hlf hwf hnv hnu

  -- %13 `fd_f25519_mul( v3, v2, v )`
  peel_lifetime
  obtain ⟨pv₁, hval₁, hbnd₁⟩ := vAt F₁
  have pv3₁ : IsFieldElemPtr s₁.mem v3 := by rw [hv3ptr]; exact F₁.locals 1
  obtain ⟨s₂, hrun₂, f₂⟩ :=
    mul_step F₁.wf pv3₁ f₁.ptr pv₁ f₁.val hval₁ f₁.bnd.loose hbnd₁.loose
  peel_call hrun₂
  clear hrun₂
  have F₂ : Frame s r s₂ := F₁.stepLocal hnr (hv3ptr ▸ f₂.wrote)
  clear pv3₁ pv₁ hval₁ hbnd₁

  -- %14 `fd_f25519_mul( uv3, u, v3 )`
  peel_lifetime
  obtain ⟨pu₂, hval₂, hbnd₂⟩ := uAt F₂
  have puv3₂ : IsFieldElemPtr s₂.mem uv3 := by rw [huv3ptr]; exact F₂.locals 2
  obtain ⟨s₃, hrun₃, f₃⟩ :=
    mul_step F₂.wf puv3₂ pu₂ f₂.ptr hval₂ f₂.val hbnd₂.loose f₂.bnd.loose
  peel_call hrun₃
  clear hrun₃
  have F₃ : Frame s r s₃ := F₂.stepLocal hnr (huv3ptr ▸ f₃.wrote)
  clear puv3₂ pu₂ hval₂ hbnd₂

  -- %15 `fd_f25519_sqr( v6, v3 )` -- `v3` survives the write at `uv3`
  peel_lifetime
  obtain ⟨pv3₃, hv3₃, hb3₃⟩ :=
    survive (f₃.live v3.id (by rw [huv3ptr, hv3ptr]; exact fieldLocal_ne (by decide)))
      f₂.ptr f₂.val f₂.bnd
  have pv6₃ : IsFieldElemPtr s₃.mem v6 := by rw [hv6ptr]; exact F₃.locals 3
  obtain ⟨s₄, hrun₄, f₄⟩ := sqr_step F₃.wf pv6₃ pv3₃ hv3₃ hb3₃.loose
  peel_call hrun₄
  clear hrun₄
  have F₄ : Frame s r s₄ := F₃.stepLocal hnr (hv6ptr ▸ f₄.wrote)
  clear pv6₃ pv3₃ hv3₃ hb3₃

  -- %16 `fd_f25519_mul( v7, v6, v )`
  peel_lifetime
  obtain ⟨pv₄, hval₄, hbnd₄⟩ := vAt F₄
  have pv7₄ : IsFieldElemPtr s₄.mem v7 := by rw [hv7ptr]; exact F₄.locals 4
  obtain ⟨s₅, hrun₅, f₅⟩ :=
    mul_step F₄.wf pv7₄ f₄.ptr pv₄ f₄.val hval₄ f₄.bnd.loose hbnd₄.loose
  peel_call hrun₅
  clear hrun₅
  have F₅ : Frame s r s₅ := F₄.stepLocal hnr (hv7ptr ▸ f₅.wrote)
  clear pv7₄ pv₄ hval₄ hbnd₄

  -- %17 `fd_f25519_mul( uv7, u, v7 )`
  peel_lifetime
  obtain ⟨pu₅, hval₅, hbnd₅⟩ := uAt F₅
  have puv7₅ : IsFieldElemPtr s₅.mem uv7 := by rw [huv7ptr]; exact F₅.locals 5
  obtain ⟨s₆, hrun₆, f₆⟩ :=
    mul_step F₅.wf puv7₅ pu₅ f₅.ptr hval₅ f₅.val hbnd₅.loose f₅.bnd.loose
  peel_call hrun₆
  clear hrun₆
  have F₆ : Frame s r s₆ := F₅.stepLocal hnr (huv7ptr ▸ f₆.wrote)
  clear puv7₅ pu₅ hval₅ hbnd₅

  -- %18 `fd_f25519_pow22523( r, uv7 )` -- the first write to the out-parameter
  obtain ⟨s₇, hrun₇, f₇⟩ := pow_step F₆.wf F₆.ptr f₆.ptr f₆.val f₆.bnd.loose
  peel_call hrun₇
  clear hrun₇
  have F₇ : Frame s r s₇ := F₆.stepOut hnr f₇.wrote

  -- %19 `fd_f25519_mul( r, r, uv3 )` -- `uv3` survives the four writes since %14
  obtain ⟨puv3₄, huv3₄, hbuv3₄⟩ :=
    survive (f₄.live uv3.id (by rw [hv6ptr, huv3ptr]; exact fieldLocal_ne (by decide)))
      f₃.ptr f₃.val f₃.bnd
  obtain ⟨puv3₅, huv3₅, hbuv3₅⟩ :=
    survive (f₅.live uv3.id (by rw [hv7ptr, huv3ptr]; exact fieldLocal_ne (by decide)))
      puv3₄ huv3₄ hbuv3₄
  obtain ⟨puv3₆, huv3₆, hbuv3₆⟩ :=
    survive (f₆.live uv3.id (by rw [huv7ptr, huv3ptr]; exact fieldLocal_ne (by decide)))
      puv3₅ huv3₅ hbuv3₅
  obtain ⟨puv3₇, huv3₇, hbuv3₇⟩ :=
    survive (f₇.live uv3.id (by rw [huv3ptr]; exact Ne.symm (fieldLocal_ne_below hnr)))
      puv3₆ huv3₆ hbuv3₆
  obtain ⟨s₈, hrun₈, f₈⟩ :=
    mul_step F₇.wf F₇.ptr f₇.ptr puv3₇ f₇.val huv3₇ f₇.bnd.loose hbuv3₇.loose
  peel_call hrun₈
  clear hrun₈
  have F₈ : Frame s r s₈ := F₇.stepOut hnr f₈.wrote
  clear puv3₇ huv3₇ hbuv3₇ puv3₆ huv3₆ hbuv3₆ puv3₅ huv3₅ hbuv3₅ puv3₄ huv3₄ hbuv3₄

  -- %20 `fd_f25519_sqr( check, r )`
  peel_lifetime
  have pcheck₈ : IsFieldElemPtr s₈.mem check := by rw [hcheckptr]; exact F₈.locals 6
  obtain ⟨s₉, hrun₉, f₉⟩ := sqr_step F₈.wf pcheck₈ f₈.ptr f₈.val f₈.bnd.loose
  peel_call hrun₉
  clear hrun₉
  have F₉ : Frame s r s₉ := F₈.stepLocal hnr (hcheckptr ▸ f₉.wrote)
  clear pcheck₈

  -- %21 `fd_f25519_mul( check, check, v )` -- `check = v * r²`, as the comment says
  obtain ⟨pv₉, hval₉, hbnd₉⟩ := vAt F₉
  obtain ⟨s₁₀, hrun₁₀, f₁₀⟩ :=
    mul_step F₉.wf f₉.ptr f₉.ptr pv₉ f₉.val hval₉ f₉.bnd.loose hbnd₉.loose
  peel_call hrun₁₀
  clear hrun₁₀
  have F₁₀ : Frame s r s₁₀ := F₉.stepLocal hnr (hcheckptr ▸ f₁₀.wrote)
  clear pv₉ hval₉ hbnd₉

  -- %22 `fd_f25519_neg( u_neg, u )` -- the limbs come back at the opp bound
  peel_lifetime
  obtain ⟨pu₁₀, huval₁₀, hubnd₁₀⟩ := uAt F₁₀
  have puneg₁₀ : IsFieldElemPtr s₁₀.mem u_neg := by rw [hu_negptr]; exact F₁₀.locals 7
  obtain ⟨s₁₁, w₁₁, hrun₁₁, hnegval, hnegbnd⟩ := neg_step F₁₀.wf puneg₁₀ pu₁₀ huval₁₀ hubnd₁₀.bias
  peel_call hrun₁₁
  clear hrun₁₁
  have F₁₁ : Frame s r s₁₁ := F₁₀.stepLocal hnr (hu_negptr ▸ w₁₁)
  clear puneg₁₀ pu₁₀ huval₁₀ hubnd₁₀

  -- %23 `fd_f25519_mul( u_neg_sqrtm1, u_neg, fd_f25519_sqrtm1 )` -- the global
  -- enters here, as the value `hsqrtm1` pins
  peel_lifetime
  obtain ⟨pg₁₁, hgval₁₁, hgbnd₁₁⟩ := F₁₁.caller hpsqrtm1 hng hglobne hsqrtm1limbs
  have pusq₁₁ : IsFieldElemPtr s₁₁.mem u_neg_sqrtm1 := by
    rw [hu_neg_sqrtm1ptr]; exact F₁₁.locals 8
  obtain ⟨s₁₂, hrun₁₂, f₁₂⟩ :=
    mul_step F₁₁.wf pusq₁₁ w₁₁.ptr pg₁₁ hnegval (hgval₁₁.trans hsqrtm1)
      (fun i => ((hnegbnd i).trans (biasLimb_le i)).trans (by norm_num)) hgbnd₁₁.loose
  peel_call hrun₁₂
  clear hrun₁₂
  have F₁₂ : Frame s r s₁₂ := F₁₁.stepLocal hnr (hu_neg_sqrtm1ptr ▸ f₁₂.wrote)
  clear pusq₁₁ pg₁₁ hgval₁₁ hgbnd₁₁

  -- the three comparands, carried to where the `eq`s read them
  obtain ⟨pchk₁₁, hchkval₁₁, hchkbnd₁₁⟩ :=
    survive (w₁₁.live check.id (by rw [hu_negptr, hcheckptr]; exact fieldLocal_ne (by decide)))
      f₁₀.ptr f₁₀.val f₁₀.bnd
  obtain ⟨pchk₁₂, hchkval₁₂, hchkbnd₁₂⟩ :=
    survive (f₁₂.live check.id
        (by rw [hu_neg_sqrtm1ptr, hcheckptr]; exact fieldLocal_ne (by decide)))
      pchk₁₁ hchkval₁₁ hchkbnd₁₁
  obtain ⟨puneg₁₂, hnegval₁₂, hnegbnd₁₂⟩ :=
    surviveBias (f₁₂.live u_neg.id
        (by rw [hu_neg_sqrtm1ptr, hu_negptr]; exact fieldLocal_ne (by decide)))
      w₁₁.ptr hnegval hnegbnd

  -- %24 `fd_f25519_eq( check, u )` -- `correct_sign_sqrt`. `eq` only reads, so
  -- every fact crosses it by `≈`.
  obtain ⟨pu₁₂, huval₁₂, hubnd₁₂⟩ := uAt F₁₂
  obtain ⟨s₁₃, hrun₁₃, heq₁₃⟩ :=
    eq_step F₁₂.wf pchk₁₂ pu₁₂ hchkbnd₁₂ (LimbBounds.bias hubnd₁₂) hchkval₁₂ huval₁₂
  peel_call hrun₁₃
  clear hrun₁₃
  have F₁₃ : Frame s r s₁₃ := F₁₂.of_equiv heq₁₃
  clear pu₁₂ huval₁₂ hubnd₁₂ pchk₁₁ hchkval₁₁ hchkbnd₁₁ hnegval hnegbnd
  obtain ⟨pchk₁₃, hchkval₁₃, hchkbnd₁₃⟩ :=
    survive (heq₁₃.live check.id).symm pchk₁₂ hchkval₁₂ hchkbnd₁₂
  obtain ⟨puneg₁₃, hnegval₁₃, hnegbnd₁₃⟩ :=
    surviveBias (heq₁₃.live u_neg.id).symm puneg₁₂ hnegval₁₂ hnegbnd₁₂
  obtain ⟨pusq₁₃, husqval₁₃, husqbnd₁₃⟩ :=
    survive (heq₁₃.live u_neg_sqrtm1.id).symm f₁₂.ptr f₁₂.val f₁₂.bnd

  -- %25 `fd_f25519_eq( check, u_neg )` -- `flipped_sign_sqrt`. The subtrahend is
  -- `fd_f25519_neg`'s uncarried result, which is why `eq` asks for the bias
  -- bound rather than the tight one.
  obtain ⟨s₁₄, hrun₁₄, heq₁₄⟩ :=
    eq_step F₁₃.wf pchk₁₃ puneg₁₃ hchkbnd₁₃ hnegbnd₁₃ hchkval₁₃ hnegval₁₃
  peel_call hrun₁₄
  clear hrun₁₄
  have F₁₄ : Frame s r s₁₄ := F₁₃.of_equiv heq₁₄
  clear puneg₁₃ hnegval₁₃ hnegbnd₁₃ puneg₁₂ hnegval₁₂ hnegbnd₁₂ pchk₁₂ hchkval₁₂ hchkbnd₁₂
  obtain ⟨pchk₁₄, hchkval₁₄, hchkbnd₁₄⟩ :=
    survive (heq₁₄.live check.id).symm pchk₁₃ hchkval₁₃ hchkbnd₁₃
  obtain ⟨pusq₁₄, husqval₁₄, husqbnd₁₄⟩ :=
    survive (heq₁₄.live u_neg_sqrtm1.id).symm pusq₁₃ husqval₁₃ husqbnd₁₃

  -- %26 `fd_f25519_eq( check, u_neg_sqrtm1 )` -- `flipped_sign_sqrt_i`
  obtain ⟨s₁₅, hrun₁₅, heq₁₅⟩ :=
    eq_step F₁₄.wf pchk₁₄ pusq₁₄ hchkbnd₁₄ (LimbBounds.bias husqbnd₁₄) hchkval₁₄ husqval₁₄
  peel_call hrun₁₅
  clear hrun₁₅
  have F₁₅ : Frame s r s₁₅ := F₁₄.of_equiv heq₁₅
  clear pusq₁₄ husqval₁₄ husqbnd₁₄ pchk₁₄ hchkval₁₄ hchkbnd₁₄ pusq₁₃ husqval₁₃ husqbnd₁₃ pchk₁₃ hchkval₁₃ hchkbnd₁₃

  -- `r` has held `(u v⁷)^((p-5)/8) · u v³` since %19; carry it past the four
  -- writes and the three comparisons to where %27 multiplies it by `√-1`
  have hcheckr : check.id ≠ r.id := by rw [hcheckptr]; exact fieldLocal_ne_below hnr
  obtain ⟨pr₉, hrval₉, hrbnd₉⟩ := survive (f₉.live r.id hcheckr) f₈.ptr f₈.val f₈.bnd
  obtain ⟨pr₁₀, hrval₁₀, hrbnd₁₀⟩ := survive (f₁₀.live r.id hcheckr) pr₉ hrval₉ hrbnd₉
  obtain ⟨pr₁₁, hrval₁₁, hrbnd₁₁⟩ :=
    survive (w₁₁.live r.id (by rw [hu_negptr]; exact fieldLocal_ne_below hnr))
      pr₁₀ hrval₁₀ hrbnd₁₀
  obtain ⟨pr₁₂, hrval₁₂, hrbnd₁₂⟩ :=
    survive (f₁₂.live r.id (by rw [hu_neg_sqrtm1ptr]; exact fieldLocal_ne_below hnr))
      pr₁₁ hrval₁₁ hrbnd₁₁
  obtain ⟨pr₁₃, hrval₁₃, hrbnd₁₃⟩ := survive (heq₁₃.live r.id).symm pr₁₂ hrval₁₂ hrbnd₁₂
  obtain ⟨pr₁₄, hrval₁₄, hrbnd₁₄⟩ := survive (heq₁₄.live r.id).symm pr₁₃ hrval₁₃ hrbnd₁₃
  obtain ⟨pr₁₅, hrval₁₅, hrbnd₁₅⟩ := survive (heq₁₅.live r.id).symm pr₁₄ hrval₁₄ hrbnd₁₄

  -- %27 `fd_f25519_mul( r_prime, r, fd_f25519_sqrtm1 )`
  peel_lifetime
  obtain ⟨pg₁₅, hgval₁₅, hgbnd₁₅⟩ := F₁₅.caller hpsqrtm1 hng hglobne hsqrtm1limbs
  have prp₁₅ : IsFieldElemPtr s₁₅.mem r_prime := by rw [hr_primeptr]; exact F₁₅.locals 9
  obtain ⟨s₁₆, hrun₁₆, f₁₆⟩ :=
    mul_step F₁₅.wf prp₁₅ pr₁₅ pg₁₅ hrval₁₅ (hgval₁₅.trans hsqrtm1) hrbnd₁₅.loose hgbnd₁₅.loose
  peel_call hrun₁₆
  clear hrun₁₆
  have F₁₆ : Frame s r s₁₆ := F₁₅.stepLocal hnr (hr_primeptr ▸ f₁₆.wrote)
  clear prp₁₅ pg₁₅ hgval₁₅ hgbnd₁₅ pr₁₄ hrval₁₄ hrbnd₁₄ pr₁₃ hrval₁₃ hrbnd₁₃ pr₁₂ hrval₁₂ hrbnd₁₂ pr₁₁ hrval₁₁ hrbnd₁₁ pr₁₀ hrval₁₀ hrbnd₁₀ pr₉ hrval₉ hrbnd₉ hcheckr


  have  uv7 : (readFieldElem hu *
         (readFieldElem hv * readFieldElem hv * readFieldElem hv *
                          (readFieldElem hv * readFieldElem hv * readFieldElem hv) *
                        readFieldElem hv)) = readFieldElem hu * ((readFieldElem hv) ^ 7) := by ring
  have uv3 : (readFieldElem hu * (readFieldElem hv * readFieldElem hv * readFieldElem hv)) = readFieldElem hu * ((readFieldElem hv) ^ 3) := by ring
  denote_step_reduce v 28 only [LLVM.or, LLVM.or?, uv7, uv3]
  set uv7powuv3 := (readFieldElem hu * readFieldElem hv ^ 7) ^ (2 ^ 252 - 3) * (readFieldElem hu * readFieldElem hv ^ 3)
  set checkVal := uv7powuv3 * uv7powuv3 * readFieldElem hv
  simp at hv28
  set cond := checkVal = -(readFieldElem hu * sqrtm1) ∨ checkVal = -(readFieldElem hu)
  replace hv28 : v28 = .value (if cond then 1#32 else 0#32) := by
    rw [hv28]
    simp only [or_flag]
    rfl
  -- the flag is now the region's operand, so the `if` peels against it
  subst hv28

  -- `r` survives the write at `r_prime`
  obtain ⟨pr₁₆, hrval₁₆, hrbnd₁₆⟩ :=
    survive (f₁₆.live r.id (by rw [hr_primeptr]; exact fieldLocal_ne_below hnr))
      pr₁₅ hrval₁₅ hrbnd₁₅

  -- %29 `fd_f25519_if( r, flipped_sign_sqrt | flipped_sign_sqrt_i, r_prime, r )`
  obtain ⟨s₁₇, w₁₇, hrun₁₇, hifval, hifbnd⟩ :=
    if_step F₁₆.wf pr₁₆ f₁₆.ptr pr₁₆ f₁₆.val hrval₁₆ f₁₆.bnd hrbnd₁₆ cond
  peel_call hrun₁₇
  clear hrun₁₇
  have F₁₇ : Frame s r s₁₇ := F₁₆.stepOut hnr w₁₇
  clear pr₁₆ hrval₁₆ hrbnd₁₆ pr₁₅ hrval₁₅ hrbnd₁₅

  -- %30 `fd_f25519_abs( r, r )` -- the region's last write
  obtain ⟨s₁₈, w₁₈, hrun₁₈, habsval, habsbnd, habssum⟩ :=
    abs_step F₁₇.wf w₁₇.ptr w₁₇.ptr hifval hifbnd
  peel_call hrun₁₈
  clear hrun₁₈
  have F₁₈ : Frame s r s₁₈ := F₁₇.stepOut hnr w₁₈
  clear hifval hifbnd

  denote_step_reduce v 31 [LLVM.or, LLVM.or?, uv7, uv3]

  iterate 10 peel_lifetime
  simp_return
  simp [hv31]
  clear hv31

  -- `c² · v = u · (u v⁷) ^ ((p-1)/4)`: the classification's left-hand side.
  -- The candidate is the one both backends form, so the algebra behind it is
  -- shared -- `Curve.lean`'s `sqrtCandidate_sq`.
  have hcheckVal :
      (readFieldElem hu * readFieldElem hv ^ 7) ^ 7237005577332262213973186563042994240829374041602535252466099000494570602493 *
              (readFieldElem hu * readFieldElem hv ^ 3) *
            ((readFieldElem hu * readFieldElem hv ^ 7) ^ 7237005577332262213973186563042994240829374041602535252466099000494570602493 *
              (readFieldElem hu * readFieldElem hv ^ 3)) *
          readFieldElem hv
        = readFieldElem hu * (readFieldElem hu * readFieldElem hv ^ 7) ^ ((p - 1) / 4) := by
    rw [← Ed25519.sqrtCandidate_sq (readFieldElem hu) (readFieldElem hv),
      Ed25519.p_sub_five_div_eight]
    ring

  set w := readFieldElem hu * readFieldElem hv ^ 7

  -- `X = w ^ ((p-1)/4)` is *a* square root of `w ^ (p/2)`, so the two
  -- comparisons together say exactly that the latter is `1`
  -- `X = w ^ ((p-1)/4)` is *a* square root of `w ^ (p/2)`, so the two
  -- comparisons together say exactly that the latter is `1`
  have hOr : (w ^ ((p - 1) / 4) = -1 ∨ w ^ ((p - 1) / 4) = 1) ↔ w ^ (p / 2) = 1 :=
    Ed25519.pow_quarter_eq_pm_one_iff w

  constructor

  by_cases hvNZ : readFieldElem hv ≠ 0
  case neg =>
    have hvZ : readFieldElem hv = 0 := of_not_not hvNZ
    rw [hvZ]
    norm_num
    simp [eq_comm (a := readFieldElem hu) (b := 0)]
  by_cases huNZ : readFieldElem hu ≠ 0
  case neg =>
    rw [of_not_not huNZ]
    norm_num

  have squareEq : (∃ x, x ^ 2 * readFieldElem hv = readFieldElem hu)
      ↔ IsSquare (readFieldElem hu / readFieldElem hv) := (Ed25519.isSquare_div_iff hvNZ).symm

  rw [hcheckVal]

  have hwNZ : w ≠ 0 := mul_ne_zero huNZ (pow_ne_zero _ hvNZ)

  have heuNeg : (readFieldElem hu * w ^ ((p - 1) / 4)
        = -readFieldElem hu)
      ↔ (w ^ ((p - 1) / 4) = -1) := by
    constructor
    · intro h
      refine mul_left_cancel₀ huNZ ?_
      rw [h]; ring
    · intro h; rw [h]; ring
  have heuPos : (readFieldElem hu * w ^ ((p - 1) / 4)
        = readFieldElem hu)
      ↔ (w ^ ((p - 1) / 4) = 1) := by
    constructor
    · intro h
      refine mul_left_cancel₀ huNZ ?_
      rw [h]; ring
    · intro h; rw [h]; ring

  simp only [heuNeg, heuPos]

  have hifOr : ((if w ^ ((p - 1) / 4) = -1 then 1#32 else 0#32)
        ||| if w ^ ((p - 1) / 4) = 1 then 1#32 else 0#32)
      = (if w ^ (p / 2) = 1 then 1#32 else 0#32) := by
    rw [or_flag]
    simp only [hOr]

  simp only [hifOr]

  simp only [squareEq, ← ZMod.euler_criterion p hwNZ]

  -- `u v⁷ = (u/v) · v⁸`, so the two differ by the square `v⁸`
  have isSqEq : IsSquare w ↔ IsSquare (readFieldElem hu / readFieldElem hv) :=
    Ed25519.isSquare_mul_pow_seven_iff hvNZ

  simp [isSqEq]

  -- the caller's write reads back exactly what `abs` left at `r`
  have key : ∀ {m : MemoryState} (q : Pointer) (hq : IsFieldElemPtr m q),
      readFieldElem (m := s.mem.splice r (packLimbs fun i => (readLimb i hq : BitVec 64)))
        (isFieldElemPtr_splice hr) = readFieldElem hq := by
    intro m q hq
    rw [readFieldElem_eq_of (readFieldElem?_splice _ hr.left), readFieldElem_eq_decode hq]
    congr 1
    funext i
    simp only [extractLsb'_packLimbs, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (readLimb_lt i hq)

  refine ⟨fun i => (readLimb i w₁₈.ptr : BitVec 64), ?even, ?_, ?zeroV, ?bounds, ?sum,
    ?stateEq⟩

  case even =>
    -- `fd_f25519_abs` returns the representative with an even canonical form:
    -- `p` is odd, so `p - x.val` is even exactly when `x.val` is odd
    have hEven : ∀ x : ZMod p, (if x.val % 2 = 1 then -x else x).val % 2 = 0 := by
      intro x
      have hp2 : p % 2 = 1 := by norm_num [p]
      have hlt : x.val < p := ZMod.val_lt x
      split
      · next h =>
        have hx0 : x ≠ 0 := by rintro rfl; simp at h
        rw [ZMod.neg_val, if_neg hx0]
        omega
      · next h => omega
    rw [key, habsval]
    exact hEven _

  case zeroV =>
    intro v0
    rw [key, habsval, v0]
    norm_num

  case bounds =>
    -- the write copies `abs`'s limbs, which sit at its per-limb bias bound
    refine biasBounds_of_readLimb? _ fun i l hl => ?_
    rw [limbReadbackPack _ _ _ hr.left i, Option.some.injEq] at hl
    subst hl
    simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
    exact le_trans (Nat.mod_le _ _) (habsbnd i)

  case sum =>
    -- ... and each limb is *equal* to `abs`'s, not merely bounded by it: the
    -- readback's `% 2 ^ 64` is inert below the bias bound
    have hlimb : ∀ i : Fin 5,
        readLimb i (m := s.mem.splice r (packLimbs fun i => (readLimb i w₁₈.ptr : BitVec 64)))
          (isFieldElemPtr_splice hr) = readLimb i w₁₈.ptr := by
      intro i
      have hread := limbReadbackPack s.mem r (fun i => (readLimb i w₁₈.ptr : BitVec 64))
        hr.left i
      have hcast : ((readLimb i w₁₈.ptr : BitVec 64)).toNat = readLimb i w₁₈.ptr := by
        simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by have := le_trans (habsbnd i) (biasLimb_le i); omega)
      rw [hcast] at hread
      exact Option.get_of_eq_some _ hread
    rw [limbSum_eq]
    simp only [hlimb]
    rw [← limbSum_eq]
    exact habssum

  case stateEq =>
    -- `r`'s block: untouched until %18, then four writes, each a 320-bit
    -- splice, which `splice_trans` collapses to the last one
    have hlr : ∀ k : Fin 10, (sqrtRatioLocal s k).id ≠ r.id :=
      fun _ => fieldLocal_ne_below hnr
    have hpre : s₆.mem.live? r.id = s.mem.live? r.id :=
      (f₆.live r.id (huv7ptr ▸ hlr 5)).trans <|
      (f₅.live r.id (hv7ptr ▸ hlr 4)).trans <|
      (f₄.live r.id (hv6ptr ▸ hlr 3)).trans <|
      (f₃.live r.id (huv3ptr ▸ hlr 2)).trans <|
      (f₂.live r.id (hv3ptr ▸ hlr 1)).trans <|
      (f₁.live r.id (hv2ptr ▸ hlr 0)).trans (fb r.id hnr)
    obtain ⟨x₇, hx₇⟩ := f₇.splice
    obtain ⟨x₈, hx₈⟩ := f₈.splice
    obtain ⟨x₁₇, hx₁₇⟩ := w₁₇.splice
    obtain ⟨x₁₈, hx₁₈⟩ := w₁₈.splice
    -- %18 and %19
    have h₇ : s₇.mem.live? r.id = (s.mem.splice r x₇).live? r.id :=
      hx₇.trans (live?_splice_congr hpre)
    have h₈ : s₈.mem.live? r.id = (s.mem.splice r x₈).live? r.id := splice_trans s h₇ hx₈
    -- %20 … %27 write locals only, and the three `eq`s write nothing
    have hmid : s₁₆.mem.live? r.id = (s.mem.splice r x₈).live? r.id :=
      ((f₁₆.live r.id (hr_primeptr ▸ hlr 9)).trans <|
        (heq₁₅.live r.id).symm.trans <|
        (heq₁₄.live r.id).symm.trans <|
        (heq₁₃.live r.id).symm.trans <|
        (f₁₂.live r.id (hu_neg_sqrtm1ptr ▸ hlr 8)).trans <|
        (w₁₁.live r.id (hu_negptr ▸ hlr 7)).trans <|
        (f₁₀.live r.id (hcheckptr ▸ hlr 6)).trans
          (f₉.live r.id (hcheckptr ▸ hlr 6))).trans h₈
    -- %29 and %30
    have h₁₇ : s₁₇.mem.live? r.id = (s.mem.splice r x₁₇).live? r.id := splice_trans s hmid hx₁₇
    have h₁₈ : s₁₈.mem.live? r.id = (s.mem.splice r x₁₈).live? r.id := splice_trans s h₁₇ hx₁₈
    -- the limbs read back at `r` are `x₁₈`'s, so the two writes agree
    have hout : packLimbs (fun i => (readLimb i w₁₈.ptr : BitVec 64)) = x₁₈ := by
      rw [show (fun i => ((readLimb i w₁₈.ptr : ℕ) : BitVec 64))
          = fun i => x₁₈.extractLsb' (64 * i.toNat) 64 from ?_, packLimbs_extractLsb']
      funext i
      have := (readLimb?_of_live?_eq h₁₈ i).trans (limbSpliceReadback s.mem r x₁₈ hr.left i)
      simp only [readLimb, Option.get_of_eq_some _ this, BitVec.natCast_eq_ofNat,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [hout]
    exact popFrame_equiv_splice hs hnr F₁₈.live h₁₈


  intro x hx
  rw [key, habsval]
  -- `fd_f25519_abs` only fixes the sign, and the spec squares the result
  have hsign : ∀ {P : Prop} [Decidable P] (y : ZMod p), (if P then -y else y) ^ 2 = y ^ 2 := by
    intro P _ y
    split <;> ring
  rw [hsign]
  -- the branch only chooses the multiplier
  have hif : ∀ {P : Prop} [Decidable P] (y z : ZMod p),
      (if P then y * z else y) = y * (if P then z else 1) := by
    intro P _ y z
    split <;> ring
  rw [hif]
  -- squared, the multiplier is just a sign
  have hmul : ∀ {P : Prop} [Decidable P],
      ((if P then sqrtm1 else 1) : ZMod p) ^ 2 = if P then -1 else 1 := by
    intro P _
    split
    · exact sqrtm1_sq
    · ring
  rw [mul_pow, hmul]

  -- the goal's products, in the shape the algebra above uses
  rw [uv7, uv3]

  by_cases hvNZ : readFieldElem hv ≠ 0
  case neg =>
    have hvZ : readFieldElem hv = 0 := of_not_not hvNZ
    have huZ : readFieldElem hu = 0 := by rw [← hx, hvZ, mul_zero]
    rw [hvZ, mul_zero, huZ]
  by_cases huNZ : readFieldElem hu ≠ 0
  case neg =>
    have huZ : readFieldElem hu = 0 := of_not_not huNZ
    simp [huZ]

  have hchk : checkVal = readFieldElem hu * w ^ ((p - 1) / 4) := hcheckVal
  have hwNZ : w ≠ 0 := by
    show readFieldElem hu * readFieldElem hv ^ 7 ≠ 0
    exact mul_ne_zero huNZ (pow_ne_zero _ hvNZ)

  -- `u = x² v`, so `w = u v⁷ = (x v⁴)²` is a square and Euler applies
  have hwsq : IsSquare w := ⟨x * readFieldElem hv ^ 4, by
    show readFieldElem hu * readFieldElem hv ^ 7 = _
    rw [← hx]; ring⟩
  have hsq : w ^ (p / 2) = 1 := (ZMod.euler_criterion p hwNZ).mp hwsq

  -- `√-1 ≠ -1` and `u ≠ -u`, so at most one comparison fires
  have hsm1_neg : sqrtm1 ≠ -1 := fun h => by
    have h2 := sqrtm1_sq
    rw [h] at h2
    exact absurd (by linear_combination h2 : (2 : ZMod p) = 0) (by decide +kernel)

  rcases hOr.mpr hsq with hk | hk
  · -- `check = -u`: the region flips, and the flip undoes the sign
    rw [if_pos (Or.inr (hchk.trans (by rw [hk]; ring)) : cond)]
    linear_combination -(hcheckVal.trans (by rw [hk]; ring :
      readFieldElem hu * w ^ ((p - 1) / 4) = -readFieldElem hu))
  · -- `check = u`: the region does not flip
    have hcond : ¬ cond := by
      rintro (h | h) <;> rw [hchk, hk, mul_one] at h
      · refine hsm1_neg ?_
        have h1 : (1 : ZMod p) = -sqrtm1 := mul_left_cancel₀ huNZ (by linear_combination h)
        linear_combination h1
      · rcases mul_eq_zero.mp (by linear_combination h : (2 : ZMod p) * readFieldElem hu = 0)
          with h3 | h3
        · exact absurd h3 (by decide +kernel)
        · exact huNZ h3
    rw [if_neg hcond]
    linear_combination hcheckVal.trans (by rw [hk]; ring :
      readFieldElem hu * w ^ ((p - 1) / 4) = readFieldElem hu)

end Firedancer.Ref
