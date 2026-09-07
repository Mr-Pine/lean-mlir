/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_point_frombytes
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.Locals
import SSA.Projects.Firedancer.Ref.Proof.Point
import SSA.Projects.Firedancer.Ref.Proof.RefWF
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_from
import SSA.Projects.Firedancer.Ref.Proof.Step.fd_f25519_add
import SSA.Projects.Firedancer.Ref.Proof.Step.fd_f25519_sub
import SSA.Projects.Firedancer.Ref.Proof.Step.fd_f25519_sgn
import SSA.Projects.Firedancer.Ref.Proof.Step.fd_f25519_mul
import SSA.Projects.Firedancer.Ref.Proof.Step.fd_f25519_sqr
import SSA.Projects.Firedancer.Ref.Proof.Step.fd_f25519_frombytes
import SSA.Projects.Firedancer.Ref.Proof.Step.fd_f25519_sqrt_ratio

/-!
# `fd_ed25519_point_frombytes` conforms to its spec

The region decompresses a point: `frombytes` the buffer into `y`, build the
ratio `u/v = (y²-1)/(d·y²+1)`, take its square root, fix the root's sign
against the buffer's top bit, and write `(x : y : 1 : x·y)` through `r`. If
the ratio is not a square it returns `NULL` and writes nothing.

`State` is the walk's invariant over the five locals; `bb3_run` is the tail
the two sign branches share, and is where the `x = 0` case -- RFC 8032 admits
`(0, y)` with the sign bit set, Dalek rejects it -- is discharged.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- The four coordinate stores miss every other block. -/
theorem live?_pointOutMem_ne {m : MemoryState} {r : Pointer} {b : BlockId}
    {oX oY oZ oT : Fin 5 → BitVec 64} (h : r.id ≠ b) :
    (pointOutMem m r oX oY oZ oT).live? b = m.live? b := by
  simp only [pointOutMem, live?_splice_ne (p := r.withOffset 80) h,
    live?_splice_ne (p := r.withOffset 120) h, live?_splice_ne (p := r.withOffset 40) h,
    live?_splice_ne h]

/-- ... and preserve an agreement on `r`'s. -/
theorem live?_pointOutMem_congr {m m' : MemoryState} {r : Pointer}
    {oX oY oZ oT : Fin 5 → BitVec 64} (h : m.live? r.id = m'.live? r.id) :
    (pointOutMem m r oX oY oZ oT).live? r.id
      = (pointOutMem m' r oX oY oZ oT).live? r.id := by
  simp only [pointOutMem]
  exact live?_splice_congr (live?_splice_congr (live?_splice_congr (live?_splice_congr h)))

/- Scaffolding for the `fd_ed25519_point_frombytes` derivation. -/
namespace PointFromBytes

/-- The five `fd_f25519_t` locals `%17 … %21` allocate. In allocation order
they are the locals `fd_curve25519.c` declares --

    0 x   1 y   2 t   3 u   4 v

-- `x`, `y`, `t` being the point's coordinates and `u`, `v` the ratio
`fd_f25519_sqrt_ratio` takes. -/
abbrev frombytesLocal (s : GlobalState) : Fin 5 → Pointer := fieldLocal s

/-- What holds at every point of the walk: the five locals hold the values
`vx … vv`, the two globals `@fd_f25519_d` and `@fd_f25519_one` still hold `d`
and `1`, the out-parameter `r` is still a point, and every other block the
caller holds -- `buf` -- reads as it did on entry. `r` is the one caller block
the region writes (`fd_ed25519_point_from`, `%37`), so it is carried
separately from the frame clause.

The globals are carried rather than recovered from `live` at each use: the
region reads `d` at `%26` and `1` at `%27`/`%28`/`%37`, and they are constant
throughout, so `pdBelow`/`poneBelow` -- their blocks predate the frame -- is
all a step needs to keep them.

`limbSum ptrx < 2 · p` is deliberately *not* a field: `%35` negates `x`, and
`fiat_25519_opp` of an all-zero limb vector is exactly `2 · p`.  It is only
wanted at `%32`, so it travels beside the state rather than inside it.

`x` is the one local whose bound is not tight: `fd_f25519_frombytes`,
`fd_f25519_sqr`, `fd_f25519_mul`, `fd_f25519_add` and `fd_f25519_sub` all
carry, so `y`, `t`, `u`, `v` are tight from the moment they are written (and
before that they are a fresh, zeroed local). `x` is whatever
`fd_f25519_sqrt_ratio` and `fd_f25519_neg` leave -- the per-limb bias bounds
and `limbSum < 2 · p`, which is exactly `fd_f25519_sgn`'s precondition at
`%32`. -/
structure State (s₀ : GlobalState) (r pd pone : Pointer)
    (vx vy vt vu vv : ZMod _root_.p) (w : GlobalState) : Prop where
  wf : w.WF
  ptrx : IsFieldElemPtr w.mem (frombytesLocal s₀ 0)
  ptry : IsFieldElemPtr w.mem (frombytesLocal s₀ 1)
  ptrt : IsFieldElemPtr w.mem (frombytesLocal s₀ 2)
  ptru : IsFieldElemPtr w.mem (frombytesLocal s₀ 3)
  ptrv : IsFieldElemPtr w.mem (frombytesLocal s₀ 4)
  valx : readFieldElem ptrx = vx
  valy : readFieldElem ptry = vy
  valt : readFieldElem ptrt = vt
  valu : readFieldElem ptru = vu
  valv : readFieldElem ptrv = vv
  bndx : BiasBounds ptrx
  bndy : LimbBounds ptry
  bndt : LimbBounds ptrt
  bndu : LimbBounds ptru
  bndv : LimbBounds ptrv
  /-- `@fd_f25519_d`'s block predates the frame ... -/
  pdBelow : pd.id.id < s₀.alloc.nextFreeBlock
  /-- ... and so does `@fd_f25519_one`'s. -/
  poneBelow : pone.id.id < s₀.alloc.nextFreeBlock
  ptrd : IsFieldElemPtr w.mem pd
  ptrone : IsFieldElemPtr w.mem pone
  vald : readFieldElem ptrd = d
  valone : readFieldElem ptrone = 1
  bndd : LimbBounds ptrd
  bndone : LimbBounds ptrone
  ptr : IsPointPtr w.mem r
  /-- Every caller block reads as it did on entry -- `r` included. The region
  writes `r` only at `%37` (`fd_ed25519_point_from`), the last operation before
  the return, so nothing is lost by keeping the invariant intact up to there
  and handing `%37` to `popFrame_equiv_splice` instead of a `State` step. -/
  live : ∀ b : BlockId, b.id < s₀.alloc.nextFreeBlock →
    w.mem.live? b = s₀.mem.live? b

namespace State

variable {s₀ w w' : GlobalState} {r pd pone : Pointer} {vx vy vt vu vv : ZMod _root_.p}

/-- A caller's field element, at any point of the walk: it is not `r`, and the
locals are above it, so nothing the region wrote reached it. -/
theorem caller (hf : State s₀ r pd pone vx vy vt vu vv w) {q : Pointer} {bound : ℕ}
    (hq : IsFieldElemPtr s₀.mem q) (hb : q.id.id < s₀.alloc.nextFreeBlock)
    (hbnd : LimbBounds hq bound) :
    ∃ hq' : IsFieldElemPtr w.mem q, readFieldElem hq' = readFieldElem hq ∧ LimbBounds hq' bound :=
  let h := hf.live q.id hb
  ⟨isFieldElemPtr_of_live?_eq h hq, carryVal h rfl, carryBnd h hbnd⟩

/-- ... and the byte buffer, which the region only reads. -/
theorem callerBuf (hf : State s₀ r pd pone vx vy vt vu vv w) {q : Pointer}
    (hq : IsByteBufPtr s₀.mem q) (hb : q.id.id < s₀.alloc.nextFreeBlock) :
    ∃ hq' : IsByteBufPtr w.mem q, readBuf hq' = readBuf hq := by
  have hl := hf.live q.id hb
  refine ⟨⟨fits_of_live?_eq hl hq.left, hq.right⟩, ?_⟩
  simp only [readBuf, readBuf?, hl]

/-- A call that only reads -- `fd_f25519_sgn` -- moves nothing. -/
theorem of_equiv (hf : State s₀ r pd pone vx vy vt vu vv w) (he : w ≈ w') :
    State s₀ r pd pone vx vy vt vu vv w' where
  wf := GlobalState.WF.of_equiv hf.wf he
  ptrx := isFieldElemPtr_of_live?_eq (he.live _).symm hf.ptrx
  ptry := isFieldElemPtr_of_live?_eq (he.live _).symm hf.ptry
  ptrt := isFieldElemPtr_of_live?_eq (he.live _).symm hf.ptrt
  ptru := isFieldElemPtr_of_live?_eq (he.live _).symm hf.ptru
  ptrv := isFieldElemPtr_of_live?_eq (he.live _).symm hf.ptrv
  valx := carryVal (he.live _).symm hf.valx
  valy := carryVal (he.live _).symm hf.valy
  valt := carryVal (he.live _).symm hf.valt
  valu := carryVal (he.live _).symm hf.valu
  valv := carryVal (he.live _).symm hf.valv
  bndx := biasBounds_of_live?_eq (he.live _).symm hf.bndx
  bndy := carryBnd (he.live _).symm hf.bndy
  bndt := carryBnd (he.live _).symm hf.bndt
  bndu := carryBnd (he.live _).symm hf.bndu
  bndv := carryBnd (he.live _).symm hf.bndv
  pdBelow := hf.pdBelow
  poneBelow := hf.poneBelow
  ptrd := isFieldElemPtr_of_live?_eq (he.live _).symm hf.ptrd
  ptrone := isFieldElemPtr_of_live?_eq (he.live _).symm hf.ptrone
  vald := carryVal (he.live _).symm hf.vald
  valone := carryVal (he.live _).symm hf.valone
  bndd := carryBnd (he.live _).symm hf.bndd
  bndone := carryBnd (he.live _).symm hf.bndone
  ptr := ⟨fits_equiv he hf.ptr.left, hf.ptr.right⟩
  live := fun b hb => (he.live b).symm.trans (hf.live b hb)

/-! ### One step per local

`stepX … stepV` are the same lemma five times over, differing only in which
field the write lands in: the written local takes the step's value and bound,
the other four carry, and so do the globals, `r` and the frame. -/

variable (hr : r.id.id < s₀.alloc.nextFreeBlock)
include hr

theorem stepX (hf : State s₀ r pd pone vx vy vt vu vv w)
    (st : Wrote (frombytesLocal s₀ 0) w w') {x' : ZMod _root_.p}
    (hv : readFieldElem st.ptr = x') (hb : BiasBounds st.ptr) :
    State s₀ r pd pone x' vy vt vu vv w' where
  wf := st.wf
  ptrx := st.ptr
  ptry := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptry
  ptrt := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptrt
  ptru := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptru
  ptrv := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptrv
  valx := hv
  valy := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valy
  valt := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valt
  valu := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valu
  valv := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valv
  bndx := hb
  bndy := carryBnd (st.live _ (fieldLocal_ne (by decide))) hf.bndy
  bndt := carryBnd (st.live _ (fieldLocal_ne (by decide))) hf.bndt
  bndu := carryBnd (st.live _ (fieldLocal_ne (by decide))) hf.bndu
  bndv := carryBnd (st.live _ (fieldLocal_ne (by decide))) hf.bndv
  pdBelow := hf.pdBelow
  poneBelow := hf.poneBelow
  ptrd := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne_below hf.pdBelow)) hf.ptrd
  ptrone :=
    isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne_below hf.poneBelow)) hf.ptrone
  vald := carryVal (st.live _ (fieldLocal_ne_below hf.pdBelow)) hf.vald
  valone := carryVal (st.live _ (fieldLocal_ne_below hf.poneBelow)) hf.valone
  bndd := carryBnd (st.live _ (fieldLocal_ne_below hf.pdBelow)) hf.bndd
  bndone := carryBnd (st.live _ (fieldLocal_ne_below hf.poneBelow)) hf.bndone
  ptr := ⟨fits_of_live?_eq (st.live _ (fieldLocal_ne_below hr)) hf.ptr.left, hf.ptr.right⟩
  live := fun b hb' => (st.live b (fieldLocal_ne_below hb')).trans (hf.live b hb')

theorem stepY (hf : State s₀ r pd pone vx vy vt vu vv w)
    (st : Wrote (frombytesLocal s₀ 1) w w') {y' : ZMod _root_.p}
    (hv : readFieldElem st.ptr = y') (hb : LimbBounds st.ptr) :
    State s₀ r pd pone vx y' vt vu vv w' where
  wf := st.wf
  ptrx := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptrx
  ptry := st.ptr
  ptrt := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptrt
  ptru := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptru
  ptrv := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptrv
  valx := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valx
  valy := hv
  valt := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valt
  valu := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valu
  valv := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valv
  bndx := biasBounds_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.bndx
  bndy := hb
  bndt := carryBnd (st.live _ (fieldLocal_ne (by decide))) hf.bndt
  bndu := carryBnd (st.live _ (fieldLocal_ne (by decide))) hf.bndu
  bndv := carryBnd (st.live _ (fieldLocal_ne (by decide))) hf.bndv
  pdBelow := hf.pdBelow
  poneBelow := hf.poneBelow
  ptrd := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne_below hf.pdBelow)) hf.ptrd
  ptrone :=
    isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne_below hf.poneBelow)) hf.ptrone
  vald := carryVal (st.live _ (fieldLocal_ne_below hf.pdBelow)) hf.vald
  valone := carryVal (st.live _ (fieldLocal_ne_below hf.poneBelow)) hf.valone
  bndd := carryBnd (st.live _ (fieldLocal_ne_below hf.pdBelow)) hf.bndd
  bndone := carryBnd (st.live _ (fieldLocal_ne_below hf.poneBelow)) hf.bndone
  ptr := ⟨fits_of_live?_eq (st.live _ (fieldLocal_ne_below hr)) hf.ptr.left, hf.ptr.right⟩
  live := fun b hb' => (st.live b (fieldLocal_ne_below hb')).trans (hf.live b hb')

theorem stepT (hf : State s₀ r pd pone vx vy vt vu vv w)
    (st : Wrote (frombytesLocal s₀ 2) w w') {t' : ZMod _root_.p}
    (hv : readFieldElem st.ptr = t') (hb : LimbBounds st.ptr) :
    State s₀ r pd pone vx vy t' vu vv w' where
  wf := st.wf
  ptrx := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptrx
  ptry := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptry
  ptrt := st.ptr
  ptru := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptru
  ptrv := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptrv
  valx := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valx
  valy := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valy
  valt := hv
  valu := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valu
  valv := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valv
  bndx := biasBounds_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.bndx
  bndy := carryBnd (st.live _ (fieldLocal_ne (by decide))) hf.bndy
  bndt := hb
  bndu := carryBnd (st.live _ (fieldLocal_ne (by decide))) hf.bndu
  bndv := carryBnd (st.live _ (fieldLocal_ne (by decide))) hf.bndv
  pdBelow := hf.pdBelow
  poneBelow := hf.poneBelow
  ptrd := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne_below hf.pdBelow)) hf.ptrd
  ptrone :=
    isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne_below hf.poneBelow)) hf.ptrone
  vald := carryVal (st.live _ (fieldLocal_ne_below hf.pdBelow)) hf.vald
  valone := carryVal (st.live _ (fieldLocal_ne_below hf.poneBelow)) hf.valone
  bndd := carryBnd (st.live _ (fieldLocal_ne_below hf.pdBelow)) hf.bndd
  bndone := carryBnd (st.live _ (fieldLocal_ne_below hf.poneBelow)) hf.bndone
  ptr := ⟨fits_of_live?_eq (st.live _ (fieldLocal_ne_below hr)) hf.ptr.left, hf.ptr.right⟩
  live := fun b hb' => (st.live b (fieldLocal_ne_below hb')).trans (hf.live b hb')

theorem stepU (hf : State s₀ r pd pone vx vy vt vu vv w)
    (st : Wrote (frombytesLocal s₀ 3) w w') {u' : ZMod _root_.p}
    (hv : readFieldElem st.ptr = u') (hb : LimbBounds st.ptr) :
    State s₀ r pd pone vx vy vt u' vv w' where
  wf := st.wf
  ptrx := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptrx
  ptry := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptry
  ptrt := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptrt
  ptru := st.ptr
  ptrv := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptrv
  valx := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valx
  valy := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valy
  valt := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valt
  valu := hv
  valv := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valv
  bndx := biasBounds_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.bndx
  bndy := carryBnd (st.live _ (fieldLocal_ne (by decide))) hf.bndy
  bndt := carryBnd (st.live _ (fieldLocal_ne (by decide))) hf.bndt
  bndu := hb
  bndv := carryBnd (st.live _ (fieldLocal_ne (by decide))) hf.bndv
  pdBelow := hf.pdBelow
  poneBelow := hf.poneBelow
  ptrd := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne_below hf.pdBelow)) hf.ptrd
  ptrone :=
    isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne_below hf.poneBelow)) hf.ptrone
  vald := carryVal (st.live _ (fieldLocal_ne_below hf.pdBelow)) hf.vald
  valone := carryVal (st.live _ (fieldLocal_ne_below hf.poneBelow)) hf.valone
  bndd := carryBnd (st.live _ (fieldLocal_ne_below hf.pdBelow)) hf.bndd
  bndone := carryBnd (st.live _ (fieldLocal_ne_below hf.poneBelow)) hf.bndone
  ptr := ⟨fits_of_live?_eq (st.live _ (fieldLocal_ne_below hr)) hf.ptr.left, hf.ptr.right⟩
  live := fun b hb' => (st.live b (fieldLocal_ne_below hb')).trans (hf.live b hb')

theorem stepV (hf : State s₀ r pd pone vx vy vt vu vv w)
    (st : Wrote (frombytesLocal s₀ 4) w w') {v' : ZMod _root_.p}
    (hv : readFieldElem st.ptr = v') (hb : LimbBounds st.ptr) :
    State s₀ r pd pone vx vy vt vu v' w' where
  wf := st.wf
  ptrx := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptrx
  ptry := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptry
  ptrt := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptrt
  ptru := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.ptru
  ptrv := st.ptr
  valx := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valx
  valy := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valy
  valt := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valt
  valu := carryVal (st.live _ (fieldLocal_ne (by decide))) hf.valu
  valv := hv
  bndx := biasBounds_of_live?_eq (st.live _ (fieldLocal_ne (by decide))) hf.bndx
  bndy := carryBnd (st.live _ (fieldLocal_ne (by decide))) hf.bndy
  bndt := carryBnd (st.live _ (fieldLocal_ne (by decide))) hf.bndt
  bndu := carryBnd (st.live _ (fieldLocal_ne (by decide))) hf.bndu
  bndv := hb
  pdBelow := hf.pdBelow
  poneBelow := hf.poneBelow
  ptrd := isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne_below hf.pdBelow)) hf.ptrd
  ptrone :=
    isFieldElemPtr_of_live?_eq (st.live _ (fieldLocal_ne_below hf.poneBelow)) hf.ptrone
  vald := carryVal (st.live _ (fieldLocal_ne_below hf.pdBelow)) hf.vald
  valone := carryVal (st.live _ (fieldLocal_ne_below hf.poneBelow)) hf.valone
  bndd := carryBnd (st.live _ (fieldLocal_ne_below hf.pdBelow)) hf.bndd
  bndone := carryBnd (st.live _ (fieldLocal_ne_below hf.poneBelow)) hf.bndone
  ptr := ⟨fits_of_live?_eq (st.live _ (fieldLocal_ne_below hr)) hf.ptr.left, hf.ptr.right⟩
  live := fun b hb' => (st.live b (fieldLocal_ne_below hb')).trans (hf.live b hb')

end State

theorem bb3_run {s : GlobalState} {r buf pd pone : Pointer} {ret : SLLVM.Ptr}
    (hs : s.WF)
    (hr : IsPointPtr s.mem r) (hbuf : IsByteBufPtr s.mem buf)
    (hnr : r.id.id < s.alloc.nextFreeBlock) (hret : ret = PoisonOr.value r)
    (V : fd_ed25519_point_frombytes.Γout.Valuation) (w : GlobalState) (xv : ZMod _root_.p)
    (hvx : V (⟨13, by rfl⟩ : fd_ed25519_point_frombytes.Γout.Var SLLVM.Ty.ptr)
      = .value (frombytesLocal s 0))
    (hvy : V (⟨12, by rfl⟩ : fd_ed25519_point_frombytes.Γout.Var SLLVM.Ty.ptr)
      = .value (frombytesLocal s 1))
    (hvt : V (⟨11, by rfl⟩ : fd_ed25519_point_frombytes.Γout.Var SLLVM.Ty.ptr)
      = .value (frombytesLocal s 2))
    (hvone : V (⟨17, by rfl⟩ : fd_ed25519_point_frombytes.Γout.Var SLLVM.Ty.ptr)
      = .value pone)
    (hvr : V (⟨32, by rfl⟩ : fd_ed25519_point_frombytes.Γout.Var SLLVM.Ty.ptr) = .value r)
    -- `%37` writes `r`; `@fd_f25519_one` is the one *global* it reads, so it
    -- has to be known apart from `r`
    (hponer : pone.id ≠ r.id)
    (state : State s r pd pone xv (decodeBytes (readBuf hbuf)) 0
      (decodeBytes (readBuf hbuf) ^ 2 - 1) (d * decodeBytes (readBuf hbuf) ^ 2 + 1) w)
    (refWF : w.RefWF [r, frombytesLocal s 0, frombytesLocal s 1, frombytesLocal s 2,
      frombytesLocal s 3, frombytesLocal s 4])
    -- what `x` is worth on entry: a root of the ratio, with the requested sign
    -- except at `0` (`fd_f25519_neg` fixes no sign there)
    (hsq : xv ^ 2 * (d * decodeBytes (readBuf hbuf) ^ 2 + 1)
      = decodeBytes (readBuf hbuf) ^ 2 - 1)
    (hsgn : xv = 0 ∨ ((xv.val % 2 = 0) ↔ (readBuf hbuf)[255] = false)) :
    ∃ s' : GlobalState,
      StateT.run (fd_ed25519_point_frombytes.blocks.run V
          { ts := [], idx := 2, hidx := by rfl, args := HVector.nil }) w
        = .value (ret ::ₕ HVector.nil, s')
      ∧ ret = PoisonOr.value r
      ∧ ∃ oX oY oZ oT : Fin 5 → BitVec 64,
          (s.popFrame s'.mem : GlobalState)
              ≈ ({ alloc := s.alloc, mem := pointOutMem s.mem r oX oY oZ oT,
                   globals := s.globals } : GlobalState)
          ∧ DecodesTo s.mem r buf hr hbuf oX oY oZ oT := by
  have hmapnil : ∀ {α : Type} {A B : α → Type} (f : (a : α) → A a → B a),
      HVector.map f (.nil : HVector A []) = .nil := fun _ => rfl
  denote_enter_block

  obtain ⟨w₁, hrun₁, f₁⟩ :=
    mul_step state.wf state.ptrt state.ptrx state.ptry state.valx state.valy
      state.bndx.loose state.bndy.loose
  peel_call hrun₁ with hmapnil, hvx, hvy, hvt
  clear hrun₁
  have state₁ := state.stepT hnr f₁.wrote f₁.val f₁.bnd
  have refWF₁ := refWF.wrote (by simp) f₁.wrote

  obtain ⟨oX, oY, oZ, oT, ⟨w₂, hrun₂, heq₂⟩, hlX, hlY, hlT, hlZ⟩ :=
  fd_ed25519_point_from_conforms r (frombytesLocal s 0) (frombytesLocal s 1) pone
    (frombytesLocal s 2) w₁ state₁.wf
    (fieldLocal_ne_below hnr) (fieldLocal_ne_below hnr) hponer
    (fieldLocal_ne_below hnr)
    state₁.ptr state₁.ptrx state₁.ptry state₁.ptrone state₁.ptrt
  peel_call hrun₂ with hmapnil, hvx, hvy, hvt, hvr, hvone

  simp [BlockCom.denote_term, Terminator.denote_br,
      simp_denote, simp_sllvm]
  denote_enter_block
  iterate 5 peel_lifetime
  simp_return
  simp [hvr, hret]

  refine ⟨fun i => oX.extractLsb' (64 * i.toNat) 64,
          fun i => oY.extractLsb' (64 * i.toNat) 64,
          fun i => oZ.extractLsb' (64 * i.toNat) 64,
          fun i => oT.extractLsb' (64 * i.toNat) 64, ?_⟩
  simp only [pointOutMem, packLimbs_extractLsb']

  set y := decodeBytes (readBuf hbuf)

  let point : Point := ⟨xv, y, 1, (xv * y)⟩

  -- `r`'s block reads the same in `w₁` as on entry: `%37` is the only write to
  -- it, and it is the same four splices on either memory.
  have hrlive :=
    live?_splice_congr (p := r.withOffset 80) (x := oT)
      (live?_splice_congr (p := r.withOffset 120) (x := oZ)
        (live?_splice_congr (p := r.withOffset 40) (x := oY)
          (live?_splice_congr (p := r) (x := oX) (state₁.live r.id hnr))))

  refine ⟨?state, ?_⟩
  case state =>
    refine popFrame_equiv_block (o := r.id) hs hnr (fun b hb hbo => ?_) (fun b hbo => ?_)
      ((heq₂.live r.id).symm.trans hrlive)
    · rw [← heq₂.live b]
      simpa [Ne.symm hbo] using state₁.live b hb
    · simp [Ne.symm hbo]

  have hpt : IsPointPtr (pointOutMem s.mem r (fun i => oX.extractLsb' (64 * i.toNat) 64)
      (fun i => oY.extractLsb' (64 * i.toNat) 64) (fun i => oZ.extractLsb' (64 * i.toNat) 64)
      (fun i => oT.extractLsb' (64 * i.toNat) 64)) r :=
    isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr)))
  show IsDecoding (readPoint hpt) (readBuf hbuf)
  -- `hpt` reads the point out of `s.mem`; the four writes `hlX`--`hlZ`
  -- describe land on `w₁.mem`. Both memories agree on `r`'s block -- the
  -- region touches it only through `%37` -- so they read the same point.
  have hptw : IsPointPtr ((((w₁.mem.splice r oX).splice (r.withOffset 40) oY).splice
      (r.withOffset 120) oZ).splice (r.withOffset 80) oT) r :=
    isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice state₁.ptr)))
  have hcongr : readPoint hpt = readPoint hptw := by
    refine readPoint_of_live?_eq ?_ hptw hpt
    simp only [pointOutMem, packLimbs_extractLsb']
    exact hrlive.symm
  -- the four coordinates are the field elements `%36`/`%37` copied in
  have hXv := (readFieldElem_eq_of_readLimb hlX).trans state₁.valx
  have hYv := (readFieldElem_eq_of_readLimb hlY).trans state₁.valy
  have hTv := (readFieldElem_eq_of_readLimb hlT).trans state₁.valt
  have hZv := (readFieldElem_eq_of_readLimb hlZ).trans state₁.valone
  have hpoint : readPoint hpt = point := hcongr.trans (readPoint_eq_of hptw hXv hYv hTv hZv)
  rw [hpoint]
  refine ⟨?_, (by simp [point]), by simp [point, y], by simp [point, Point.x, Point.y], ?xsign⟩

  case xsign =>
    simp [point]
    intro h
    simp [h] at hsgn
    exact hsgn

  simp [point, Point.x, Point.y, OnCurve]
  linear_combination -hsq

end PointFromBytes

open PointFromBytes in
set_option maxHeartbeats 3200000 in
theorem fd_ed25519_point_frombytes_conforms (r buf : Pointer) (s : GlobalState)
    -- well-formed, with `@fd_f25519_d`, `@fd_f25519_one` and `@fd_f25519_sqrtm1`
    -- loaded and none of them `r`, the one caller block the region writes
    (hm : s.RefWF [r])
    (hr : IsPointPtr s.mem r)
    (hbuf : IsByteBufPtr s.mem buf)
    -- `%37` writes `r` and `%22`/`%24` read `buf`; the spec is stated over
    -- `readBuf hbuf` at the entry state, so the two are kept apart
    (hbufr : buf.id ≠ r.id) :
    fd_ed25519_point_frombytes_spec r buf s hr hbuf := by
  simp only [fd_ed25519_point_frombytes_spec, Cfg.denote]

  let bufBytes := readBuf hbuf
  let y := decodeBytes bufBytes
  let u := y^2 - 1
  let v := d * y^2 + 1
  set returnValue := if ∃ x, x^2 * v = u then .value r else SLLVM.Ptr.null with hreturnValue

  apply existsISecond returnValue
  refine run_runFunction' _ ?_

  have hs := hm.wf
  obtain ⟨pd, hgd, hapartd⟩ := hm.gd
  obtain ⟨pone, hgone, hapartone⟩ := hm.gone
  have hpd := hgd.ptr; have hd := hgd.value; have hdlimbs := hgd.bnd
  have hpone := hgone.ptr; have hone := hgone.value; have honelimbs := hgone.bnd
  have hglobne₁ : pd.id ≠ r.id := hapartd r (by simp)
  have hglobne₂ : pone.id ≠ r.id := hapartone r (by simp)

  denote_step_reduce v 6 [LLVM.const?, insertvalue] fold
  peel_addressof hgd.addr
  denote_step_reduce v 12 [LLVM.const?, insertvalue] fold
  peel_addressof hgone.addr
  denote_step_reduce v 16 [LLVM.const?, insertvalue] fold

  -- Everything the caller can address predates the frame, so no `alloca` of
  -- the chain touches it.
  have hnr : r.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hr.left
  have hnbuf : buf.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hbuf.left
  have hnd : pd.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hpd.left
  have hnone : pone.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hpone.left

  -- The frame, while `s.allocaChain fieldW 5` is still transparent: left
  -- exposed it is five `HashMap` inserts, and defeq walks them on every `live?`.
  have fb : FrameBelow s.alloc.nextFreeBlock s (s.allocaChain fieldW 5) :=
    FrameBelow.allocaChain (le_refl _) (FrameBelow.refl _ _) 5
  have hwf : (s.allocaChain fieldW 5).WF := GlobalState.WF.allocaChain hs 5
  have hlf : ∀ k : Fin 5,
      Fits (s.allocaChain fieldW 5).mem (frombytesLocal s k) 320 :=
    fun k => GlobalState.fits_chainPtr k.isLt
  have hrc : IsPointPtr (s.allocaChain fieldW 5).mem r :=
    ⟨fits_of_live?_eq (fb r.id hnr) hr.left, hr.right⟩

  -- a fresh local reads back as five zero limbs
  have hz : ∀ (k : Fin 5) (i : Fin 5),
      readLimb? (frombytesLocal s k) i (s.allocaChain fieldW 5).mem = some 0 := by
    intro k i
    simp only [fieldLocal]
    rw [readLimb?_of_live?_eq (GlobalState.live?_allocaChain_of_lt 5 k.isLt)]
    exact readLimb?_afterAlloca_self (s.allocaChain fieldW k.val) i

  set sLocals : GlobalState := s.allocaChain fieldW 5 with hsLocals
  clear_value sLocals

  -- %17 … %21, folded to `frombytesLocal s k` and sealed as `sLocals`
  peel_alloca_chain s, fieldW, 5
  fold_cells s, fieldW, frombytesLocal, 5
  rw [← hsLocals]

  -- the stepper's `v0`, `v2 … v6`, `v8 … v12`: the alloca count, and the
  -- `@fd_f25519_d` / `@fd_f25519_one` initialisers the region materialises and
  -- never reads. `v14`, `v15`, `v16` -- `0#32`, `NULL`, `7#8` -- are read, at
  -- `%30`, the `cond_br` and `%31`.
  denote_clear v 0 0
  denote_clear v 2 6
  denote_clear v 8 12

  -- `fd_curve25519.c`'s names for the five locals; `p`-prefixed, since the
  -- field values `y`, `u`, `v` are already in scope.
  set px := frombytesLocal s 0 with hpxptr
  set py := frombytesLocal s 1 with hpyptr
  set pt := frombytesLocal s 2 with hptptr
  set pu := frombytesLocal s 3 with hpuptr
  set pv := frombytesLocal s 4 with hpvptr

  -- `%17`, `%18`, `%19`, up to the `fd_f25519_frombytes` call
  peel_lifetime
  peel_lifetime
  peel_lifetime

  -- the frame on entry: five fresh locals, all zero, `r` and everything else
  -- the caller holds exactly as it was
  have hploc : ∀ k : Fin 5, IsFieldElemPtr sLocals.mem (frombytesLocal s k) :=
    fun k => ⟨hlf k, by simp [fieldLocal]⟩
  have F₀ : State s r pd pone 0 0 0 0 0 sLocals := {
    wf := hwf
    ptrx := hploc 0
    ptry := hploc 1
    ptrt := hploc 2
    ptru := hploc 3
    ptrv := hploc 4
    valx := readFieldElem_eq_of (by simp [readFieldElem?, hz 0, decodeFieldElem])
    valy := readFieldElem_eq_of (by simp [readFieldElem?, hz 1, decodeFieldElem])
    valt := readFieldElem_eq_of (by simp [readFieldElem?, hz 2, decodeFieldElem])
    valu := readFieldElem_eq_of (by simp [readFieldElem?, hz 3, decodeFieldElem])
    valv := readFieldElem_eq_of (by simp [readFieldElem?, hz 4, decodeFieldElem])
    bndx := biasBounds_of_readLimb? _ fun i l hl => by
      rw [hz 0 i, Option.some.injEq] at hl; have := tight_le_biasLimb i; omega
    bndy := limbBounds_of_readLimb? _ fun i l hl => by rw [hz 1 i, Option.some.injEq] at hl; omega
    bndt := limbBounds_of_readLimb? _ fun i l hl => by rw [hz 2 i, Option.some.injEq] at hl; omega
    bndu := limbBounds_of_readLimb? _ fun i l hl => by rw [hz 3 i, Option.some.injEq] at hl; omega
    bndv := limbBounds_of_readLimb? _ fun i l hl => by rw [hz 4 i, Option.some.injEq] at hl; omega
    pdBelow := hnd
    poneBelow := hnone
    ptrd := isFieldElemPtr_of_live?_eq (fb pd.id hnd) hpd
    ptrone := isFieldElemPtr_of_live?_eq (fb pone.id hnone) hpone
    vald := carryVal (fb pd.id hnd) hd
    valone := carryVal (fb pone.id hnone) hone
    bndd := carryBnd (fb pd.id hnd) hdlimbs
    bndone := carryBnd (fb pone.id hnone) honelimbs
    ptr := hrc
    live := fun b hb => fb b hb }
  -- `RefWF` over the frame: the globals are below the entry counter and the
  -- five locals are at or above it, so the list can name every pointer the
  -- rest of the walk writes through -- and then `RefWF.wrote` is the whole
  -- carry.
  have widen : ∀ {name : String} {val : ZMod p},
      (∃ q, FieldGlobal s name q val ∧ Apart q [r]) →
      (∃ q, FieldGlobal sLocals name q val ∧ Apart q [r, px, py, pt, pu, pv]) := by
    rintro name val ⟨q, hg, hq⟩
    have hbq : q.id.id < s.alloc.nextFreeBlock := hg.below hm.wf
    have hlive : sLocals.mem.live? q.id = s.mem.live? q.id := fb q.id hbq
    refine ⟨q, ⟨?_, isFieldElemPtr_of_live?_eq hlive hg.ptr, carryVal hlive hg.value,
      carryBnd hlive hg.bnd⟩, ?_⟩
    · show GlobalPtr sLocals name q
      simp only [GlobalPtr, hsLocals]
      exact hg.addr
    · intro pp hpp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpp
      have hqr : q.id ≠ r.id := hq r (by simp)
      rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hqr
      all_goals exact Ne.symm (fieldLocal_ne_below hbq)
  have hm₀ : sLocals.RefWF [r, px, py, pt, pu, pv] :=
    ⟨hwf, widen hm.gd, widen hm.gone, widen hm.gm1⟩


  -- the frame is sealed in `F₀` now; the raw chain facts are spent
  clear hz hploc hlf hrc hwf fb hsLocals

  -- `buf` at any point of the walk: the region only reads it
  have bufAt : ∀ {w : GlobalState} {a b c e f : ZMod p},
      State s r pd pone a b c e f w →
      ∃ h : IsByteBufPtr w.mem buf, readBuf h = readBuf hbuf :=
    fun F => F.callerBuf hbuf hnbuf

  -- %22 `fd_f25519_frombytes( y, buf )`
  obtain ⟨hbuf₀, hbufval₀⟩ := bufAt F₀
  obtain ⟨s₁, f₁, hrun₁, hval₁, hbnd₁⟩ := frombytes_step F₀.wf F₀.ptry hbuf₀
  peel_call hrun₁
  clear hrun₁
  -- state the local's value over the *entry* buffer, which is what the spec reads
  rw [hbufval₀] at hval₁
  have S₁ : State s r pd pone 0 y 0 0 0 s₁ := F₀.stepY hnr f₁ hval₁ hbnd₁
  have hm₁ := hm₀.wrote (by simp [hpxptr, hpyptr, hptptr, hpuptr, hpvptr]) f₁
  clear f₁ hval₁ hbnd₁ hbuf₀ hbufval₀ F₀

  -- %23 `getelementptr( buf, 31 )` -- the byte the sign rides in
  obtain ⟨hbuf₁, hbufval₁⟩ := bufAt S₁
  -- the index operand is `%1`, from the entry's constant fold
  subst hv1
  peel_gep 31 with buf, hbuf₁.left, s₁ as bufTop

  -- %24 `load i8`
  obtain ⟨blk, hblkTop, hblklenTop⟩ := hbufTop
  -- `peel_gep` states the remaining `Fits` with `bufTop` unfolded; `omega`
  -- needs it as the atom the load's obligation is about
  have hfit8 : bufTop.offsetInBits + 8 ≤ blk.lengthInBits := by
    simpa [bufTop] using hblklenTop
  peel_load (.bitvec (.concrete 8)), blk, bufTop, hblkTop, s₁
  -- `blk` and `hblkTop` stay: the loaded byte is `blk.bytes`, and `hbufval₁`
  -- is what will tie it back to `readBuf hbuf`
  clear hblklenTop hfit8

  -- %25 `fd_f25519_sqr( u, y )` -- `u = y²`, after the `%20`/`%21` lifetimes
  peel_lifetime
  peel_lifetime
  obtain ⟨s₂, hrun₂, f₂⟩ := sqr_step S₁.wf S₁.ptru S₁.ptry S₁.valy S₁.bndy.loose
  peel_call hrun₂
  clear hrun₂
  have S₂ : State s r pd pone 0 y 0 (y ^ 2) 0 s₂ :=
    S₁.stepU hnr f₂.wrote (by rw [f₂.val]; ring) f₂.bnd
  have hm₂ := hm₁.wrote (by simp [hpxptr, hpyptr, hptptr, hpuptr, hpvptr]) f₂.wrote
  clear f₂ S₁

  -- %26 `fd_f25519_mul( v, u, d )` -- `v = d·y²`
  obtain ⟨s₃, hrun₃, f₃⟩ :=
    mul_step S₂.wf S₂.ptrv S₂.ptru S₂.ptrd S₂.valu S₂.vald
      S₂.bndu.loose S₂.bndd.loose
  peel_call hrun₃
  clear hrun₃
  have S₃ : State s r pd pone 0 y 0 (y ^ 2) (d * y ^ 2) s₃ :=
    S₂.stepV hnr f₃.wrote (by rw [f₃.val]; ring) f₃.bnd
  have hm₃ := hm₂.wrote (by simp [hpxptr, hpyptr, hptptr, hpuptr, hpvptr]) f₃.wrote
  clear f₃ S₂ hm₂

  -- %27 `fd_f25519_sub( u, u, 1 )` -- `u = y² - 1`
  obtain ⟨s₄, hrun₄, f₄⟩ :=
    sub_step S₃.wf S₃.ptru S₃.ptru S₃.ptrone S₃.valu S₃.valone
      S₃.bndu S₃.bndone.bias
  peel_call hrun₄
  clear hrun₄
  have S₄ : State s r pd pone 0 y 0 u (d * y ^ 2) s₄ :=
    S₃.stepU hnr f₄.wrote (by rw [f₄.val];) f₄.bnd
  have hm₄ := hm₃.wrote (by simp [hpxptr, hpyptr, hptptr, hpuptr, hpvptr]) f₄.wrote
  clear f₄ S₃ hm₃

  -- %28 `fd_f25519_add( v, v, 1 )` -- `v = d·y² + 1`
  obtain ⟨s₅, hrun₅, f₅⟩ :=
    add_step S₄.wf S₄.ptrv S₄.ptrv S₄.ptrone S₄.valv S₄.valone
      S₄.bndv S₄.bndone
  peel_call hrun₅
  clear hrun₅
  have S₅ : State s r pd pone 0 y 0 u v s₅ :=
    S₄.stepV hnr f₅.wrote (by rw [f₅.val];) f₅.bnd
  have hm₅ := hm₄.wrote (by simp [hpxptr, hpyptr, hptptr, hpuptr, hpvptr]) f₅.wrote
  clear f₅ S₄ hm₄

  -- %29 `fd_f25519_sqrt_ratio( x, u, v )` -- the root, and the flag `%30`
  -- branches on. `@fd_f25519_sqrtm1` is the callee's own `addressof`; it
  -- reaches here because `Wrote.globals` carries the symbol table.
  obtain ⟨pm1, hgm1, hapartm1⟩ := hm₅.gm1
  obtain ⟨s₆, w₆, root, hrun₆, hval₆, heven₆, hsq₆, hzero₆, hbnd₆, hsum₆⟩ :=
    sqrtRatio_step S₅.wf S₅.ptrx S₅.ptru S₅.ptrv hgm1 (hapartm1 px (by simp))
      S₅.valu S₅.valv S₅.bndu S₅.bndv
      (fieldLocal_ne (by decide)) (fieldLocal_ne (by decide))
  peel_call hrun₆
  clear hrun₆
  -- `fd_f25519_sqrt_ratio` leaves the loose bound, not the tight one -- which
  -- is what `State`'s per-limb `bndx`/`sumx` are for
  have S₆ : State s r pd pone root y 0 u v s₆ :=
    S₅.stepX hnr w₆ hval₆ hbnd₆
  have hm₆ := hm₅.wrote (by simp [hpxptr, hpyptr, hptptr, hpuptr, hpvptr]) w₆
  clear S₅ hm₅

  denote_step_reduce v 30 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', hv14]

  -- `%29`'s flag is `1` exactly when the ratio is a square, so `%30` -- the
  -- test against `0` -- holds in the *non*-square case, and that is the edge
  -- to `^bb4`, the `NULL` return. `^bb1` is the square case.
  by_cases squareness : ∃ x, x ^ 2 * v = u
  case neg =>
    rw [if_neg squareness] at hreturnValue hv30
    simp only [hv30, BlockCom.denote_term, Terminator.denote_condBr_value,
      simp_denote, simp_sllvm]
    denote_enter_block
    iterate 5 peel_lifetime
    simp_return
    simp [hv15, hreturnValue]
    have isNotSquare : ¬ IsSquare (u / v) := fun hs =>
      squareness ((isSquare_div_iff (denom_ne_zero y)).mp hs)
    refine ⟨fun _ => ?_, 0, 0, 0, 0, fun hsq' => absurd hsq' isNotSquare⟩
    exact (FrameBelow.popFrame_equiv hs (fun b hb => S₆.live b hb)).symm

  rw [if_pos squareness] at hreturnValue hv30 ⊢
  simp [squareness] at hsq₆
  simp only [hv30, BlockCom.denote_term, Terminator.denote_condBr_value,
    simp_denote, simp_sllvm]
  denote_enter_block

  have isSquare : IsSquare (u / v) :=
    (isSquare_div_iff (denom_ne_zero y)).mpr squareness
  -- `simp` matches syntactically, and `u`/`v` are `let`s the *goal* never
  -- mentions -- so restate the fact in the goal's own vocabulary (defeq, hence
  -- `:= isSquare`) and both implications collapse: the `¬IsSquare` conjunct
  -- disappears and the `IsSquare` one loses its hypothesis.
  have isSquare' : IsSquare ((decodeBytes (readBuf hbuf) ^ 2 - 1)
      / (d * decodeBytes (readBuf hbuf) ^ 2 + 1)) := isSquare
  simp only [isSquare', not_true, false_implies, true_implies, true_and]
  simp at hv30
  clear isSquare isSquare' squareness

  -- The stepper reads its index off the valuation *depth*, and treats a base
  -- built by `ofHVector`/`singleton` as contributing `0` -- matching MLIR,
  -- where `%arg0`/`%arg1` are not numbered. Entering `^bb1` normalised that
  -- base into a plain `cons` spine, so the two block arguments started
  -- counting and every index gained `2`. Re-anchor: the value at depth `33`
  -- is `%31`.
  have := denoteNumbering 31 33

  -- A tail block's valuation is `blockArgs ++ ambient`, and `^bb1` takes no
  -- arguments -- so the left factor is `(HVector.map V .nil).reverse`.
  -- `HVector` has `map_cons` but no `map_nil`, so that never collapses,
  -- `simp_peephole` cannot project the operands out, and the reduction stalls
  -- one stage *before* the shift. Supply the missing lemma.
  --
  -- TODO: this belongs in `LeanMLIR/HVector.lean`, as `@[simp] map_nil`
  -- beside `map_cons` -- it is `rfl`, and `map'` already carries both
  -- `map'_cons` and `map'_nil`. With it a `simp` lemma, every argument-less
  -- tail block reduces on its own: this call site, `^bb2` and `^bb3` below,
  -- and the valuation normalisation that forced the `denoteNumbering`
  -- re-anchor above.
  have hmapnil : ∀ {α : Type} {A B : α → Type} (f : (a : α) → A a → B a),
      HVector.map f (.nil : HVector A []) = .nil := fun _ => rfl

  denote_step_reduce v 31 [LLVM.lshr, LLVM.lshr?, hmapnil, hv16]

  -- %32 `fd_f25519_sgn( x )`
  --
  obtain ⟨s₇, hrun₇, heq₇⟩ := sgn_step S₆.wf S₆.ptrx S₆.valx S₆.bndx hsum₆
  peel_call hrun₇
  clear hrun₇
  have S₇ := S₆.of_equiv heq₇
  have hm₇ := hm₆.of_equiv heq₇
  clear S₆ hm₆

  -- %33 `zext( %31 )`, %34 `icmp eq( sgn x, expected )`
  denote_step_reduce v 34 [hmapnil, hv31, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.zext, LLVM.zext?] fold

  simp [hv34, BlockCom.denote_term, Terminator.denote_condBr_value,
    simp_denote, simp_sllvm]

  -- `%23`/`%24` loaded `buf`'s last byte, so `%32` compared `sgn x` against
  -- bit 255 of the buffer the spec reads. Both edges of `%34` need this.
  have hbit : (readBuf hbuf)[255]
      = (BitVec.extractLsb' bufTop.offsetInBits 8 blk.bytes).getLsbD 7 := by
    have hoff : bufTop.offsetInBits + 7 = buf.offsetInBits + 255 := by
      have hb : buf.offset.toNat + 32 ≤ 2 ^ 64 := hbuf.right
      show 8 * (buf.offset + 31#64).toNat + 7 = 8 * buf.offset.toNat + 255
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hblk' : s₁.mem[buf.id]? = some (Block.live blk) := hblkTop
    rw [show readBuf hbuf = blk.bytes.extractLsb' buf.offsetInBits 256 from by
      rw [← hbufval₁]; simp only [readBuf, readBuf?, MemoryState.live?, hblk']; rfl]
    show (BitVec.extractLsb' buf.offsetInBits 256 blk.bytes).getLsbD 255 = _
    simp only [BitVec.getLsbD_extractLsb', hoff]
    simp
  -- the shift picks that bit out, and nothing else
  have hshift : ∀ b : BitVec 8,
      BitVec.setWidth 32 b >>> (7 : Nat) = if b.getLsbD 7 then 1#32 else 0#32 := by decide

  by_cases hsign : BitVec.ofNat 32 (root.val % 2) = BitVec.setWidth 32 (BitVec.extractLsb' bufTop.offsetInBits 8 blk.bytes) >>> (7 : Nat)
  case neg =>
    simp [hsign, hmapnil]
    denote_enter_block

    -- %35 `fd_f25519_neg( x, x )` -- the sign the encoding asked for.
    -- `neg` takes the *bias* bounds, which is why `x` never needed to be
    -- tight; and it leaves them, which is all `^bb3`'s `mul` wants.
    obtain ⟨s₈, f₈, hrun₈, hnegval, hnegbnd⟩ :=
      neg_step S₇.wf S₇.ptrx S₇.ptrx S₇.valx S₇.bndx
    peel_call hrun₈
    clear hrun₈
    have S₈ : State s r pd pone (-root) y 0 u v s₈ :=
      S₇.stepX hnr f₈ hnegval hnegbnd
    have hm₈ := hm₇.wrote (by simp [hpxptr, hpyptr, hptptr, hpuptr, hpvptr]) f₈
    clear S₇ hm₇

    simp [hmapnil]

    refine bb3_run hs hr hbuf hnr hreturnValue _ s₈ (-root) (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) hglobne₂ S₈ hm₈ (by rw [show (-root) ^ 2 = root ^ 2 from by ring]; exact hsq₆) ?_

    -- `heven₆` makes `sgn x` zero, so `hsign` says the requested bit is `1`
    have hexp : (readBuf hbuf)[255] = true := by
      by_contra hc
      simp only [Bool.not_eq_true] at hc
      exact hsign (by rw [heven₆, hshift, ← hbit, hc]; simp)

    by_cases hroot : root = 0
    · left
      rw [hroot, neg_zero]
    · right
      rw [hexp]
      simp only [Bool.true_eq_false, iff_false]
      rw [ZMod.neg_val, if_neg hroot]
      have hlt : root.val < p := ZMod.val_lt root
      have hne : root.val ≠ 0 := fun h => hroot ((ZMod.val_eq_zero root).mp h)
      have hp : p % 2 = 1 := by decide +kernel
      omega



  simp [hsign, hmapnil]

  refine bb3_run hs hr hbuf hnr hreturnValue _ s₇ root (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) hglobne₂ S₇ hm₇ hsq₆ ?_
  right
  simp [heven₆]
  have h := hsign
  rw [heven₆, hshift] at h
  rw [hbit]
  by_contra hc
  simp only [Bool.not_eq_false] at hc
  rw [hc] at h
  simp at h

end Firedancer.Ref
