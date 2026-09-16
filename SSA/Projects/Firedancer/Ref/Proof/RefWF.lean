/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Proof.Step.Basic
import SSA.Projects.Firedancer.Ref.Proof.Globals
import SSA.Projects.Firedancer.Curve
import SSA.Projects.Firedancer.Ed25519
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_affine_is_small_order

/-!
# A state the `ref` module can run in

`GlobalState.WF` says the state is well-formed; `RefWF` says it also carries
the seven field-element constants and the base-point table `ref.mlir` declares, so
that a region -- or a
callee doing its own `llvm.mlir.addressof` -- finds them where it expects. The
carry lemmas take it past a step, which is where the `apart` list is spent.
-/

namespace Firedancer.Ref

open LeanMLIR SLLVM

/-- A `constant` field element the module loads: `ref.mlir` records `q` as
`name`'s address, and `val` is what lives there, tight.

The address half is carried separately from the value because the two are
spent in different places: a region that reaches the global itself needs only
the value at `q`, while a *callee* that does its own `llvm.mlir.addressof`
needs `addr` at the state it is called in. Nothing here says two globals are
apart -- LLVM does not (`unnamed_addr` licenses constant merging, an `@alias`
points into its aliasee), so a spec that needs it says so. -/
structure FieldGlobal (s : GlobalState) (name : String) (q : Pointer) (val : ZMod _root_.p) :
    Prop where
  addr : GlobalPtr s name q
  ptr : IsFieldElemPtr s.mem q
  value : readFieldElem ptr = val
  bnd : LimbBounds ptr

namespace FieldGlobal

variable {s s' : GlobalState} {name : String} {q : Pointer} {val : ZMod _root_.p}

/-- A loaded global predates every frame the module then runs in. -/
theorem below (hg : FieldGlobal s name q val) (hs : s.WF) : q.id.id < s.alloc.nextFreeBlock :=
  lt_nextFreeBlock_of_fits hs hg.ptr.left

/-- A call that moved nothing leaves the global where it was -- table, value
and bound. -/
theorem of_equiv (hg : FieldGlobal s name q val) (he : s ≈ s') : FieldGlobal s' name q val where
  addr := hg.addr.of_equiv he
  ptr := isFieldElemPtr_of_live?_eq (he.live _).symm hg.ptr
  value := carryVal (he.live _).symm hg.value
  bnd := carryBnd (he.live _).symm hg.bnd

end FieldGlobal

/-- A global whose contents are not stated: `ref.mlir` records `q` as `name`'s
address, and `n` bytes fit there. -/
structure SizedGlobal (s : GlobalState) (name : String) (q : Pointer) (n : Nat) : Prop where
  addr : GlobalPtr s name q
  fits : Fits s.mem q (n * 8)
  off : q.offset.toNat + n ≤ 2 ^ 64

namespace SizedGlobal

variable {s s' : GlobalState} {name : String} {q : Pointer} {n : Nat}

theorem below (hg : SizedGlobal s name q n) (hs : s.WF) : q.id.id < s.alloc.nextFreeBlock :=
  lt_nextFreeBlock_of_fits hs hg.fits

/-- The address at `s'` and `q`'s block unchanged carry the global. -/
theorem carry (hg : SizedGlobal s name q n) (haddr : GlobalPtr s' name q)
    (h : s'.mem.live? q.id = s.mem.live? q.id) : SizedGlobal s' name q n :=
  ⟨haddr, fits_of_live?_eq h hg.fits, hg.off⟩

theorem of_equiv (hg : SizedGlobal s name q n) (he : s ≈ s') : SizedGlobal s' name q n :=
  hg.carry (hg.addr.of_equiv he) (he.live _).symm

end SizedGlobal

/-- `q` is none of the blocks in `apart`. The region's writes are what these
keep it off: a spec lists the pointers it writes through, and a global apart
from all of them survives the walk. -/
abbrev Apart (q : Pointer) (apart : List Pointer) : Prop :=
  ∀ p ∈ apart, q.id ≠ p.id

/-- `s` loads `name` at *some* address, holding `val`, apart from everything in
`apart`. The address is existential -- a caller that needs to name it does so
by `obtain`, and one that only needs the value never mentions it. -/
abbrev Loaded (s : GlobalState) (name : String) (val : ZMod _root_.p) (apart : List Pointer) :
    Prop :=
  ∃ q : Pointer, FieldGlobal s name q val ∧ Apart q apart

/-- `s` is a state the `ref` module can run in: well-formed in
`GlobalState.WF`'s sense, and carrying the seven `ref.mlir` field-element
constants and the table the call graph below it reads, each apart from every pointer the region
writes through
-- for `fd_ed25519_point_frombytes` just `r`, so that theorem passes `[r]`.

`@fd_f25519_d` and `@fd_f25519_one` the region addresses itself, at `%3` and
`%4`, so only their *values* are wanted after entry. `@fd_f25519_sqrtm1` the
region never mentions: `fd_f25519_sqrt_ratio` reaches it at its own `%1`, so
its `addr` half has to survive the walk as far as `%18` -- which is what makes
the symbol table, not just memory, part of what a step must carry.

The last two are the low-order table:
`fd_ed25519_affine_is_small_order` addresses both at `%1` and `%2` and hands
them to `fd_f25519_eq`. They live here rather than in that region's
specification for the same reason as the other three -- their addresses are the
loader's to choose, so a spec that named them would be quantifying over
something the module already fixed.

`fd_curve25519_into_precomputed` addresses `@fd_f25519_k`, `2·d`, at `%1` and
passes it to `fd_f25519_mul`.

`fd_ed25519_point_set_zero` addresses `@fd_f25519_zero` and `@fd_f25519_one` at
`%0` and `%1`.

`fd_ed25519_double_scalar_mul_base` addresses `@fd_ed25519_base_point_wnaf_table`,
128 points, at `%13`; its contents are not stated yet.

`wf` is what puts the eight blocks below the frame, via `FieldGlobal.below` and
`SizedGlobal.below`. -/
structure _root_.LeanMLIR.GlobalState.RefWF (s : GlobalState) (apart : List Pointer) : Prop where
  wf : s.WF
  gd : Loaded s "fd_f25519_d" Ed25519.d apart
  gone : Loaded s "fd_f25519_one" 1 apart
  gm1 : Loaded s "fd_f25519_sqrtm1" _root_.sqrtm1 apart
  gy0 : Loaded s "fd_ed25519_order8_point_y0" Ed25519.order8_y0 apart
  gy1 : Loaded s "fd_ed25519_order8_point_y1" Ed25519.order8_y1 apart
  gk : Loaded s "fd_f25519_k" (2 * Ed25519.d) apart
  gzero : Loaded s "fd_f25519_zero" 0 apart
  gtbl : ∃ q, SizedGlobal s "fd_ed25519_base_point_wnaf_table" q (128 * (4 * 5 * 8)) ∧ Apart q apart

section RefWFCarry

variable {s w w' : GlobalState} {apart : List Pointer}

/-- One constant across one write that misses it: `Wrote.globals` carries the
address, `Wrote.live` carries the value and the bound. -/
theorem carryGlobal {name : String} {val : ZMod _root_.p} {q dst : Pointer} (st : Wrote dst w w')
    (hne : q.id ≠ dst.id) (hg : FieldGlobal w name q val) : FieldGlobal w' name q val :=
  let h := st.live q.id (Ne.symm hne)
  { addr := by
      simp only [GlobalPtr, st.globals]; exact hg.addr
    ptr := isFieldElemPtr_of_live?_eq h hg.ptr
    value := carryVal h hg.value
    bnd := carryBnd h hg.bnd }

/-- A write through a pointer the state is declared apart from leaves the
module's constants alone -- so a `Wrote` step preserves `RefWF`.

`Apart` is what pays for it: the write misses each global's block. That is why
`apart` is a *list*: a region's write set is its out-parameters plus its own
locals, and a walk that lists all of them gets every step's carry from this
one lemma. -/
theorem _root_.LeanMLIR.GlobalState.RefWF.wrote {dst : Pointer} (hw : w.RefWF apart)
    (hdst : dst ∈ apart) (st : Wrote dst w w') : w'.RefWF apart
    where
  wf := st.wf
  gd :=
    let ⟨q, hg, hq⟩ := hw.gd;
    ⟨q, carryGlobal st (hq dst hdst) hg, hq⟩
  gone :=
    let ⟨q, hg, hq⟩ := hw.gone;
    ⟨q, carryGlobal st (hq dst hdst) hg, hq⟩
  gm1 :=
    let ⟨q, hg, hq⟩ := hw.gm1;
    ⟨q, carryGlobal st (hq dst hdst) hg, hq⟩
  gy0 :=
    let ⟨q, hg, hq⟩ := hw.gy0;
    ⟨q, carryGlobal st (hq dst hdst) hg, hq⟩
  gy1 :=
    let ⟨q, hg, hq⟩ := hw.gy1;
    ⟨q, carryGlobal st (hq dst hdst) hg, hq⟩
  gk :=
    let ⟨q, hg, hq⟩ := hw.gk;
    ⟨q, carryGlobal st (hq dst hdst) hg, hq⟩
  gzero :=
    let ⟨q, hg, hq⟩ := hw.gzero;
    ⟨q, carryGlobal st (hq dst hdst) hg, hq⟩
  gtbl :=
    let ⟨q, hg, hq⟩ := hw.gtbl
    ⟨q,
      hg.carry
        (by
          simp only [GlobalPtr, st.globals]; exact hg.addr)
        (st.live q.id (Ne.symm (hq dst hdst))),
      hq⟩

/-- A shorter `apart` list is a weaker claim: the constants stay apart from
whatever the caller still lists. -/
theorem _root_.LeanMLIR.GlobalState.RefWF.mono {apart' : List Pointer} (hw : w.RefWF apart)
    (h : apart' ⊆ apart) : w.RefWF apart'
    where
  wf := hw.wf
  gd :=
    let ⟨q, hg, hq⟩ := hw.gd;
    ⟨q, hg, fun p hp => hq p (h hp)⟩
  gone :=
    let ⟨q, hg, hq⟩ := hw.gone;
    ⟨q, hg, fun p hp => hq p (h hp)⟩
  gm1 :=
    let ⟨q, hg, hq⟩ := hw.gm1;
    ⟨q, hg, fun p hp => hq p (h hp)⟩
  gy0 :=
    let ⟨q, hg, hq⟩ := hw.gy0;
    ⟨q, hg, fun p hp => hq p (h hp)⟩
  gy1 :=
    let ⟨q, hg, hq⟩ := hw.gy1;
    ⟨q, hg, fun p hp => hq p (h hp)⟩
  gk :=
    let ⟨q, hg, hq⟩ := hw.gk;
    ⟨q, hg, fun p hp => hq p (h hp)⟩
  gzero :=
    let ⟨q, hg, hq⟩ := hw.gzero;
    ⟨q, hg, fun p hp => hq p (h hp)⟩
  gtbl :=
    let ⟨q, hg, hq⟩ := hw.gtbl;
    ⟨q, hg, fun p hp => hq p (h hp)⟩

/-- `apart` matters only up to block ids. -/
theorem _root_.LeanMLIR.GlobalState.RefWF.of_ids {apart' : List Pointer} (hw : w.RefWF apart)
    (h : ∀ p ∈ apart', ∃ q ∈ apart, p.id = q.id) : w.RefWF apart' :=
  let ap {q : Pointer} (hq : Apart q apart) : Apart q apart' := fun p hp =>
    (h p hp).elim fun q' ⟨hq', he⟩ => by
      rw [he]; exact hq q' hq'
  { wf := hw.wf
    gd :=
      let ⟨q, hg, hq⟩ := hw.gd;
      ⟨q, hg, ap hq⟩
    gone :=
      let ⟨q, hg, hq⟩ := hw.gone;
      ⟨q, hg, ap hq⟩
    gm1 :=
      let ⟨q, hg, hq⟩ := hw.gm1;
      ⟨q, hg, ap hq⟩
    gy0 :=
      let ⟨q, hg, hq⟩ := hw.gy0;
      ⟨q, hg, ap hq⟩
    gy1 :=
      let ⟨q, hg, hq⟩ := hw.gy1;
      ⟨q, hg, ap hq⟩
    gk :=
      let ⟨q, hg, hq⟩ := hw.gk;
      ⟨q, hg, ap hq⟩
    gzero :=
      let ⟨q, hg, hq⟩ := hw.gzero;
      ⟨q, hg, ap hq⟩
    gtbl :=
      let ⟨q, hg, hq⟩ := hw.gtbl;
      ⟨q, hg, ap hq⟩ }

/-- `RefWF` across a whole call, given only what it left of memory: a step
that touched no block the state is `Apart` from keeps the constants. `wrote`
is the single-splice case; a region that writes its out-parameter several
times -- `fd_ed25519_point_frombytes` -- needs this one. -/
theorem _root_.LeanMLIR.GlobalState.RefWF.untouched (hw : w.RefWF apart) (hwf : w'.WF)
    (hg : w'.globals = w.globals)
    (hlive : ∀ b : BlockId, (∀ p ∈ apart, b ≠ p.id) → w'.mem.live? b = w.mem.live? b) :
    w'.RefWF apart :=
  let carry {name : String} {val : ZMod _root_.p} {q : Pointer} (hq : Apart q apart)
    (hgq : FieldGlobal w name q val) : FieldGlobal w' name q val :=
    let h := hlive q.id (fun p hp => hq p hp)
    { addr := by
        simp only [GlobalPtr, hg]; exact hgq.addr
      ptr := isFieldElemPtr_of_live?_eq h hgq.ptr
      value := carryVal h hgq.value
      bnd := carryBnd h hgq.bnd }
  { wf := hwf
    gd :=
      let ⟨q, hg', hq⟩ := hw.gd;
      ⟨q, carry hq hg', hq⟩
    gone :=
      let ⟨q, hg', hq⟩ := hw.gone;
      ⟨q, carry hq hg', hq⟩
    gm1 :=
      let ⟨q, hg', hq⟩ := hw.gm1;
      ⟨q, carry hq hg', hq⟩
    gy0 :=
      let ⟨q, hg', hq⟩ := hw.gy0;
      ⟨q, carry hq hg', hq⟩
    gy1 :=
      let ⟨q, hg', hq⟩ := hw.gy1;
      ⟨q, carry hq hg', hq⟩
    gk :=
      let ⟨q, hg', hq⟩ := hw.gk;
      ⟨q, carry hq hg', hq⟩
    gzero :=
      let ⟨q, hg', hq⟩ := hw.gzero;
      ⟨q, carry hq hg', hq⟩
    gtbl :=
      let ⟨q, hg', hq⟩ := hw.gtbl
      ⟨q,
        hg'.carry
          (by
            simp only [GlobalPtr, hg]; exact hg'.addr)
          (hlive q.id hq),
        hq⟩ }

/-- A call that moved nothing -- `fd_f25519_sgn` -- leaves them alone too, and
needs no `Apart`. -/
theorem _root_.LeanMLIR.GlobalState.RefWF.of_equiv (hw : w.RefWF apart) (he : w ≈ w') :
    w'.RefWF apart
    where
  wf := GlobalState.WF.of_equiv hw.wf he
  gd :=
    let ⟨q, hg, hq⟩ := hw.gd;
    ⟨q, hg.of_equiv he, hq⟩
  gone :=
    let ⟨q, hg, hq⟩ := hw.gone;
    ⟨q, hg.of_equiv he, hq⟩
  gm1 :=
    let ⟨q, hg, hq⟩ := hw.gm1;
    ⟨q, hg.of_equiv he, hq⟩
  gy0 :=
    let ⟨q, hg, hq⟩ := hw.gy0;
    ⟨q, hg.of_equiv he, hq⟩
  gy1 :=
    let ⟨q, hg, hq⟩ := hw.gy1;
    ⟨q, hg.of_equiv he, hq⟩
  gk :=
    let ⟨q, hg, hq⟩ := hw.gk;
    ⟨q, hg.of_equiv he, hq⟩
  gzero :=
    let ⟨q, hg, hq⟩ := hw.gzero;
    ⟨q, hg.of_equiv he, hq⟩
  gtbl :=
    let ⟨q, hg, hq⟩ := hw.gtbl;
    ⟨q, hg.of_equiv he, hq⟩

end RefWFCarry

end Firedancer.Ref
