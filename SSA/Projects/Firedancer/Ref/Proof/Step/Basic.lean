/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Bias
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

/-!
# What a peeled call leaves behind

A ref region is a chain of calls, each writing one 40-byte out-parameter.
`Wrote` is what such a call leaves of the state; `StepFacts` is that plus the
value and the tight bound at `dst`. The `Step/fd_*` files package one
conformance lemma each into these shapes, so that a walk only ever handles
`StepFacts` and the frame lemmas below.
-/

namespace Firedancer.Ref

open LeanMLIR SLLVM

/-- The part of a peeled call the frame invariant needs: the state is still
well-formed, `dst`'s block is the only one that moved, and `dst` is still a
field element. `StepFacts` is this plus the value and the tight bound, which
`fd_f25519_neg` does not give. -/
structure Wrote (dst : Pointer) (u u' : GlobalState) : Prop where
  wf : u'.WF
  /-- The symbol table is untouched -- `runFunction` restores it, and no
  operation writes it. What a global's address *is* therefore survives a call,
  which is what a callee doing its own `llvm.mlir.addressof` needs. -/
  globals : u'.globals = u.globals
  live : ∀ b : BlockId, dst.id ≠ b → u'.mem.live? b = u.mem.live? b
  ptr : IsFieldElemPtr u'.mem dst
  splice : ∃ x : BitVec (5 * 64), u'.mem.live? dst.id = (u.mem.splice dst x).live? dst.id

/-- `Wrote` plus what `dst` now holds: the value `v`, tight. -/
structure StepFacts (dst : Pointer) (v : ZMod _root_.p) (u u' : GlobalState) : Prop where
  wf : u'.WF
  /-- See `Wrote.globals`. -/
  globals : u'.globals = u.globals
  live : ∀ b : BlockId, dst.id ≠ b → u'.mem.live? b = u.mem.live? b
  splice : ∃ x : BitVec (5 * 64), u'.mem.live? dst.id = (u.mem.splice dst x).live? dst.id
  ptr : IsFieldElemPtr u'.mem dst
  val : readFieldElem ptr = v
  bnd : LimbBounds ptr

/-- Every peeled `sqr`/`mul`/`pow22523` is one. -/
theorem StepFacts.wrote {dst : Pointer} {v : ZMod _root_.p} {u u' : GlobalState}
    (st : StepFacts dst v u u') : Wrote dst u u' :=
  ⟨st.wf, st.globals, st.live, st.ptr, st.splice⟩

/-- `readFieldElem` back into the proof-free `readFieldElem?` form. -/
theorem readFieldElem?_eq_some {m : MemoryState} {q : Pointer} (h : IsFieldElemPtr m q)
    {v : ZMod _root_.p} (hv : readFieldElem h = v) : readFieldElem? q m = some v := by
  rw [← hv]; exact (Option.some_get _).symm

/-! ## Building a step from a conformance lemma

Every kernel returns its entry state with one splice at `dst`, up to `≈`; the
two lemmas below turn that into `StepFacts`/`Wrote`, so a `Step/fd_*` file has
only the value and the bound left to line up. -/

section OfSplice

variable {dst : Pointer} {u u' : GlobalState} {x : BitVec (5 * 64)}

/-- The state half, common to every kernel. -/
theorem Wrote.of_splice (hu : u.WF) (hd : IsFieldElemPtr u.mem dst)
    (heq : ({ u with mem := u.mem.splice dst x } : GlobalState) ≈ u') : Wrote dst u u'
    where
  wf := GlobalState.WF.of_equiv hu.splice heq
  globals := heq.globals.symm
  live := fun b hb => (heq.live b).symm.trans (live?_splice_ne hb)
  ptr := ⟨fits_equiv heq (by simpa using fits_splice hd.1), hd.2⟩
  splice := ⟨x, (heq.live dst.id).symm⟩

/-- What `dst` reads back as at the state the callee returned: whatever the
splice holds -- the form the kernels' conformance lemmas state their output
in. -/
theorem readFieldElem_of_splice {v : ZMod _root_.p}
    (heq : ({ u with mem := u.mem.splice dst x } : GlobalState) ≈ u')
    (hval : readFieldElem? dst (u.mem.splice dst x) = some v) {h' : IsFieldElemPtr u'.mem dst} :
    readFieldElem h' = v :=
  readFieldElem_eq_of ((readFieldElem?_of_equiv heq dst).symm.trans hval)

/-- ... and the same with the value left as the read at the splice, for a
callee whose output is stated about that read. -/
theorem readFieldElem_eq_splice (hd : IsFieldElemPtr u.mem dst)
    (heq : ({ u with mem := u.mem.splice dst x } : GlobalState) ≈ u')
    {h' : IsFieldElemPtr u'.mem dst} :
    readFieldElem h' = readFieldElem (m := u.mem.splice dst x) (isFieldElemPtr_splice hd) :=
  readFieldElem_of_splice heq (Option.some_get _).symm

/-- ... and the bounds at it, from the callee's `readLimb?`-shaped output. -/
theorem limbBounds_of_splice {n : ℕ}
    (heq : ({ u with mem := u.mem.splice dst x } : GlobalState) ≈ u')
    (hbnd : ∀ (i : Fin 5) (l : ℕ), readLimb? dst i (u.mem.splice dst x) = some l → l ≤ n)
    {h' : IsFieldElemPtr u'.mem dst} : LimbBounds h' n :=
  limbBounds_of_readLimb? _ fun i l hl => hbnd i l ((readLimb?_of_equiv heq dst i).trans hl)

/-- ... per limb, for a `fiat_25519_opp` result. -/
theorem biasBounds_of_splice (heq : ({ u with mem := u.mem.splice dst x } : GlobalState) ≈ u')
    (hbnd : ∀ (i : Fin 5) (l : ℕ), readLimb? dst i (u.mem.splice dst x) = some l → l ≤ biasLimb i)
    {h' : IsFieldElemPtr u'.mem dst} : BiasBounds h' :=
  biasBounds_of_readLimb? _ fun i l hl => hbnd i l ((readLimb?_of_equiv heq dst i).trans hl)

/-- ... and the sum bound `fd_f25519_sgn` needs downstream. -/
theorem limbSum_of_splice (hd : IsFieldElemPtr u.mem dst)
    (heq : ({ u with mem := u.mem.splice dst x } : GlobalState) ≈ u')
    {h' : IsFieldElemPtr u'.mem dst} :
    limbSum h' = limbSum (m := u.mem.splice dst x) (isFieldElemPtr_splice hd) :=
  limbSum_of_live?_eq (heq.live dst.id).symm

/-- ... and the whole of `StepFacts`, given how the splice reads back. -/
theorem StepFacts.of_splice {v : ZMod _root_.p} (hu : u.WF) (hd : IsFieldElemPtr u.mem dst)
    (heq : ({ u with mem := u.mem.splice dst x } : GlobalState) ≈ u')
    (hval : readFieldElem? dst (u.mem.splice dst x) = some v)
    (hbnd :
      ∀ (i : Fin 5) (l : ℕ), readLimb? dst i (u.mem.splice dst x) = some l → l ≤ 0x8000000000000) :
    StepFacts dst v u u' :=
  let w := Wrote.of_splice hu hd heq
  { wf := w.wf, globals := w.globals, live := w.live, splice := w.splice, ptr := w.ptr
    val := readFieldElem_eq_of ((readFieldElem?_of_equiv heq dst).symm.trans hval)
    bnd := limbBounds_of_readLimb? _ fun i l hl => hbnd i l (by rwa [readLimb?_of_equiv heq]) }

end OfSplice

/-! ## Carrying a field element past a step

A step writes one block; everything read out of another block is unchanged,
because `readLimb?` looks only at `m.live? q.id`. -/

/-- `m'` holds `q`'s block exactly as `m` did -- the whole of what a field
element at `q` is read out of, so every fact about it carries across. -/
abbrev Untouched (q : Pointer) (m m' : MemoryState) : Prop :=
  m'.live? q.id = m.live? q.id

section Carry

variable {m m' : MemoryState} {q : Pointer} {bound : ℕ} {v : ZMod _root_.p} (h : Untouched q m m')

include h

/-- A block the step left alone keeps its value ... -/
theorem carryVal {hq : IsFieldElemPtr m q} (hv : readFieldElem hq = v) {hq' : IsFieldElemPtr m' q} :
    readFieldElem hq' = v :=
  readFieldElem_eq_of ((readFieldElem?_of_live?_eq h).trans (readFieldElem?_eq_some hq hv))

/-- ... its limb bound ... -/
theorem carryBnd {hq : IsFieldElemPtr m q} (hb : LimbBounds hq bound) {hq' : IsFieldElemPtr m' q} :
    LimbBounds hq' bound :=
  limbBounds_of_readLimb? _ (limbBounds_of_live?_eq h (limbBounds_readLimb? hq hb))

/-- ... and the per-limb bias bound a `fd_f25519_neg` result comes at. -/
theorem carryBias {hq : IsFieldElemPtr m q} (hb : BiasBounds hq) {hq' : IsFieldElemPtr m' q} :
    BiasBounds hq' :=
  biasBounds_of_readLimb? _ fun i l hl =>
    biasBounds_readLimb? hq hb i l ((readLimb?_of_live?_eq h i).symm.trans hl)

/-- The three together, with the new pointer produced rather than assumed --
what an `obtain` at a step wants. -/
theorem carry (hq : IsFieldElemPtr m q) (hb : LimbBounds hq bound) :
    ∃ hq' : IsFieldElemPtr m' q, readFieldElem hq' = readFieldElem hq ∧ LimbBounds hq' bound :=
  ⟨isFieldElemPtr_of_live?_eq h hq, carryVal h rfl, carryBnd h hb⟩

/-- ... with the value pinned to whatever it was already known to be. -/
theorem survive (hq : IsFieldElemPtr m q) (hv : readFieldElem hq = v) (hb : LimbBounds hq bound) :
    ∃ hq' : IsFieldElemPtr m' q, readFieldElem hq' = v ∧ LimbBounds hq' bound :=
  ⟨isFieldElemPtr_of_live?_eq h hq, carryVal h hv, carryBnd h hb⟩

/-- ... and the bias-bounded counterpart. -/
theorem surviveBias (hq : IsFieldElemPtr m q) (hv : readFieldElem hq = v) (hb : BiasBounds hq) :
    ∃ hq' : IsFieldElemPtr m' q, readFieldElem hq' = v ∧ BiasBounds hq' :=
  ⟨isFieldElemPtr_of_live?_eq h hq, carryVal h hv, carryBias h hb⟩

end Carry

end Firedancer.Ref
