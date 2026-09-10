/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.F25519
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Point
import SSA.Projects.Firedancer.Avx512.Spec.Vec
import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic
import SSA.Projects.Firedancer.Proof.Globals

/-!
# The relational invariant

Conformance proofs in `Conformance/Proof/` compose two whole-function
specifications, one per backend. That works while a region's content is
arithmetic, because the only bridge between 5x51-bit limbs and 6x43-bit limbs
is the field element both stand for -- and computing it *is* the specification.

It stops paying where the two backends run the *same* source. There the regions
agree op for op and the relation is preserved syntactically, with no
mathematical content to prove; what the proof spends its lines on instead is
carrying "what the other pointers still hold" across each call. `Corr` is that
bookkeeping, named once.

`FieldCorr` is the only place the two representations meet. Everything else --
`Corr`, its framing lemmas -- is about keeping a list of such pairs alive
across a callee that writes somewhere else.

Ordering note: the pointer lists are kept `Nodup` per side, but nothing relates
a ref pointer's block to its AVX-512 partner's. The two states are separate;
`p.id` and `p'.id` may coincide or not, and no proof may depend on which.
-/

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- A ref field element at `p` and an AVX-512 vector at `p'` stand for the same
element of `ZMod p`.

Not equality of representations -- ref packs five 51-bit limbs into 320 bits,
AVX-512 six 43-bit limbs into eight 64-bit lanes -- but equality of the value
they decode to, which is the only thing both sides can agree on. -/
structure FieldCorr (m m' : MemoryState) (q q' : Pointer) : Prop where
  ref : Ref.IsFieldElemPtr m q
  avx : Avx512.IsVecPtr m' q'
  value : Ref.readFieldElem ref = Avx512.vecValue (Avx512.readVec avx)

/-- The relational invariant a lockstep walk maintains: both states well
formed, and every pointer pair in `φ` holding the same field element.

`φ` is a list rather than a set because the walk adds and drops pairs in
program order, and because the two `Nodup` fields are what a callee's frame
condition is spent against. -/
structure Corr (s s' : GlobalState) (φ : List (Pointer × Pointer)) : Prop where
  wf : s.WF
  wf' : s'.WF
  nodup : (φ.map (fun q => q.1.id)).Nodup
  nodup' : (φ.map (fun q => q.2.id)).Nodup
  pairs : ∀ q ∈ φ, FieldCorr s.mem s'.mem q.1 q.2

namespace FieldCorr

/-- A ref-side store to another block leaves the pair alone. The AVX-512 half is
untouched, so this is the asymmetric half of framing -- the two sides are
framed independently, since a write on one cannot reach the other's state. -/
theorem splice_ref_ne {m m' : MemoryState} {q q' r : Pointer} {w : Nat} {x : BitVec w}
    (h : FieldCorr m m' q q') (hne : r.id ≠ q.id) :
    FieldCorr (m.splice r x) m' q q' where
  ref := Ref.isFieldElemPtr_splice (p := r) (x := x) h.ref
  avx := h.avx
  value := by
    have hlimb : ∀ i : Fin 5,
        Ref.readLimb i (Ref.isFieldElemPtr_splice (p := r) (x := x) h.ref) = Ref.readLimb i h.ref := by
      intro i
      simp only [Ref.readLimb, Ref.readLimb?_splice_of_disjoint i (Or.inl hne)]
    rw [Ref.readFieldElem_eq_of_readLimb hlimb]
    exact h.value

/-- ... and symmetrically for an AVX-512-side store. -/
theorem splice_avx_ne {m m' : MemoryState} {q q' r : Pointer} {w : Nat} {x : BitVec w}
    (h : FieldCorr m m' q q') (hne : r.id ≠ q'.id) :
    FieldCorr m (m'.splice r x) q q' where
  ref := h.ref
  avx := Avx512.isVecPtr_splice (q := r) (x := x) h.avx
  value := by
    have hv : Avx512.readVec (Avx512.isVecPtr_splice (q := r) (x := x) h.avx)
        = Avx512.readVec h.avx := by
      simp only [Avx512.readVec, Avx512.readVec?_splice_ne hne]
    rw [hv]
    exact h.value

/-- Both memories agree on the two blocks: the pair stands. What an `alloca`
elsewhere, or a callee's frame discipline, hands back. -/
theorem of_live?_eq {m m₁ m' m₁' : MemoryState} {q q' : Pointer}
    (h : FieldCorr m m' q q')
    (hl : m₁.live? q.id = m.live? q.id) (hl' : m₁'.live? q'.id = m'.live? q'.id) :
    FieldCorr m₁ m₁' q q' where
  ref := Ref.isFieldElemPtr_of_live?_eq hl h.ref
  avx := ⟨fits_of_live?_eq hl' h.avx.1, h.avx.2⟩
  value := by
    rw [Ref.readFieldElem_eq_of (v := Ref.readFieldElem h.ref)
          ((Ref.readFieldElem?_of_live?_eq hl).trans (Option.some_get _).symm)]
    have : Avx512.readVec (⟨fits_of_live?_eq hl' h.avx.1, h.avx.2⟩ : Avx512.IsVecPtr m₁' q')
        = Avx512.readVec h.avx := by
      simp only [Avx512.readVec, Avx512.readVec?_of_live?_eq hl']
    rw [this]; exact h.value

/-- `≈` on both sides carries the pair. -/
theorem of_equiv {s s' t t' : GlobalState} {q q' : Pointer}
    (h : FieldCorr s.mem s'.mem q q') (he : s ≈ t) (he' : s' ≈ t') :
    FieldCorr t.mem t'.mem q q' :=
  h.of_live?_eq (he.live q.id).symm (he'.live q'.id).symm

end FieldCorr

/-- `run_runFunction'` for two backends at once, keeping both runs under a
*single* goal.

Stripping `runFunction` side by side is what makes a lockstep walk possible at
all: applying the one-sided `run_runFunction'` to each conjunct separately
splits the goal in two, and once split there is no place left to thread `Corr`
-- each side gets walked on its own and the invariant degenerates into a
bundle of hypotheses fixed up at the end. Here the two runs, and the relation
between the states they produce, stay in one place. -/
theorem run_runFunction₂ {α β : Type} {b : EffectM α} {b' : EffectM β}
    {r : α} {r' : β} {s s' : GlobalState}
    (P : GlobalState → GlobalState → Prop)
    (h : ∃ t t' : GlobalState,
      StateT.run b s = .value (r, t) ∧ StateT.run b' s' = .value (r', t')
        ∧ P (s.popFrame t.mem) (s'.popFrame t'.mem)) :
    ∃ t t' : GlobalState,
      StateT.run (runFunction b) s = .value (r, t)
        ∧ StateT.run (runFunction b') s' = .value (r', t') ∧ P t t' :=
  let ⟨t, t', hb, hb', hP⟩ := h
  ⟨_, _, run_runFunction hb, run_runFunction hb', hP⟩

namespace Corr

/-- Read one pair out of the invariant. -/
theorem get {s s' : GlobalState} {φ : List (Pointer × Pointer)} {q q' : Pointer}
    (h : Corr s s' φ) (hmem : (q, q') ∈ φ) : FieldCorr s.mem s'.mem q q' :=
  h.pairs _ hmem

/-- The frame rule, one call's worth: a callee that writes only to blocks
outside `φ` leaves the whole invariant standing. This is the lemma that
absorbs the `isFieldElemPtr_splice` towers the composed proofs spend their
length on. -/
theorem frame {s s' : GlobalState} {φ : List (Pointer × Pointer)}
    {r r' : Pointer} {w w' : Nat} {x : BitVec w} {x' : BitVec w'}
    (h : Corr s s' φ)
    (hr : ∀ q ∈ φ, r.id ≠ q.1.id) (hr' : ∀ q ∈ φ, r'.id ≠ q.2.id)
    (hwf : ({ s with mem := s.mem.splice r x } : GlobalState).WF)
    (hwf' : ({ s' with mem := s'.mem.splice r' x' } : GlobalState).WF) :
    Corr { s with mem := s.mem.splice r x } { s' with mem := s'.mem.splice r' x' } φ where
  wf := hwf
  wf' := hwf'
  nodup := h.nodup
  nodup' := h.nodup'
  pairs q hq := ((h.pairs q hq).splice_ref_ne (hr q hq)).splice_avx_ne (hr' q hq)

/-- `≈` on both sides carries the invariant: what a conformance lemma hands
back after a callee is an equivalent state, not a syntactically equal one. -/
theorem of_equiv {s s' t t' : GlobalState} {φ : List (Pointer × Pointer)}
    (h : Corr s s' φ) (he : s ≈ t) (he' : s' ≈ t') : Corr t t' φ where
  wf := h.wf.of_equiv he
  wf' := h.wf'.of_equiv he'
  nodup := h.nodup
  nodup' := h.nodup'
  pairs q hq := (h.pairs q hq).of_equiv he he'

end Corr

/-! ## Focusing on one conjunct of a lockstep goal

A lockstep walk keeps both backends' runs under one goal `b ∧ c`. Stepping one of
them with `denote_step_all` introduces `v_i` with `hv_i : v_i = e_i` -- names for
the instructions' denotations -- and rewrites that conjunct in terms of them.
Done inside `apply And.imp_left; intro h; …; exact h`, the names die with the
focus: `?a` was created before them and cannot mention them.

They need not. Each `hv_i` has a right-hand side closed over the outer context
and the earlier `v_j`, so the pair is a pure abbreviation, and an abbreviation
can be minted anywhere. `focus_left`/`focus_right` therefore

1. run the block on a scratch copy of the focused conjunct,
2. read the `(v_i, hv_i)` pairs it introduced off the residual context and
   re-introduce each in the *combined* goal, as `∃ x, x = e_i` destructured
   -- the opaque naming `sllvm-proof-elaboration-cost` recommends, so nothing
   later zeta-expands through them,
3. take the block's own proof term, fill its residual goal with `h`, rename the
   scratch variables to the outer ones, and package it as `side' → side`,
4. finish with `And.imp_left`/`_right`, leaving the combined goal with the
   focused conjunct stepped and every `v_i`, `hv_i` in scope.

The block must leave exactly one goal, and everything it introduces must come
as such a pair. A bare fact (`have foo : P := …`) has no defining equation to
lift; end the block with `clear foo` if one is needed only locally. -/

open Lean Elab Tactic Meta in
/-- Substitute away, in `g`, every hypothesis of `hs` that is a defining
equation `v = e` for a local `v`, later ones first. Returns the goal. -/
private def substDefs (g : MVarId) (hs : Array FVarId) : MetaM MVarId := do
  let mut g := g
  for h in hs.reverse do
    if (← g.getDecl).lctx.contains h then
      g ← Lean.Meta.subst g h
  return g

open Lean Elab Tactic Meta in
def focusConj (left : Bool) (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq) :
    TacticM Unit := do
  let who := if left then "focus_left" else "focus_right"
  let g ← getMainGoal
  g.withContext do
    let tgt ← whnfR (← instantiateMVars (← g.getType))
    let some (b, c) := tgt.and?
      | throwError "{who}: goal is not a conjunction"
    let (side, other) := if left then (b, c) else (c, b)
    let lctx₀ ← getLCtx
    -- 1. Discovery: run the block on a scratch copy of the focused conjunct and
    --    read off what it introduced. Only the residual *context* and *type* are
    --    used; the scratch proof term is discarded.
    let scratch ← mkFreshExprSyntheticOpaqueMVar side
    let gs ← Tactic.run scratch.mvarId! (evalTactic tac)
    let [g'] := gs
      | throwError "{who}: the block must leave exactly one goal, but left {gs.length}"
    let lctx' := (← g'.getDecl).lctx
    let newDecls : Array LocalDecl :=
      lctx'.foldl (fun acc d => if lctx₀.contains d.fvarId then acc else acc.push d) #[]
    -- 2. Lift every `(v, hv : v = e)` into the combined goal, as an `∃` destructured.
    let mut gCur := g
    let mut fromVars : Array Expr := #[]
    let mut toVars : Array Expr := #[]
    let mut outerHvs : Array Name := #[]
    let mut i := 0
    while i < newDecls.size do
      let d := newDecls[i]!
      let some hd := newDecls[i + 1]?
        | throwError "{who}: `{d.userName}` has no defining equation; \
            end the block with `subst_vars` or `clear {d.userName}`"
      let some (_, lhs, e) := (← instantiateMVars hd.type).eq?
        | throwError "{who}: `{hd.userName}` is not an equation `{d.userName} = …`"
      unless lhs == .fvar d.fvarId do
        throwError "{who}: `{hd.userName}` does not define `{d.userName}`"
      let ty' := (← instantiateMVars d.type).replaceFVars fromVars toVars
      let e' := (← instantiateMVars e).replaceFVars fromVars toVars
      let pred ← withLocalDeclD `x ty' fun x => do mkLambdaFVars #[x] (← mkEq x e')
      let exTy ← mkAppM ``Exists #[pred]
      let exPf ← mkAppOptM ``Exists.intro #[ty', pred, e', ← mkEqRefl e']
      let g₁ ← gCur.assert `hEx exTy exPf
      let (hEx, g₂) ← g₁.intro1P
      let sgs ← g₂.cases hEx #[{ varNames := [d.userName, hd.userName] }]
      let #[sg] := sgs
        | throwError "{who}: internal: `cases` on `∃` produced {sgs.size} goals"
      gCur := sg.mvarId
      fromVars := (fromVars.push (.fvar d.fvarId)).push (.fvar hd.fvarId)
      toVars := (toVars.push sg.fields[0]!).push sg.fields[1]!
      outerHvs := outerHvs.push hd.userName
      i := i + 2
    -- 3. The stepped conjunct, spelled with the outer names.
    let side' := (← instantiateMVars (← g'.getType)).replaceFVars fromVars toVars
    -- 4. `f : side' → side`. The block's own proof binds its `v`s internally
    --    (`generalize`), so its term cannot take `h` directly; re-run the block
    --    under the lambda instead, then bring both spellings -- `h`'s outer
    --    names and the residual's inner ones -- down to the definitions with
    --    `subst`, where they coincide.
    let f ← gCur.withContext do
      withLocalDeclD `h side' fun h => do
        let inner ← mkFreshExprSyntheticOpaqueMVar side
        let gs ← Tactic.run inner.mvarId! (evalTactic tac)
        let [gI] := gs
          | throwError "{who}: the block left {gs.length} goals on its second run"
        let lctxBase ← getLCtx
        let innerHvs : Array FVarId := (← gI.getDecl).lctx.foldl (init := #[]) fun acc d =>
          if lctxBase.contains d.fvarId then acc
          else match d.type.eq? with
            | some (_, lhs, _) => if lhs.isFVar then acc.push d.fvarId else acc
            | none => acc
        let gS ← substDefs gI innerHvs
        let lctxS := (← gS.getDecl).lctx
        let outerIds ← outerHvs.mapM fun n => do
          match lctxS.findFromUserName? n with
          | some d => pure d.fvarId
          | none => throwError "{who}: internal: lost `{n}`"
        let gS ← substDefs gS outerIds
        gS.withContext do
          let some hd := (← getLCtx).findFromUserName? `h
            | throwError "{who}: internal: lost `h`"
          let want ← gS.getType
          unless ← isDefEq hd.type want do
            throwError "{who}: after substitution the block's result\n  {want}\n\
              does not match the lifted statement\n  {hd.type}"
          gS.assign (.fvar hd.fvarId)
        mkLambdaFVars #[h] (← instantiateMVars inner)
    -- 5. The combined goal, focused conjunct stepped.
    gCur.withContext do
      let restTy := if left then mkAnd side' other else mkAnd other side'
      let restG ← mkFreshExprSyntheticOpaqueMVar restTy (← g.getTag)
      let lem := if left then ``And.imp_left else ``And.imp_right
      gCur.assign (← mkAppM lem #[f, restG])
      replaceMainGoal [restG.mvarId!]

/-- Run a block on the left conjunct of `b ∧ c` and return to the combined goal
with `b` stepped and the block's `v_i`/`hv_i` in scope. See `focusConj`. -/
elab "focus_left " tac:tacticSeq : tactic => focusConj true tac

/-- ... and on the right conjunct. -/
elab "focus_right " tac:tacticSeq : tactic => focusConj false tac

end Firedancer
