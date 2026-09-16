import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Avx512.Spec.Quad

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Firedancer.Avx512 (vecBV flatten_vecBV)

/-- The clause that names the state a write lands in: `as s' := hs'`, where
`hs' : s' = { s with mem := s.mem.splice … }`.

A *named* syntax, not an inline group. An optional group whose first element is
a string atom -- `named:(" as " term " := " term)?` -- never matches: the atom
is not reached, and the clause is silently dropped. Naming the syntax is how
Lean's own `(location)?` works, and `denote_step_reduce`'s `(reduceArgs)?`. -/
syntax stateNaming := " as " term " := " term

open Lean Elab Tactic Meta in
/-- `peel_store x, p, hp, s` runs the next `llvm.store`, storing `x` (a
`Vector (BitVec 64) 8` or a `BitVec w`) at `p`, where `hp` states
`Fits s.mem p (512 or w)`.

`… as s' := hs'` names the state it lands in, with
`hs' : s' = { s with mem := s.mem.splice p … }`. Worth it once stores chain:
without it the next one spells the whole spliced state inline -- as its own
`s`, and again inside its `Fits` -- and every later `isDefEq` walks that term
rather than an `fvar`. That is the cost `frameState` had before
`exists_slots_frame` handed its state out opaquely. A single store does not
care, so the clause is optional and the tactic writes the state out.

The trailing `with` list is extra simp lemmas for the operand side goal --
whatever says what the stored value or the destination is, when the default
set does not reduce them on its own.

They join the *same* `simp only` as the default set, so they cannot reach a
term that pass itself first exposes. That is the limit worth knowing in a
**tail block**, whose operands sit behind
`Ctxt.Valuation.ofHVector args.reverse ++ Vamb`: unfolding `Expr.denoteOp`
exposes the lookups, but `simp` does not revisit them, the spine stands, and
the `run_store` rewrite below then matches nothing. Adding `simp_spine` to the
list does not help -- it is in the same pass. A tail block wants two passes,
the default set and then the ambient facts; `GeDecode2.peel_store_amb`
(`Avx512/Proof/Point/fd_r43x6_ge_decode2_blocks.lean`) is that form for a
whole-vector store. -/
elab "peel_store " x:term ", " p:term ", " hp:term ", " st:term
    named:(stateNaming)? extra:(" with " term,+)? : tactic =>
  withMainContext do
    -- The elaboration is only to classify `x` (and read its width); the
    -- emitted script elaborates it again for real. `withMainContext` is load
    -- bearing: without the goal's local context `x` is not in scope and every
    -- store looks scalar.
    let xTy ← withoutModifyingState do
      whnf (← instantiateMVars (← inferType (← Term.elabTerm x none)))
    -- Everything but these four pieces is common to the two shapes.
    let (bits, ty, val, hflat, width) ← if xTy.isAppOf ``Vector then
        pure (← `(vecBV $x), ← `(.vector 8 (.bitvec (.concrete 64))),
          ← `(($x).map PoisonOr.value), ← `(flatten_vecBV $x), ← `(512))
      else do
        -- a scalar store of `x : BitVec w`, at whatever `w` is
        let some w := (← whnf (xTy.getArg! 0)).rawNatLit?
          | throwError "peel_store: cannot reduce the stored value's width to a \
              literal in {← Meta.ppExpr xTy}"
        let wLit := Syntax.mkNumLit (toString w)
        pure (← `($x), ← `(.bitvec (.concrete $wLit)),
          ← `(PoisonOr.value $x), ← `(rfl), ← `($wLit:num))
    -- The operands are `Ctxt.Var`s: in an entry block the valuation is
    -- concrete and the default set reduces them, but in a *tail* block the
    -- ambient valuation is opaque and the destination is only known from an
    -- `EntryEnv`-style fact. Those go in the `with` list.
    let extras : Array Term := match extra with
      | some e => e.raw[1].getSepArgs.map fun s => ⟨s⟩
      | none => #[]
    -- The state the store lands in. Without `as`, the tactic writes it out, as
    -- it always did; with it, the caller's local stands in and `hst'` puts the
    -- definition back inside the side goal, where the term is harmless.
    let (stOut, putBack) ← match named with
      | some n => do
          let st' : Term := ⟨n.raw[1]⟩
          let hst' : Term := ⟨n.raw[3]⟩
          pure (st', ← `(tactic| (rw [$hst':term]; rfl)))
      | none => do
          pure (← `({ $st with mem := ($st).mem.splice $p $bits }), ← `(tactic| rfl))
    let simpArgs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      ((← #[← `(Expr.denoteOp), ← `(Ctxt.Valuation.singleton), ← `(simp_denote),
          ← `(simp_sllvm)].mapM pure) ++ extras).mapM fun t =>
        `(Lean.Parser.Tactic.simpLemma| $t:term)
    evalTactic (← `(tactic|
     (try simp only [bind_assoc]
      reduce_cfg_indices
      rw [BlockCom.run_bind_denote_var_of_nil (s' := $stOut)
        (by simp only [$[$simpArgs],*]
            rw [run_liftM (run_store (t := $ty) (x := $val) $hflat
              (show Fits (($st).mem) $p $width from Fits.mono $hp (by omega)))]
            $putBack:tactic)])))

/-- `peel_lifetime` runs the next `llvm.lifetime` marker, which moves neither
the state nor the valuation; the block's last instruction included. -/
macro "peel_lifetime" : tactic =>
  `(tactic| first | rw [BlockCom.run_bind_denote_lifetime] | rw [BlockCom.run_denote_lifetime])

open Lean Elab Tactic Meta in
/-- `peel_load t, blk, p, hblk, s` runs the next `llvm.load` of type `t`,
binding the value the live block `blk` holds at `p`.

`t : LLVM.Ty` (a `.bitvec`, or a `.vector` of them at any lane count)
`blk : LiveBlock`
`p : Pointer`
`hblk : (s.mem)[p.id]? = some (.live blk)`
`s : GlobalState` -/
elab "peel_load " t:term ", " blk:term ", " p:term ", " hblk:term ", " st:term : tactic =>
  withMainContext do
    let isVec : Bool ← withoutModifyingState do
      let ty ← Term.elabTerm (← `((($t) : LLVM.Ty))) none
      return (← whnf (← instantiateMVars ty)).isAppOf ``InstCombine.MTy.vector
    -- the loaded width, as a literal: the `omega` obligation below needs one
    let width ← withoutModifyingState do
      let e ← Term.elabTerm (← `((LLVM.Ty.width (($t) : LLVM.Ty) : Nat))) none
      let some n := (← whnf (← instantiateMVars e)).rawNatLit?
        | throwError "peel_load: cannot reduce the width of {← ppExpr e} to a literal"
      `(term| $(Syntax.mkNumLit (toString n)):num)
    -- a vector decodes lane by lane, a scalar is the extract itself
    let val ← if isVec then
        `(LLVM.Ty.unflatten $t (($blk).bytes.extractLsb' ($p).offsetInBits $width))
      else
        `(PoisonOr.value (($blk).bytes.extractLsb' ($p).offsetInBits $width))
    evalTactic (← `(tactic|
     (try simp only [bind_assoc]
      reduce_cfg_indices
      rw [BlockCom.run_bind_denote_var_of_value (x := $val) (s' := $st)
        (by simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
            rw [run_liftM (run_load (t := $t) ($hblk)
              (by show ($p).offsetInBits + $width ≤ _; omega))]
            rfl)])))

open Lean Elab Tactic in
/-- `peel_gep off with p, hp, s as x` peels back a `getelementptr` instruction
computing an offset pointer from `hp` at state `s`. `hp` should be a `Fits`
statement with enough remaining space.
The new pointer will be called `x` and there will be a hypothesis `hx` stating
the remaining `Fits` for `x`. -/
elab "peel_gep " off:term " with " p:term ", " hp:term ", " st:term " as " nm:ident : tactic => do
  let n ← nextStepIndex (← getMainGoal)
  let nLit := Syntax.mkNumLit (toString n)
  let vBase := mkIdent (Name.mkSimple "v")
  let v := mkIdent (Name.mkSimple ("v" ++ toString n))
  let hv := mkIdent (Name.mkSimple ("hv" ++ toString n))
  let base := nm.getId.eraseMacroScopes.toString
  let ptr := mkIdent (Name.mkSimple base)
  let hptr := mkIdent (Name.mkSimple ("h" ++ base))
  evalTactic (← `(tactic| denote_step_all $vBase $nLit))
  evalTactic (← `(tactic| denote_eval $vBase $nLit $nLit))
  evalTactic (← `(tactic| let $ptr := ($p).withOffset (($off) : BitVec 64)))
  evalTactic (← `(tactic| have $hptr:ident :=
        remainingFits ($st).mem $p $hp (($off) : BitVec 64) (by simp)))
  -- `remainingFits` leaves the size as `n - o.toNat * 8`; normalise it to a
  -- literal so the obligations downstream are `omega`-shaped.
  evalTactic (← `(tactic| norm_num [$ptr:ident] at $hptr:ident))
  evalTactic (← `(tactic| have vValue : $v = .value $ptr := by
        simp [$hv:ident, gep, gepConst, ptradd, $ptr:ident, Pointer.withOffset, Ctxt.Valuation.singleton,
          LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?, simp_sllvm]))
  evalTactic (← `(tactic| subst vValue))
  evalTactic (← `(tactic| clear $hv))

/-- `peel_memset b, len, p, hp, s` runs the next `llvm.intr.memset` instruction,
filling `len` bytes with the byte `b` at `p`.

`b : BitVec 8`
`len : Nat`
`p : Pointer`
`hp : Fits s.mem p (8 * len)`
`s : GlobalState` -/
macro "peel_memset " b:term ", " len:term ", " p:term ", " hp:term ", " st:term : tactic =>
  `(tactic|
   (try simp only [bind_assoc]
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_nil
      (s' := { $st with mem := ($st).mem.splice $p (BitVec.replicate $len $b) })
      (by simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
          rw [run_liftM (run_memset (b := $b) (len := BitVec.ofNat 64 $len)
            (show Fits (($st).mem) $p (8 * (BitVec.ofNat 64 $len).toNat) from
              Fits.mono $hp (by simp)))]
          rw [show (BitVec.ofNat 64 $len).toNat = $len from by simp]
          rfl)
    ]))

open Lean Elab Tactic in
open Lean Elab Tactic in
/-- `peel_memcpy len, dst, src, hsrc, hdst, s` runs the next `llvm.intr.memcpy`
of `len` *bytes* from `src` to `dst`.

`hsrc : Fits s.mem src (8 * len)` and `hdst : Fits s.mem dst (8 * len)`; the
source's block comes out of `hsrc` by `choose` rather than being passed, since
destructing the `∃` in `Fits` at a call site reverts the walk goal.

`… as s' := hs'` names the state it lands in, for chained copies: the second
of a pair would otherwise spell the first's spliced state inline three times
over, and every later `isDefEq` would walk that term rather than an `fvar`.

`memcpy` reads before it writes, so what lands at `dst` is the source block's
bytes in the *pre-copy* state. -/
elab "peel_memcpy " len:term ", " dst:term ", " src:term ", "
    hsrc:term ", " hdst:term ", " st:term named:(stateNaming)? : tactic => do
  let (stOut, putBack) ← match named with
    | some n => do
        let st' : Term := ⟨n.raw[1]⟩
        let hst' : Term := ⟨n.raw[3]⟩
        pure (st', ← `(tactic| (rw [$hst':term]; rfl)))
    | none => do
        pure (← `({ $st with mem := ($st).mem.splice $dst (BitVec.extractLsb' (($src).offsetInBits) (8 * $len) ($hsrc).choose.bytes) }), ← `(tactic| rfl))
  evalTactic (← `(tactic|
   (try simp only [bind_assoc]
    reduce_cfg_indices
    rw [BlockCom.run_bind_denote_var_of_nil (s' := $stOut)
      (by simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
          rw [run_liftM (run_memcpy (len := BitVec.ofNat 64 $len)
            (($hsrc).choose_spec.1)
            (by have := ($hsrc).choose_spec.2
                rw [show (BitVec.ofNat 64 $len).toNat = $len from by simp]
                omega)
            (by rw [show (BitVec.ofNat 64 $len).toNat = $len from by simp]; exact $hdst))]
          rw [show (BitVec.ofNat 64 $len).toNat = $len from by simp]
          $putBack:tactic)])))

/-- `peel_addressof hg` runs the next `llvm.mlir.addressof`, binding the
global's address. Simpler than every other peel: the operation only reads the
symbol table, so the state does not move.

`hg : GlobalPtr s name p` -- or `h.ptr` from a `HoldsGlobal`. What the global
*holds* is spent later, by the `peel_load`s that read through the pointer. -/
macro "peel_addressof " hg:term : tactic =>
  `(tactic| first
    | rw [BlockCom.run_bind_denote_var_of_value
        (x := PoisonOr.value _)
        (by simp only [denoteOp_addressof, EffectM.run_map]
            rw [run_addressof $hg]
            rfl)]
    | rw [BlockCom.run_denote_var_of_value
        (x := PoisonOr.value _)
        (by simp only [denoteOp_addressof, EffectM.run_map]
            rw [run_addressof $hg]
            rfl)])

/-- `peel_alloca from s as t with ht` runs the next `llvm.alloca` instruction,
binding the fresh pointer `⟨⟨s.alloc.nextFreeBlock⟩, 0⟩` and advancing the state
to `t`. `t` and `ht` are the first two facts
`GlobalState.exists_afterAlloca_facts` provides.

`s : GlobalState`
`t : GlobalState`
`ht : t = s.afterAlloca w` -/
macro "peel_alloca" " from " st:term " as " t:term " with " ht:term : tactic =>
  `(tactic| first
    | rw [BlockCom.run_bind_denote_var_of_value
        (x := PoisonOr.value ⟨⟨($st).alloc.nextFreeBlock⟩, 0⟩) (s' := $t)
        (by simp only [denoteOp_alloca, EffectM.run_map]
            rw [run_alloca, $ht:term]
            rfl)]
    | rw [BlockCom.run_denote_var_of_value
        (x := PoisonOr.value ⟨⟨($st).alloc.nextFreeBlock⟩, 0⟩) (s' := $t)
        (by simp only [denoteOp_alloca, EffectM.run_map]
            rw [run_alloca, $ht:term]
            rfl)])

open Lean Elab Tactic in
/-- `peel_alloca_chain s, cw, 21` runs the 21 `alloca`s of `s.allocaChain cw`. -/
elab "peel_alloca_chain " st:term ", " w:term ", " n:num : tactic => do
  for k in [0 : n.getNat] do
    let ki := Syntax.mkNumLit (toString k)
    let ki1 := Syntax.mkNumLit (toString (k + 1))
    evalTactic (← `(tactic|
      peel_alloca from (GlobalState.allocaChain $st $w $ki)
        as (GlobalState.allocaChain $st $w $ki1)
        with (allocaChain_step $st $w $ki $ki1 rfl)))

open Lean Elab Tactic in
/-- `fold_cells s, cw, cellPtr, n` folds the `n` chain pointers an `alloca`
prologue leaves in the valuation back to `cellPtr s k`, the form facts about
them are stated over and the form `peel_load` matches against. -/
elab "fold_cells " st:term ", " w:term ", " cp:term ", " n:num : tactic => do
  let mut lems : Array Term := #[]
  for k in [0 : n.getNat] do
    let kn := Syntax.mkNumLit (toString k)
    lems := lems.push (← `(show
      (⟨⟨(GlobalState.allocaChain $st $w $kn).alloc.nextFreeBlock⟩, 0⟩ : Pointer)
        = $cp $st $kn from rfl))
  evalTactic (← `(tactic| simp only [$[$lems:term],*]))

end Firedancer
