import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Avx512.Spec.Quad

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Firedancer.Avx512 (vecBV flatten_vecBV)

open Lean Elab Tactic Meta in
/-- `peel_store x, p, hp, s` runs the next `llvm.store` instruction, storing
`x` (of type `Vector (BitVec 64) 8` or `BitVec 64` at `p` where `hp` states
`Fits s.mem p (512 or 64)`.
 -/
elab "peel_store " x:term ", " p:term ", " hp:term ", " st:term : tactic =>
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
    evalTactic (← `(tactic|
     (try simp only [bind_assoc]
      rw [BlockCom.run_bind_denote_var_of_nil
        (s' := { $st with mem := ($st).mem.splice $p $bits })
        (by simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
            rw [run_liftM (run_store (t := $ty) (x := $val) $hflat
              (show Fits (($st).mem) $p $width from Fits.mono $hp (by omega)))]
            rfl)])))

/-- `peel_lifetime` runs the next `llvm.lifetime` marker, which moves neither
the state nor the valuation. -/
macro "peel_lifetime" : tactic =>
  `(tactic| rw [BlockCom.run_bind_denote_lifetime])

open Lean Elab Tactic Meta in
/-- `peel_load t, blk, p, hblk, s` runs the next `llvm.load` of type `t`,
binding the value the live block `blk` holds at `p`.

`t : LLVM.Ty` (`.bitvec (.concrete 64)` or `.vector 8 (.bitvec (.concrete 64))`)
`blk : LiveBlock`
`p : Pointer`
`hblk : (s.mem)[p.id]? = some (.live blk)`
`s : GlobalState` -/
elab "peel_load " t:term ", " blk:term ", " p:term ", " hblk:term ", " st:term : tactic =>
  withMainContext do
    let isVec : Bool ← withoutModifyingState do
      let ty ← Term.elabTerm (← `((($t) : LLVM.Ty))) none
      return (← whnf (← instantiateMVars ty)).isAppOf ``InstCombine.MTy.vector
    let (val, width) ← if isVec then
        pure (← `(LLVM.Ty.unflatten $t (($blk).bytes.extractLsb' ($p).offsetInBits 512)),
          ← `(512))
      else do
        -- the scalar width, as a literal: the `omega` obligation below needs one
        let w ← withoutModifyingState do
          let e ← Term.elabTerm (← `((LLVM.Ty.width (($t) : LLVM.Ty) : Nat))) none
          let some n := (← whnf (← instantiateMVars e)).rawNatLit?
            | throwError "peel_load: cannot reduce the width of {← ppExpr e} to a literal"
          `(term| $(Syntax.mkNumLit (toString n)):num)
        pure (← `(PoisonOr.value (($blk).bytes.extractLsb' ($p).offsetInBits $w)), w)
    evalTactic (← `(tactic|
     (try simp only [bind_assoc]
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
        simp [$hv:ident, gep, ptradd, $ptr:ident, Pointer.withOffset, Ctxt.Valuation.singleton,
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
    rw [BlockCom.run_bind_denote_var_of_nil
      (s' := { $st with mem := ($st).mem.splice $p (BitVec.replicate $len $b) })
      (by simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
          rw [run_liftM (run_memset (b := $b) (len := BitVec.ofNat 64 $len)
            (show Fits (($st).mem) $p (8 * (BitVec.ofNat 64 $len).toNat) from
              Fits.mono $hp (by simp)))]
          rw [show (BitVec.ofNat 64 $len).toNat = $len from by simp]
          rfl)
    ]))

/-- `peel_alloca from s as t with ht` runs the next `llvm.alloca` instruction,
binding the fresh pointer `⟨⟨s.alloc.nextFreeBlock⟩, 0⟩` and advancing the state
to `t`. `t` and `ht` are the first two facts
`GlobalState.exists_afterAlloca_facts` provides.

`s : GlobalState`
`t : GlobalState`
`ht : t = s.afterAlloca w` -/
macro "peel_alloca" " from " st:term " as " t:term " with " ht:term : tactic =>
  `(tactic|
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value ⟨⟨($st).alloc.nextFreeBlock⟩, 0⟩) (s' := $t)
      (by simp only [denoteOp_alloca, EffectM.run_map]
          rw [run_alloca, $ht:term]
          rfl)])

end Firedancer
