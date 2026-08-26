import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.MLIR.DenoteStep

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

macro "peel_load " blk:term ", " p:term ", " hblk:term ", " st:term : tactic =>
  `(tactic|
   (try simp only [bind_assoc]
    rw [BlockCom.run_bind_denote_var_of_value
      (x := PoisonOr.value (($blk).bytes.extractLsb' ($p).offsetInBits 64)) (s' := $st)
      (by simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
          rw [run_liftM (run_load ($hblk) (by show ($p).offsetInBits + 64 ≤ _; omega))]
          rfl)
    ]))

/-- `Fits` is antitone in the size demanded. -/
theorem Fits.mono {m : MemoryState} {p : Pointer} {n n' : Nat} (h : Fits m p n)
    (hle : n' ≤ n) : Fits m p n' :=
  let ⟨blk, hblk, hlen⟩ := h; ⟨blk, hblk, by omega⟩

/-- `peel_store x, p, hp, s` runs the next instruction, which must be an
`llvm.store` of a 64-bit `x` through `p`, and leaves the run at `s` with `x`
spliced in at `p`. `hp : Fits ($st).mem $p n` is the no-trap obligation, for any `n` at least
64 -- the room the store itself needs is weakened out of it.

A `store` binds no variable, so -- unlike `peel_load` -- there is no `v<n>` to
name afterwards; only the state moves. -/
macro "peel_store " x:term ", " p:term ", " hp:term ", " st:term : tactic =>
  `(tactic|
   (try simp only [bind_assoc]
    rw [BlockCom.run_bind_denote_var_of_nil
      (s' := { $st with mem := ($st).mem.splice $p $x })
      (by simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
          rw [run_liftM (run_store (t := .bitvec (.concrete 64))
            (x := PoisonOr.value $x) rfl
            (show Fits (($st).mem) $p 64 from Fits.mono $hp (by omega)))]
          rfl)
    ]))

/-- Stepping `o` bytes into a block leaves the same block, with `o * 8` fewer
bits available. -/
theorem remainingFits (m: MemoryState) (p: Pointer) (hp: Fits m p n) (o: BitVec 64)
    (ho : o.toNat * 8 ≤ n) : Fits m (p.withOffset o) (n - (o.toNat * 8)) := by
  obtain ⟨blk, hblk, hlen⟩ := hp
  refine ⟨blk, hblk, ?_⟩
  have h1 : p.offset.toNat < 2 ^ 64 := p.offset.isLt
  have h2 : o.toNat < 2 ^ 64 := o.isLt
  simp only [Pointer.withOffset, Pointer.offsetInBits, LiveBlock.lengthInBits,
    BitVec.toNat_add] at hlen ⊢
  omega

/-- `₀`-style index for the per-limb names the tactics below generate. -/
def subscript (i : Nat) : String :=
  (toString i).map fun c => Char.ofNat (c.toNat - '0'.toNat + '₀'.toNat)

open Lean Elab Tactic in
/-- `peel_gep i, p, hp, s, x` steps the next instruction, which must be a
`getelementptr` off `p` by the constant `i`, and replaces the pointer it yields
by `x<i> := p.withOffset (8 * i)` -- substituted into the goal, so the stepper's
`v<n>`/`hv<n>` for the gep are gone afterwards. Leaves `hx<i> : Fits s.mem x<i>
_` beside it.

Assumes a five-limb field element at `p`, i.e. `hp : Fits s.mem p (5 * 64)`;
the remaining size is `(5 - i) * 64`. -/
elab "peel_gep " i:num ", " p:term ", " hp:term ", " st:term ", " nm:ident : tactic => do
  let num := i.getNat
  -- `withOffset` counts bytes, `Fits` counts bits
  let offBytes := Syntax.mkNumLit (toString (num * 8))
  let remainingBits := Syntax.mkNumLit (toString ((5 - num) * 64))
  let n ← nextStepIndex (← getMainGoal)
  let nLit := Syntax.mkNumLit (toString n)
  let vBase := mkIdent (Name.mkSimple "v")
  let v := mkIdent (Name.mkSimple ("v" ++ toString n))
  let hv := mkIdent (Name.mkSimple ("hv" ++ toString n))
  let s := subscript num
  -- `nm` is the stem: the gep's result is `nm<i>`, its `Fits` is `hnm<i>`
  let base := nm.getId.eraseMacroScopes.toString
  let ptr := mkIdent (Name.mkSimple (base ++ s))
  let hptr := mkIdent (Name.mkSimple ("h" ++ base ++ s))
  evalTactic (← `(tactic| denote_step_all $vBase $nLit))
  evalTactic (← `(tactic| denote_eval $vBase $nLit $nLit))
  evalTactic (← `(tactic| let $ptr := ($p).withOffset (($offBytes) : BitVec 64)))
  evalTactic (← `(tactic| have $hptr:ident : Fits ($st).mem $ptr ($remainingBits) := by
        simpa using remainingFits ($st).mem $p $hp ($offBytes) (by simp)))
  evalTactic (← `(tactic| have vValue : $v = .value $ptr := by
        simp [$hv:ident, gep, ptradd, $ptr:ident, Pointer.withOffset, Ctxt.Valuation.singleton,
          LLVM.add, LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?, simp_sllvm]))
  evalTactic (← `(tactic| subst vValue))
  evalTactic (← `(tactic| clear $hv))

open Lean Elab Tactic in
/-- `peel_limb i, p<i>, hp<i>` peels the load at `p<i>`, naming its value
`limb<i>` with defining equation `hlimb<i>`.

`peel_load` needs a block hypothesis for the pointer being loaded, not for the
base pointer -- the `load` carries the whole pointer, offset included -- so this
first destructs `hp<i>` into `blk<i>`/`hblk<i>`/`hlen<i>`, which also gives the
no-trap bound directly. The block is then identified with the base `blk` and
substituted away, so only one block name survives.

Expects `blk`, `hblk` and the state `s` in scope, under those names. -/
elab "peel_limb " i:num ", " ptr:ident ", " hptr:term : tactic => do
  let baseblk := mkIdent (Name.mkSimple "blk")
  let basehblk := mkIdent (Name.mkSimple "hblk")
  let s := subscript i.getNat
  let blk := mkIdent (Name.mkSimple ("blk" ++ s))
  let hblk := mkIdent (Name.mkSimple ("hblk" ++ s))
  let hlen := mkIdent (Name.mkSimple ("hlen" ++ s))
  let limb := mkIdent (Name.mkSimple ("limb" ++ s))
  let hlimb := mkIdent (Name.mkSimple ("hlimb" ++ s))
  let st := mkIdent (Name.mkSimple "s")
  -- byte offset of limb `i`, and the bits still left after it
  evalTactic (← `(tactic| obtain ⟨$blk, $hblk, $hlen⟩ := id $hptr))
  evalTactic (← `(tactic| peel_load $blk, $ptr, $hblk, $st))
  evalTactic (← `(tactic| set $limb:ident := (($blk).bytes.extractLsb' ($ptr).offsetInBits 64) with $hlimb:ident))
  -- `$ptr` is a `let`-bound pointer for i > 0 and must be in the simp set to
  -- zeta-unfold; at limb 0 it is the plain fvar `p`, which simp would reject.
  if i.getNat == 0 then
    evalTactic (← `(tactic| have hblkeq : $baseblk = $blk := by
        simpa [Pointer.withOffset, $basehblk:ident] using $hblk))
  else
    evalTactic (← `(tactic| have hblkeq : $baseblk = $blk := by
        simpa [$ptr:ident, Pointer.withOffset, $basehblk:ident] using $hblk))
  evalTactic (← `(tactic| subst hblkeq))
  evalTactic (← `(tactic| clear $hblk $hlen))

end Firedancer.Ref
