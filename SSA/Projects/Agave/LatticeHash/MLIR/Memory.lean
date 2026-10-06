import SSA.Projects.Firedancer.Proof.Tactics.Memory

/-! Shared memory lemmas for the compiler-emitted Agave vector kernels.
The lane count and element width are independent: the same bytes are accessed
as u32 lanes during compression and u16 lanes during LtHash accumulation. -/

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM
open InstCombine (LLVM)

def packBits {n w : Nat} (v : Vector (BitVec w) n) : BitVec (w * n) :=
  LLVM.Ty.flattenBV (.vector n (.bitvec (.concrete w))) (v.map PoisonOr.value)

theorem flatten_packBits {n w : Nat} (v : Vector (BitVec w) n) :
    LLVM.Ty.flatten (.vector n (.bitvec (.concrete w))) (v.map PoisonOr.value) =
      .value (packBits v) := by
  rw [LLVM.Ty.flatten, ite_eq_left]
  · rfl
  · intro i
    show LLVM.Ty.ofBitvec ((v.map PoisonOr.value)[i.val]) ≠ .poison
    rw [Vector.getElem_map]
    exact PoisonOr.value_ne_poison _

theorem unflatten_packBits {n w : Nat} (v : Vector (BitVec w) n) :
    LLVM.Ty.unflatten (.vector n (.bitvec (.concrete w))) (packBits v) =
      v.map PoisonOr.value := by
  apply LLVM.Ty.unflatten_flattenBV
  intro i
  show LLVM.Ty.ofBitvec ((v.map PoisonOr.value)[i.val]) ≠ .poison
  rw [Vector.getElem_map]
  exact PoisonOr.value_ne_poison _

theorem extract_packBits {n w : Nat} (v : Vector (BitVec w) n) (i : Fin n) :
    (packBits v).extractLsb' (i.val * w) w = v[i] := by
  have h := LLVM.Ty.extractLsb'_flattenBV_vector
    (e := .bitvec (.concrete w)) (v.map PoisonOr.value) i.val i.isLt
  simpa [packBits, LLVM.Ty.flattenBV, LLVM.Ty.width] using h

theorem run_load_vector {n w : Nat} {m : MemoryState} {p : Pointer}
    (v : Vector (BitVec w) n) (hp : Fits m p (w * n))
    (hv : Firedancer.readWord? p (w * n) m = some (packBits v)) :
    (load (.value p) (.vector n (.bitvec (.concrete w)))).run m =
      .value (v.map PoisonOr.value, m) := by
  obtain ⟨block, hblk, hlen⟩ := hp
  have hread : block.bytes.extractLsb' p.offsetInBits (w * n) = packBits v := by
    simpa [Firedancer.readWord?, MemoryState.live?, hblk] using hv
  rw [run_load (t := .vector n (.bitvec (.concrete w))) hblk hlen]
  simp only [LLVM.Ty.width]
  rw [hread, unflatten_packBits]


open Lean Elab Tactic Meta in
/-- Store a fully defined vector at any concrete lane count and word width. -/
elab "peel_store_vector " x:term ", " p:term ", " hp:term ", " st:term
    named:(Firedancer.stateNaming)? extra:(" with " term,+)? : tactic =>
  withMainContext do
    let xTy ← withoutModifyingState do
      whnf (← instantiateMVars (← inferType (← Term.elabTerm x none)))
    unless xTy.isAppOf ``Vector do
      throwError "peel_store_vector expects a Vector (BitVec w) n"
    let args := xTy.getAppArgs
    let elTy ← whnf args[0]!
    unless elTy.isAppOf ``BitVec do
      throwError "peel_store_vector expects BitVec elements"
    let some w := (← whnf elTy.getAppArgs[0]!).rawNatLit?
      | throwError "peel_store_vector requires a concrete element width"
    let some n := (← whnf args[1]!).rawNatLit?
      | throwError "peel_store_vector requires a concrete lane count"
    let wLit := Syntax.mkNumLit (toString w)
    let nLit := Syntax.mkNumLit (toString n)
    let bitsLit := Syntax.mkNumLit (toString (w*n))
    let extras : Array Term := match extra with
      | some e => e.raw[1].getSepArgs.map fun s => ⟨s⟩
      | none => #[]
    let (stOut, putBack) ← match named with
      | some nm => do
          let st' : Term := ⟨nm.raw[1]⟩
          let hst' : Term := ⟨nm.raw[3]⟩
          pure (st', ← `(tactic| (rw [$hst':term]; rfl)))
      | none => do
          pure (← `({ $st with mem := ($st).mem.splice $p (packBits $x) }),
            ← `(tactic| rfl))
    let simpArgs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      ((← #[← `(Expr.denoteOp), ← `(Ctxt.Valuation.singleton), ← `(simp_denote),
          ← `(simp_sllvm)].mapM pure) ++ extras).mapM fun t =>
        `(Lean.Parser.Tactic.simpLemma| $t:term)
    evalTactic (← `(tactic|
      (try simp only [bind_assoc]
       reduce_cfg_indices
       rw [BlockCom.run_bind_denote_var_of_nil (s' := $stOut)
         (by simp only [$[$simpArgs],*]
             rw [run_liftM (run_store
               (t := .vector $nLit (.bitvec (.concrete $wLit)))
               (x := ($x).map PoisonOr.value) (flatten_packBits $x)
               (show Fits (($st).mem) $p $bitsLit from Firedancer.Fits.mono $hp (by omega)))]
             $putBack:tactic)])))

/-- Load a vector using a bounds fact and its independently specified bytes. -/
macro "peel_load_vector " x:term ", " p:term ", " hp:term ", " hv:term ", " st:term : tactic =>
  `(tactic|
    (try simp only [bind_assoc]
     reduce_cfg_indices
     rw [BlockCom.run_bind_denote_var_of_value
       (x := ($x).map PoisonOr.value) (s' := $st)
       (by simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
           rw [run_liftM (run_load_vector (p := $p) $x $hp $hv)]
           rfl)]))

end AgaveLatticeHash.MLIR
