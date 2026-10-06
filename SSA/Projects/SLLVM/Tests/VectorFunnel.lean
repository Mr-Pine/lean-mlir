/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
Vector funnel shifts: parsed programs preserve lane order, reduce each shift
amount modulo the element width, and propagate poison only within a lane.
Unequal high and low inputs distinguish funnels from rotations and catch
operand reversal; the final lane checks the largest representable amount.
-/
namespace LeanMLIR.SLLVM.Tests.VectorFunnel

open LeanMLIR
open InstCombine (LLVM)

private abbrev V := SLLVM.Ty.arith (.vector 4 (.bitvec 8))
private abbrev Vec := Vector (LLVM.IntW 8) 4

private def vec (xs : List Int) : Vec := LLVM.Ty.dense (.vector 4 (.bitvec 8)) xs

def left : Com SLLVM (Ctxt.ofList [V, V, V]) .pure [V] :=
  [sllvm| {
    ^entry(%a:vector<4xi8>, %b:vector<4xi8>, %n:vector<4xi8>):
      %r = "llvm.intr.fshl"(%a, %b, %n) : (vector<4xi8>, vector<4xi8>, vector<4xi8>) -> vector<4xi8>
      "llvm.return"(%r) : (vector<4xi8>) -> ()
  }]

def right : Com SLLVM (Ctxt.ofList [V, V, V]) .pure [V] :=
  [sllvm| {
    ^entry(%a:vector<4xi8>, %b:vector<4xi8>, %n:vector<4xi8>):
      %r = "llvm.intr.fshr"(%a, %b, %n) : (vector<4xi8>, vector<4xi8>, vector<4xi8>) -> vector<4xi8>
      "llvm.return"(%r) : (vector<4xi8>) -> ()
  }]

private def run (p : Com SLLVM (Ctxt.ofList [V, V, V]) .pure [V]) (a b n : Vec) : Vec :=
  (p.denote (Ctxt.Valuation.ofHVector [n, b, a]ₕ)).head

/-- The parsed programs refine scalar funnel shifts for arbitrary lane values,
including poison, rather than just for the concrete fixtures below. -/
theorem left_lane (a b n : Vec) (i : Fin 4) :
    (run left a b n)[i] = fshl a[i] b[i] n[i] := by
  change (vfshl a b n)[i] = _
  exact vfshl_getElem a b n i

theorem right_lane (a b n : Vec) (i : Fin 4) :
    (run right a b n)[i] = fshr a[i] b[i] n[i] := by
  change (vfshr a b n)[i] = _
  exact vfshr_getElem a b n i

example : run left (vec [170, 18, 52, 86]) (vec [240, 129, 171, 205])
    (vec [0, 1, 8, 255]) = vec [170, 37, 52, 102] := rfl

example : run right (vec [170, 18, 52, 86]) (vec [240, 129, 171, 205])
    (vec [0, 1, 8, 255]) = vec [240, 64, 171, 173] := rfl

/-- Poison in each of the three operands stays in its lane; even at zero
amount both funnel operands are demanded, as in the scalar semantics. -/
example : run left ((vec [170, 18, 52, 86]).set 0 .poison)
    ((vec [240, 129, 171, 205]).set 2 .poison)
    ((vec [0, 1, 8, 255]).set 1 .poison) =
      (((vec [0, 0, 0, 102]).set 0 .poison).set 1 .poison).set 2 .poison := rfl

example : run right ((vec [170, 18, 52, 86]).set 0 .poison)
    ((vec [240, 129, 171, 205]).set 2 .poison)
    ((vec [0, 1, 8, 255]).set 1 .poison) =
      (((vec [0, 0, 0, 173]).set 0 .poison).set 1 .poison).set 2 .poison := rfl

end LeanMLIR.SLLVM.Tests.VectorFunnel
