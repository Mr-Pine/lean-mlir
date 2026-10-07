import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Ladder

/-! The four signed addition interfaces depend only on the ladder specification.
Their definition does not import any point-doubling or square-helper execution. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Tables (F)
set_option maxRecDepth 10000

/-- Arithmetic residuals after linking bb18 to its imported implementation.
Only the four signed addition blocks remain as execution obligations. -/
structure AdditionBlocks (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (ctx : LocalContext) (a b : Nat) (da db : Pointer)
    (table : TableIndex → Extended F) : Prop where
  subA : ∀ E s pos Q, LadderReady ctx a b da db E s pos → PointAt .doubled E Q →
    nafDigits 5 a pos.val < 0 →
    E.read (%527) = .value (BitVec.ofNat 64 ((nafMagnitude5 a pos.val).val / 2)) →
    ∃ E' s', ArithmeticBlockPost p g ctx a b da db 22 26 .afterA
      (signedPoint table false (nafDigits 5 a pos.val) Q) E s pos E' s'
  addA : ∀ E s pos Q, LadderReady ctx a b da db E s pos → PointAt .doubled E Q →
    0 < nafDigits 5 a pos.val →
    E.read (%625) = .value (BitVec.ofNat 64 ((nafMagnitude5 a pos.val).val / 2)) →
    ∃ E' s', ArithmeticBlockPost p g ctx a b da db 25 26 .afterA
      (signedPoint table false (nafDigits 5 a pos.val) Q) E s pos E' s'
  subB : ∀ E s pos Q, LadderReady ctx a b da db E s pos → PointAt .afterA E Q →
    nafDigits 8 b pos.val < 0 →
    E.read (%708) = .value (BitVec.ofNat 64 ((nafMagnitude8 b pos.val).val / 2)) →
    ∃ E' s', ArithmeticBlockPost p g ctx a b da db 29 30 .afterB
      (signedPoint table true (nafDigits 8 b pos.val) Q) E s pos E' s'
  addB : ∀ E s pos Q, LadderReady ctx a b da db E s pos → PointAt .afterA E Q →
    0 < nafDigits 8 b pos.val →
    E.read (%813) = .value (BitVec.ofNat 64 ((nafMagnitude8 b pos.val).val / 2)) →
    ∃ E' s', ArithmeticBlockPost p g ctx a b da db 33 30 .afterB
      (signedPoint table true (nafDigits 8 b pos.val) Q) E s pos E' s'

end Agave.Ed25519.DoubleBase.ExecutionAvx2
