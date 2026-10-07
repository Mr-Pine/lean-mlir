import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlinePrefixSquare

/-! The previously exposed piecewise prefix is definitionally the same source
instruction interval, independent of intermediate registers and memory. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR

theorem pieces_eq_segment (f : Func) (block : Fin f.n) (first : Nat)
    (counts : List Nat) (E : Env f.Γ) :
    OuterComposition.pieces f block first counts E =
      Cutpoint.segment f block first counts.sum E := by
  induction counts generalizing first E with
  | nil => rfl
  | cons count rest ih =>
    simp only [OuterComposition.pieces,List.sum_cons]
    rw [segment_append]
    simp only [ih]

theorem executionPrefix_eq_segment (g : Globals) (E : Env program.Γ) :
    executionPrefix g E = Cutpoint.segment (program sqrtRatioPrimitives g) 0 0 1047 E := by
  rw [executionPrefix,pieces_eq_segment,executionPieceLengths_sum]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
