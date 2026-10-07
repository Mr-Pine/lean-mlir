import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.SourceAlignment6
import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.OutputValue

/-! Universal arithmetic correctness of the exact source reducer. The proof
joins the checked LLVM expression, its signed radix-2^21 arithmetic, and both
little-endian bit-layout boundaries. No digest certificate is a premise. -/

namespace Firedancer.Common.ScalarArithmetic
open IntegerRegisters

/-- Every 64-byte input has a defined source result, and its four stored words
encode exactly the canonical residue modulo the Ed25519 group order. -/
theorem sourceReduce_correct (digest : BitVec 512) :
    ∃ words, sourceReduce digest = some words ∧
      (packWords words).toNat = digest.toNat % groupOrder := by
  let d := inputDigits digest
  have hd : Bounded d := inputDigits_bounded digest
  have hm := inputMatches digest
  refine ⟨packingWords (packingInputs d), ?_, ?_⟩
  · rw [Registers.sourceReduce_eq, Registers.reduce_eq_packingWords digest d hd hm]
  · have h := packed_output_value d hd
    rw [output_exact d hd, inputValue_eq digest] at h
    exact_mod_cast h

end Firedancer.Common.ScalarArithmetic
