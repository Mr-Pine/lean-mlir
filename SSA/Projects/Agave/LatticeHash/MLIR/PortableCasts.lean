import SSA.Projects.Agave.LatticeHash.MLIR.GArithmetic
import SSA.Projects.Firedancer.Proof.Tactics

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)

/-- The actual `lshr 32; trunc nuw` sequence is defined for every u64 counter.
The upper-half truncation loses no set bits, as required by the compiler flag. -/
theorem portable_counter_high (counter : BitVec 64) :
    LLVM.trunc 32 (LLVM.lshr (.value counter) (.value (32 : BitVec 64))) {nsw := false, nuw := true} =
    .value (counter.extractLsb' 32 32) := by
  simp [simp_llvm, simp_llvm_option]
  split_ifs with h
  · congr 1
  · exfalso
    apply h
    bv_decide

end AgaveLatticeHash.MLIR
