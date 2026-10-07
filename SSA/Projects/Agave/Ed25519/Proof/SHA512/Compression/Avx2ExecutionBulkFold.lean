import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkMemory

/-! Two-message folds and cursor arithmetic shared by the AVX2 outer induction. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
open Spec

/-- Advancing one AVX2 pair consumes exactly 256 bytes. -/
theorem bulk_pair_pointer (data : Pointer) (index : Nat) :
    (data.add (BitVec.ofNat 64 (128*index))).add 256#64 =
      data.add (BitVec.ofNat 64 (128*(index+2))) := by
  rw [Pointer.add_add]
  congr 1
  rw [← BitVec.ofNat_add]
  congr 1

/-- The streaming specification processes the first and second lanes in order. -/
theorem bulk_run_pair (initial : Spec.State) (mem : MemoryState) (data : Pointer) (n : Nat) :
    Spec.run (pack initial) (readBytes mem data (128*(n+2))) =
      Spec.run (pack (compressBlock
        (compressBlock initial (readBytes mem data 128))
        (readBytes mem (data.add 128#64) 128)))
        (readBytes mem (data.add 256#64) (128*n)) := by
  rw [show n+2 = (n+1)+1 by omega, run_readBytes_succ, run_readBytes_succ]
  simp only [Pointer.add_add]
  rfl

end Agave.Ed25519.SHA512.Execution.Avx2
