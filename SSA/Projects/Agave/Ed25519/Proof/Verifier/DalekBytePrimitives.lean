import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekBlackBoxPrimitive
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.BytesEq

/-!
Exact source symbol:
`_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519`.

`bcmp` remains an external library obligation: the pinned verifier IR contains
only its declaration, not an implementation. This file does not substitute a
model equality function for that absent compiled routine. The byte equality
proof establishes the returned value and sequential memory frame, not timing.
-/
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
namespace BytePrimitives

/-- The exact unrolled comparison, including all 33 imported black-box calls,
satisfies the verifier's 32-byte equality contract. No disjointness assumption
is needed for the two read-only inputs. -/
theorem bytesEq_contract :
    BytesEqContract (Encoding.Decompress.Execution.BytesEq.program
      Encoding.Decompress.Execution.bytesEqPrimitives).call := by
  intro left right state a b hwf ha hb
  refine ⟨{state with alloc := ⟨state.alloc.nextFreeBlock + 33⟩}, ?_,
    readOnly_add_blocks state 33 hwf⟩
  have h := Encoding.Decompress.Execution.BytesEq.program_exact left right state hwf ha.1 hb.1
  simpa only [args2, Encoding.Decompress.Execution.BytesEq.program.args, ha.2, hb.2] using h

end BytePrimitives
end Agave.Ed25519.Verifier.Execution.Dalek
