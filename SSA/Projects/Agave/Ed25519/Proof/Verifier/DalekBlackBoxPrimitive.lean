import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContracts
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.BlackBox

/-!
Discharge the Dalek verifier's byte helper contracts using the independently
imported bodies from the same pinned crate IR. Both bodies preserve memory but
advance the allocation counter: one block for black_box, 33 for byte equality.

The exact source symbols are:
* `_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519`
* `_RNvXs8_Csh8VEmffyqhs_6subtleShNtB5_14ConstantTimeEq5ct_eqCsjK63O35OHGN_14solana_ed25519`

`bcmp` remains an external library obligation: the pinned verifier IR contains
only its declaration, not an implementation. These proofs do not substitute a
model equality function for that absent compiled routine. The byte equality
proof establishes the returned value and sequential memory frame, not timing or
volatile-event trace equivalence.
-/
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR

namespace BytePrimitives

/-- Reclaimed private allocations preserve every memory read and live range. -/
theorem readOnly_add_blocks (state : GlobalState) (blocks : Nat) (hwf : state.WF) :
    ReadOnlyFrame state {state with alloc := ⟨state.alloc.nextFreeBlock + blocks⟩} := by
  exact ⟨hwf.add_blocks, fun _ _ h => h, fun _ _ => rfl⟩

/-- The exact volatile-load black-box body satisfies byte identity with its
true allocation effect and needs only well-formed initial memory. -/
theorem blackBox_contract :
    BlackBoxContract Encoding.Decompress.Execution.BlackBox.program.call := by
  intro value state hwf
  refine ⟨{state with alloc := ⟨state.alloc.nextFreeBlock + 1⟩}, ?_,
    readOnly_add_blocks state 1 hwf⟩
  exact Encoding.Decompress.Execution.BlackBox.program_call value state hwf

end BytePrimitives
end Agave.Ed25519.Verifier.Execution.Dalek
