import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Linked
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Terminal
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Constants
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Sign
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Input

/-!
Execution progress for the manifest-pinned decompressor:
* all seven reachable helper bodies are imported without modifying any region
  instruction or attribute; `linkedProgram` binds every call to imported code;
* the actual subtle black_box returns its input byte, leaves caller memory
  unchanged, and advances the fresh-allocation counter by one;
* the actual common return block writes its incoming Option discriminant;
* arbitrary input bytes establish parser field value and tight limb bounds;
* the existing actual serial multiplication kernel establishes field value and
  tight output bounds; exact global bytes denote D and SQRT_M1;
* sign extraction and its flagged mask subtraction have kernel-checked
  arithmetic laws. Conditional limb assignment/negation remains outstanding.

This is not yet an execution proof of `linkedProgram` against `decompress`.
Outstanding: pow2k loop execution/termination and limb bounds; pow22501 stack
and call composition; the complete to_bytes and byte-comparison memory proofs;
all sqrt_ratio_i comparisons and stores; decompression entry/success blocks,
frame preservation, and X/Y/Z/T payload readback. The existing source-formula
soundness/completeness theorem does not discharge any of these obligations.

RIR models sequential memory values. In the preserved black_box region,
`volatile_` does not add an observable event to RIR's load semantics. Alignment,
noalias promises and concurrent/volatile event traces need a separate LLVM-to-
RIR justification. There is no unresolved external cryptographic call in the
linked graph; unproved execution composition must not be described as such a
primitive assumption or hidden behind whole-decoder equality.
-/

/-- info: All 17 decompression execution components use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.Execution.BlackBox.program_call,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.terminal_block,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.terminal_run,
    ``Agave.Ed25519.Encoding.Decompress.Execution.fromBytesWord_tight,
    ``Agave.Ed25519.Encoding.Decompress.Execution.fromBytesWord_value,
    ``Agave.Ed25519.Encoding.Decompress.Execution.machine_value,
    ``Agave.Ed25519.Encoding.Decompress.Execution.machine_tight,
    ``Agave.Ed25519.Encoding.Decompress.Execution.mul_call,
    ``Agave.Ed25519.Encoding.Decompress.Execution.inputWords_eq,
    ``Agave.Ed25519.Encoding.Decompress.Execution.inputWords_contract,
    ``Agave.Ed25519.Encoding.Decompress.Execution.curveD_value,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtM1_value,
    ``Agave.Ed25519.Encoding.Decompress.Execution.curveD_read,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtM1_read,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sign_byte,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sign_mask_nooverflow,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sign_mask_operation]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 17 decompression execution components use only standard Lean axioms."
