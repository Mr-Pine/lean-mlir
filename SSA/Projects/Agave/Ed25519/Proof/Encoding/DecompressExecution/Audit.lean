import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Linked
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Terminal
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Constants
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Sign
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Input
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ByteHelpersAudit
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.CutpointAudit
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow2k
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecodeWords
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.InlineWords
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.LinkedCalls
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ParseInput
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ReadyValues
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtOutput

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
  arithmetic laws; exact to_bytes serialization and byte equality are checked;
* actual rejection/tag control and the success suffix from Y/Z initialization
  through payload copy are checked, with exact overlapping caller reads;
* invocation-local initialized D/SQRT_M1 memory is explicit and frame-stable.
* the entire actual repeated-square helper, including loads, its pure loop,
  final stores and caller-frame behavior; pow22501 word schedule and field value;
* the parsed-input execution slice, scalar sign/arithmetic word laws, and the
  exact sqrt output suffix; the word decoder has the same acceptance predicate
  and field coordinates as the mathematical decoder.

This is not yet an execution proof of `linkedProgram` against `decompress`.
Outstanding: pow22501 full call execution;
sqrt_ratio_i call/serialization/comparison composition and its
conditional assignment/negation execution; decompression entry allocation and
inline vector arithmetic/sign execution; full caller-frame erasure and
composition from input through the checked X/Y/Z/T payload suffix. The existing source-formula
soundness/completeness theorem does not discharge any of these obligations.

RIR models sequential memory values. In the preserved black_box region,
`volatile_` does not add an observable event to RIR's load semantics. Alignment,
noalias promises and concurrent/volatile event traces need a separate LLVM-to-
RIR justification. There is no unresolved external cryptographic call in the
linked graph; unproved execution composition must not be described as such a
primitive assumption or hidden behind whole-decoder equality.
-/

/-- info: All 86 decompression execution components use only standard Lean axioms. -/
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
    ``Agave.Ed25519.Encoding.Decompress.Execution.sign_mask_operation,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Pow2k.body_run,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Pow2k.loop_run,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Pow2k.program_run,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Pow2k.program_call,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Pow2k.program_call_field,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Pow2k.iterateSquare_value,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Pow2k.iterateSquare_tight,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Pow22501.wordChain_value,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Pow22501.wordChain_tight,
    ``Agave.Ed25519.Encoding.Decompress.Execution.selectWord_sign,
    ``Agave.Ed25519.Encoding.Decompress.Execution.emittedNegativeWords_eq,
    ``Agave.Ed25519.Encoding.Decompress.Execution.signedWords_value,
    ``Agave.Ed25519.Encoding.Decompress.Execution.signedWords_tight,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.wordSqrt_value,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.wordSqrt_tight,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.wordDecode_acceptance,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.pointWords_value,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.numeratorMachine_eq,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.numeratorMachine_value,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.numeratorMachine_tight,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.denominatorMachine_eq,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.denominatorMachine_value,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.denominatorMachine_tight,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.parsed_resume,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Decode.parsed_readback,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Ready.curveD_read,
    ``Agave.Ed25519.Encoding.Decompress.Execution.Ready.sqrtM1_read,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.outputState_live,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.outputState_root,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.outputState_flag,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.choice_or,
    ``Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.output_run,
    ``Agave.Ed25519.Encoding.Decompress.Execution.decode_pow2k_0_73,
    ``Agave.Ed25519.Encoding.Decompress.Execution.decode_mul_0_105,
    ``Agave.Ed25519.Encoding.Decompress.Execution.decode_blackBoxByte_1_8,
    ``Agave.Ed25519.Encoding.Decompress.Execution.decode_mul_1_49,
    ``Agave.Ed25519.Encoding.Decompress.Execution.pow22501_pow2k_0_28,
    ``Agave.Ed25519.Encoding.Decompress.Execution.pow22501_pow2k_0_31,
    ``Agave.Ed25519.Encoding.Decompress.Execution.pow22501_pow2k_0_32,
    ``Agave.Ed25519.Encoding.Decompress.Execution.pow22501_mul_0_35,
    ``Agave.Ed25519.Encoding.Decompress.Execution.pow22501_mul_0_37,
    ``Agave.Ed25519.Encoding.Decompress.Execution.pow22501_pow2k_0_39,
    ``Agave.Ed25519.Encoding.Decompress.Execution.pow22501_mul_0_41,
    ``Agave.Ed25519.Encoding.Decompress.Execution.pow22501_mul_0_45,
    ``Agave.Ed25519.Encoding.Decompress.Execution.pow22501_mul_0_49,
    ``Agave.Ed25519.Encoding.Decompress.Execution.pow22501_mul_0_53,
    ``Agave.Ed25519.Encoding.Decompress.Execution.pow22501_mul_0_57,
    ``Agave.Ed25519.Encoding.Decompress.Execution.pow22501_mul_0_61,
    ``Agave.Ed25519.Encoding.Decompress.Execution.pow22501_mul_0_65,
    ``Agave.Ed25519.Encoding.Decompress.Execution.pow22501_mul_0_68,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_pow2k_0_86,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_mul_0_87,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_pow2k_0_91,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_mul_0_92,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_mul_0_95,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_mul_0_98,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_mul_0_106,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_mul_0_109,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_pow2k_0_115,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_mul_0_116,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_toBytes_0_306,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_bytesEq_0_307,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_bytesEq_0_569,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_mul_0_576,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_bytesEq_0_947,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_mul_0_953,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_blackBoxByte_0_955,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_blackBoxByte_0_1028,
    ``Agave.Ed25519.Encoding.Decompress.Execution.sqrtratio_blackBoxByte_0_1048]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 86 decompression execution components use only standard Lean axioms."
