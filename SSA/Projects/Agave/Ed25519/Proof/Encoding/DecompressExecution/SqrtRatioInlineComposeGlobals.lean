import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineComposeMemory

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR SerialFieldMul
open Verifier.Execution.Dalek (ReadBytes)
set_option maxRecDepth 32000

/-- The emitted initializer is exactly the five-limb payload used by the word model. -/
theorem sqrtM1_payload : sqrtM1.bytes = limbBytes sqrtM1Word.limbs := by
  rfl

/-- A local byte-read prerequisite suffices; an entire constant allocation is unnecessary. -/
theorem sqrtM1_words (s : GlobalState) (p : Pointer)
    (h : ReadBytes s p 40 sqrtM1.bytes) : readLimbs s p = sqrtM1Word.limbs :=
  readLimbs_of_limbBytes s p sqrtM1Word.limbs h.1 (h.2.trans sqrtM1_payload)

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
