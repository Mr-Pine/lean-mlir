import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorLoopRegisters
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorEntrySuffix

namespace Agave.Ed25519.Tables.SerialConstructorLoopRegisters
open LeanMLIR.RIR
open SerialConstructorStack (constants)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem suffix_ready (E : ⟪SerialConstructor.kernel.Γ⟫)
    (g : SerialConstructor.Globals) (slots : Slots) (table input : Pointer)
    (hc : constants (SerialConstructorEntrySuffix.suffixResult E slots table input) g =
      SerialConstructorEntrySuffix.suffixResult E slots table input) :
    Ready g slots table (SerialConstructorEntrySuffix.suffixResult E slots table input) := by
  refine ⟨hc, ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
  all_goals simp [SerialConstructorEntrySuffix.suffixResult,
    SerialConstructorEntrySuffix.suffixInput, mlir_env]

end Agave.Ed25519.Tables.SerialConstructorLoopRegisters
