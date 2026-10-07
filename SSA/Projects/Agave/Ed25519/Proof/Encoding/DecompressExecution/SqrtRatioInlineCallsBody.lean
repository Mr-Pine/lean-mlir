import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineCallsWords

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

structure ArithmeticCalls (s : GlobalState) (u v : Pointer) (t : Nat → GlobalState) : Prop where
  c0 : sqrtRatioPrimitives.pow2k (.cons (.value (slot s 20)) (.cons (.value v) (.cons (.value 1#32) .nil))) (t 0) = .value (.nil,t 1)
  c1 : sqrtRatioPrimitives.mul (.cons (.value (slot s 21)) (.cons (.value (slot s 20)) (.cons (.value v) .nil))) (t 1) = .value (.nil,t 2)
  c2 : sqrtRatioPrimitives.pow2k (.cons (.value (slot s 18)) (.cons (.value (slot s 21)) (.cons (.value 1#32) .nil))) (t 2) = .value (.nil,t 3)
  c3 : sqrtRatioPrimitives.mul (.cons (.value (slot s 19)) (.cons (.value (slot s 18)) (.cons (.value v) .nil))) (t 3) = .value (.nil,t 4)
  c4 : sqrtRatioPrimitives.mul (.cons (.value (slot s 16)) (.cons (.value u) (.cons (.value (slot s 21)) .nil))) (t 4) = .value (.nil,t 5)
  c5 : sqrtRatioPrimitives.mul (.cons (.value (slot s 14)) (.cons (.value u) (.cons (.value (slot s 19)) .nil))) (t 5) = .value (.nil,t 6)
  c6 : sqrtRatioPrimitives.pow22501 (.cons (.value (slot s 7)) (.cons (.value (slot s 14)) .nil)) (t 6) = .value (.nil,t 7)
  c7 : ∀ (E : Env program.Γ), Operation.memcpy (.value (slot s 8)) (.value (slot s 7)) (.value 40#64) E (t 7) = .value (E,t 8)
  c8 : sqrtRatioPrimitives.pow2k (.cons (.value (slot s 6)) (.cons (.value (slot s 8)) (.cons (.value 2#32) .nil))) (t 8) = .value (.nil,t 9)
  c9 : sqrtRatioPrimitives.mul (.cons (.value (slot s 15)) (.cons (.value (slot s 14)) (.cons (.value (slot s 6)) .nil))) (t 9) = .value (.nil,t 10)
  c10 : sqrtRatioPrimitives.mul (.cons (.value (slot s 17)) (.cons (.value (slot s 16)) (.cons (.value (slot s 15)) .nil))) (t 10) = .value (.nil,t 11)
  c11 : sqrtRatioPrimitives.pow2k (.cons (.value (slot s 12)) (.cons (.value (slot s 17)) (.cons (.value 1#32) .nil))) (t 11) = .value (.nil,t 12)
  c12 : sqrtRatioPrimitives.mul (.cons (.value (slot s 13)) (.cons (.value v) (.cons (.value (slot s 12)) .nil))) (t 12) = .value (.nil,t 13)

/-- Execute all actual calls and intervening lifetime markers, through pc116. -/
theorem arithmetic_calls_segment (g : Globals) (s : GlobalState) (u v : Pointer)
    (E : Env program.Γ) (t : Nat → GlobalState)
    (hslots : ∀ i : Fin 22, E.read (slotRegister i) = .value (slot s i))
    (hu : E.read (%arg1) = .value u) (hv : E.read (%arg2) = .value v)
    (h0 : E.read (%0) = .value 1#32) (h1 : E.read (%1) = .value 40#64)
    (h2 : E.read (%2) = .value 2#32) (hc : ArithmeticCalls s u v t) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 86 31 E (t 0) =
      .value (E,t 13) := by
  have huargs : E.args 1 = .value u := hu
  have hvargs : E.args 2 = .value v := hv
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12⟩ := hc
  have e68 : E.read (%68) = .value (slot s 6) := hslots 6
  have e69 : E.read (%69) = .value (slot s 7) := hslots 7
  have e70 : E.read (%70) = .value (slot s 8) := hslots 8
  have e71 : E.read (%71) = .value (slot s 9) := hslots 9
  have e72 : E.read (%72) = .value (slot s 10) := hslots 10
  have e73 : E.read (%73) = .value (slot s 11) := hslots 11
  have e74 : E.read (%74) = .value (slot s 12) := hslots 12
  have e75 : E.read (%75) = .value (slot s 13) := hslots 13
  have e76 : E.read (%76) = .value (slot s 14) := hslots 14
  have e77 : E.read (%77) = .value (slot s 15) := hslots 15
  have e78 : E.read (%78) = .value (slot s 16) := hslots 16
  have e79 : E.read (%79) = .value (slot s 17) := hslots 17
  have e80 : E.read (%80) = .value (slot s 18) := hslots 18
  have e81 : E.read (%81) = .value (slot s 19) := hslots 19
  have e82 : E.read (%82) = .value (slot s 20) := hslots 20
  have e83 : E.read (%83) = .value (slot s 21) := hslots 21
  change List.foldlM Instr.run E (((program.entry sqrtRatioPrimitives g).body.drop 86).take 31) (t 0) = _
  dsimp only [program.entry,List.drop,List.take]
  simp only [List.foldlM_cons,List.foldlM_nil,Instr.run,EffectM.bind_eq,
    EffectM.pure_eq,PoisonOr.value_bind,Env.writeMany_nil,mlir_effect,mlir_env,hu,hv,huargs,hvargs,h0,h1,h2,
    e68,e69,e70,e71,e72,e73,e74,e75,e76,e77,e78,e79,e80,e81,e82,e83,
    c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
