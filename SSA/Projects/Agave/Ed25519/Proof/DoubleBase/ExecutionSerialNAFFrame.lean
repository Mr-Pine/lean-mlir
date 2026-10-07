import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialIteration

/-! Exact register frame of each NAF loop. Every argument and every register
before its compiler-assigned loop temporaries is retained. In particular this
preserves all global addresses, constants, scratch pointers and digit-array
pointers needed by the other emitter, table setup, point loop and final store. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR NAF NAF.RIR
set_option maxRecDepth 10000

theorem loadedEnv5_frame (E : ⟪serialKernel.Γ⟫) (scratch : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    PrefixEq (loopEnv5 E scratch pos carry)
      (loadedEnv5 E scratch pos carry bits) 43 := by
  unfold loadedEnv5
  split_ifs
  · unfold loadResult5
    rw [loadInput_loop5]
    iterate 7 apply PrefixEq.write (hi := by decide)
    exact PrefixEq.refl _ _
  · unfold crossResult5
    dsimp only
    rw [crossInput_load5]
    unfold loadResult5
    rw [loadInput_loop5]
    iterate 13 apply PrefixEq.write (hi := by decide)
    exact PrefixEq.refl _ _

theorem controlEnv5_frame (E : ⟪serialKernel.Γ⟫) (scratch : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    PrefixEq (loopEnv5 E scratch pos carry)
      (controlEnv5 E scratch pos carry bits) 43 := by
  unfold controlEnv5 windowResult5
  rw [windowInput_loaded5]
  iterate 4 apply PrefixEq.write (hi := by decide)
  exact loadedEnv5_frame E scratch pos carry bits

theorem evenExitEnv5_frame (E : ⟪serialKernel.Γ⟫) (scratch : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    PrefixEq (loopEnv5 E scratch pos carry)
      (evenResult5 (controlEnv5 E scratch pos carry bits) pos) 43 := by
  unfold evenResult5
  rw [evenInput_control5]
  iterate 2 apply PrefixEq.write (hi := by decide)
  exact controlEnv5_frame E scratch pos carry bits

theorem oddExitEnv5_frame (E : ⟪serialKernel.Γ⟫) (scratch out : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    PrefixEq (loopEnv5 E scratch pos carry)
      (storeResult5 (controlEnv5 E scratch pos carry bits) out pos
        (sum5 (mask5 (WordWindow.rawWindow bits pos.val 5)) carry)) 43 := by
  unfold storeResult5
  rw [storeInput_control5]
  iterate 8 apply PrefixEq.write (hi := by decide)
  exact controlEnv5_frame E scratch pos carry bits

theorem evenNextEnv5_frame (E : ⟪serialKernel.Γ⟫) (scratch : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    PrefixEq (loopEnv5 E scratch pos carry)
      (evenNextEnv5 E scratch pos carry bits) 43 := by
  unfold evenNextEnv5
  apply PrefixEq.write (hi := by decide)
  exact evenExitEnv5_frame E scratch pos carry bits

theorem oddNextEnv5_frame (E : ⟪serialKernel.Γ⟫) (scratch out : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    PrefixEq (loopEnv5 E scratch pos carry)
      (oddNextEnv5 E scratch out pos carry bits) 43 := by
  unfold oddNextEnv5
  iterate 3 apply PrefixEq.write (hi := by decide)
  exact oddExitEnv5_frame E scratch out pos carry bits

theorem loadedEnv8_frame (E : ⟪serialKernel.Γ⟫) (scratch : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    PrefixEq (loopEnv8 E scratch pos carry)
      (loadedEnv8 E scratch pos carry bits) 74 := by
  unfold loadedEnv8
  split_ifs
  · unfold loadResult8
    rw [loadInput_loop8]
    iterate 7 apply PrefixEq.write (hi := by decide)
    exact PrefixEq.refl _ _
  · unfold crossResult8
    dsimp only
    rw [crossInput_load8]
    unfold loadResult8
    rw [loadInput_loop8]
    iterate 13 apply PrefixEq.write (hi := by decide)
    exact PrefixEq.refl _ _

theorem controlEnv8_frame (E : ⟪serialKernel.Γ⟫) (scratch : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    PrefixEq (loopEnv8 E scratch pos carry)
      (controlEnv8 E scratch pos carry bits) 74 := by
  unfold controlEnv8 windowResult8
  rw [windowInput_loaded8]
  iterate 4 apply PrefixEq.write (hi := by decide)
  exact loadedEnv8_frame E scratch pos carry bits

theorem evenExitEnv8_frame (E : ⟪serialKernel.Γ⟫) (scratch : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    PrefixEq (loopEnv8 E scratch pos carry)
      (evenResult8 (controlEnv8 E scratch pos carry bits) pos) 74 := by
  unfold evenResult8
  rw [evenInput_control8]
  iterate 2 apply PrefixEq.write (hi := by decide)
  exact controlEnv8_frame E scratch pos carry bits

theorem oddExitEnv8_frame (E : ⟪serialKernel.Γ⟫) (scratch out : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    PrefixEq (loopEnv8 E scratch pos carry)
      (storeResult8 (controlEnv8 E scratch pos carry bits) out pos
        (sum8 (mask8 (WordWindow.rawWindow bits pos.val 8)) carry)) 74 := by
  unfold storeResult8
  rw [storeInput_control8]
  iterate 6 apply PrefixEq.write (hi := by decide)
  exact controlEnv8_frame E scratch pos carry bits

theorem evenNextEnv8_frame (E : ⟪serialKernel.Γ⟫) (scratch : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    PrefixEq (loopEnv8 E scratch pos carry)
      (evenNextEnv8 E scratch pos carry bits) 74 := by
  unfold evenNextEnv8
  apply PrefixEq.write (hi := by decide)
  exact evenExitEnv8_frame E scratch pos carry bits

theorem oddNextEnv8_frame (E : ⟪serialKernel.Γ⟫) (scratch out : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    PrefixEq (loopEnv8 E scratch pos carry)
      (oddNextEnv8 E scratch out pos carry bits) 74 := by
  unfold oddNextEnv8
  iterate 3 apply PrefixEq.write (hi := by decide)
  exact oddExitEnv8_frame E scratch out pos carry bits

end Agave.Ed25519.DoubleBase.RIR
