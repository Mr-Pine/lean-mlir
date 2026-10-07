import SSA.Projects.Agave.Ed25519.Proof.NAF.Initialization
import SSA.Projects.Agave.Ed25519.Proof.NAF.Carry
import SSA.Projects.Agave.Ed25519.Proof.NAF.StoreLoop

/-!
# Composition of the imported NAF loop

The entry block establishes these persistent registers. Each equation below
executes the original RIR blocks: no block result is a hypothesis. The live
scratch object supplies its word loads and flagged interior addresses.
-/
namespace Agave.Ed25519.NAF.RIR

open LeanMLIR.RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000

def loopEnv5 (E : ⟪kernel5.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) : ⟪kernel5.Γ⟫ :=
  E[%1 := .value 0#8, %2 := .value 256#64, %4 := .value 0#64,
    %5 := .value 6#64, %6 := .value 63#64, %7 := .value 59#64,
    %8 := .value 8#64, %9 := .value 31#64, %10 := .value 1#64,
    %11 := .value 15#64, %12 := .value 224#8, %13 := .value 5#64,
    %14 := .value 251#64, %15 := .value scratch,
    %18 := .value (BitVec.ofNat 64 carry.val), %19 := .value (BitVec.ofNat 64 pos.val)]

def loopEnv8 (E : ⟪kernel8.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) : ⟪kernel8.Γ⟫ :=
  E[%1 := .value 0#8, %2 := .value 256#64, %4 := .value 0#64,
    %5 := .value 6#64, %6 := .value 63#64, %7 := .value 56#64,
    %8 := .value 8#64, %9 := .value 255#64, %10 := .value 1#64,
    %11 := .value 127#64, %12 := .value 248#64, %13 := .value scratch,
    %16 := .value (BitVec.ofNat 64 carry.val), %17 := .value (BitVec.ofNat 64 pos.val)]

theorem loadInput_loop5 (E : ⟪kernel5.Γ⟫) (scratch : Pointer) (pos : Fin 256) (carry : Fin 2) :
    loadInput5 (loopEnv5 E scratch pos carry) scratch pos = loopEnv5 E scratch pos carry := by
  let base := loopEnv5 E scratch pos carry
  have h5 : base.read (%5) = .value 6#64 := by
    simp [base, loopEnv5, mlir_env]
  have h6 : base.read (%6) = .value 63#64 := by
    simp [base, loopEnv5, mlir_env]
  have h7 : base.read (%7) = .value 59#64 := by
    simp [base, loopEnv5, mlir_env]
  have h15 : base.read (%15) = .value scratch := by
    simp [base, loopEnv5, mlir_env]
  have h19 : base.read (%19) = .value (BitVec.ofNat 64 pos.val) := by
    simp [base, loopEnv5, mlir_env]
  change loadInput5 base scratch pos = base
  unfold loadInput5
  rw [Env.write_of_read base (%5) h5, Env.write_of_read base (%6) h6, Env.write_of_read base (%7) h7, Env.write_of_read base (%15) h15, Env.write_of_read base (%19) h19]

theorem loadInput_loop8 (E : ⟪kernel8.Γ⟫) (scratch : Pointer) (pos : Fin 256) (carry : Fin 2) :
    loadInput8 (loopEnv8 E scratch pos carry) scratch pos = loopEnv8 E scratch pos carry := by
  let base := loopEnv8 E scratch pos carry
  have h5 : base.read (%5) = .value 6#64 := by
    simp [base, loopEnv8, mlir_env]
  have h6 : base.read (%6) = .value 63#64 := by
    simp [base, loopEnv8, mlir_env]
  have h7 : base.read (%7) = .value 56#64 := by
    simp [base, loopEnv8, mlir_env]
  have h13 : base.read (%13) = .value scratch := by
    simp [base, loopEnv8, mlir_env]
  have h17 : base.read (%17) = .value (BitVec.ofNat 64 pos.val) := by
    simp [base, loopEnv8, mlir_env]
  change loadInput8 base scratch pos = base
  unfold loadInput8
  rw [Env.write_of_read base (%5) h5, Env.write_of_read base (%6) h6, Env.write_of_read base (%7) h7, Env.write_of_read base (%13) h13, Env.write_of_read base (%17) h17]

theorem crossInput_load5 (E : ⟪kernel5.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    crossInput5 (loadResult5 (loopEnv5 E scratch pos carry) scratch pos bits) scratch pos
      (WordWindow.word bits (pos.val / 64) >>> (pos.val % 64)) =
      loadResult5 (loopEnv5 E scratch pos carry) scratch pos bits := by
  let base := loadResult5 (loopEnv5 E scratch pos carry) scratch pos bits
  have h4 : base.read (%4) = .value 0#64 := by
    simp [base, loadResult5, loadInput5, loopEnv5, mlir_env]
  have h6 : base.read (%6) = .value 63#64 := by
    simp [base, loadResult5, loadInput5, loopEnv5, mlir_env]
  have h8 : base.read (%8) = .value 8#64 := by
    simp [base, loadResult5, loadInput5, loopEnv5, mlir_env]
  have h19 : base.read (%19) = .value (BitVec.ofNat 64 pos.val) := by
    simp [base, loadResult5, loadInput5, loopEnv5, mlir_env]
  have h23 : base.read (%23) = .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64)))) := by
    simp [base, loadResult5, loadInput5, loopEnv5, mlir_env]
  have h25 : base.read (%25) = .value (WordWindow.word bits (pos.val / 64) >>> (pos.val % 64)) := by
    simp [base, loadResult5, loadInput5, loopEnv5, mlir_env]
  change crossInput5 base scratch pos (WordWindow.word bits (pos.val / 64) >>> (pos.val % 64)) = base
  unfold crossInput5
  rw [Env.write_of_read base (%4) h4, Env.write_of_read base (%6) h6, Env.write_of_read base (%8) h8, Env.write_of_read base (%19) h19, Env.write_of_read base (%23) h23, Env.write_of_read base (%25) h25]

theorem crossInput_load8 (E : ⟪kernel8.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    crossInput8 (loadResult8 (loopEnv8 E scratch pos carry) scratch pos bits) scratch pos
      (WordWindow.word bits (pos.val / 64) >>> (pos.val % 64)) =
      loadResult8 (loopEnv8 E scratch pos carry) scratch pos bits := by
  let base := loadResult8 (loopEnv8 E scratch pos carry) scratch pos bits
  have h4 : base.read (%4) = .value 0#64 := by
    simp [base, loadResult8, loadInput8, loopEnv8, mlir_env]
  have h6 : base.read (%6) = .value 63#64 := by
    simp [base, loadResult8, loadInput8, loopEnv8, mlir_env]
  have h8 : base.read (%8) = .value 8#64 := by
    simp [base, loadResult8, loadInput8, loopEnv8, mlir_env]
  have h17 : base.read (%17) = .value (BitVec.ofNat 64 pos.val) := by
    simp [base, loadResult8, loadInput8, loopEnv8, mlir_env]
  have h21 : base.read (%21) = .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64)))) := by
    simp [base, loadResult8, loadInput8, loopEnv8, mlir_env]
  have h23 : base.read (%23) = .value (WordWindow.word bits (pos.val / 64) >>> (pos.val % 64)) := by
    simp [base, loadResult8, loadInput8, loopEnv8, mlir_env]
  change crossInput8 base scratch pos (WordWindow.word bits (pos.val / 64) >>> (pos.val % 64)) = base
  unfold crossInput8
  rw [Env.write_of_read base (%4) h4, Env.write_of_read base (%6) h6, Env.write_of_read base (%8) h8, Env.write_of_read base (%17) h17, Env.write_of_read base (%21) h21, Env.write_of_read base (%23) h23]

def loadedEnv5 (E : ⟪kernel5.Γ⟫) (scratch : Pointer) (pos : Fin 256) (carry : Fin 2)
    (bits : BitVec 320) : ⟪kernel5.Γ⟫ :=
  let low := WordWindow.word bits (pos.val / 64) >>> (pos.val % 64)
  let loaded := loadResult5 (loopEnv5 E scratch pos carry) scratch pos bits
  if pos.val % 64 < 59 then loaded[%32 := .value low]
  else
    (crossResult5 loaded scratch pos low bits)[%32 :=
      .value ((WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)) ||| low)]

def loadedEnv8 (E : ⟪kernel8.Γ⟫) (scratch : Pointer) (pos : Fin 256) (carry : Fin 2)
    (bits : BitVec 320) : ⟪kernel8.Γ⟫ :=
  let low := WordWindow.word bits (pos.val / 64) >>> (pos.val % 64)
  let loaded := loadResult8 (loopEnv8 E scratch pos carry) scratch pos bits
  if pos.val % 64 < 56 then loaded[%30 := .value low]
  else
    (crossResult8 loaded scratch pos low bits)[%30 :=
      .value ((WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)) ||| low)]

/-- Actual execution through either one or two word loads reaches the same
window block, with the original compiler register values on both paths. -/
theorem kernel5_load_window_run (E : ⟪kernel5.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits) :
    kernel5.runFrom (loopEnv5 E scratch pos carry) 2 s =
      kernel5.runFrom (loadedEnv5 E scratch pos carry bits) 4 s := by
  have hload := kernel5_load_block (loopEnv5 E scratch pos carry) scratch pos bits s hbuffer hbits
  rw [loadInput_loop5] at hload
  rw [Func.runFrom_eq, show kernel5.blocks 2 = kernel5.bb2 from rfl, hload]
  by_cases hshort : pos.val % 64 < 59
  · simp only [hshort, ite_true, PoisonOr.value_bind, Func.continue, loadedEnv5]
  · simp only [hshort, ite_false, PoisonOr.value_bind, Func.continue]
    conv_lhs => rw [← crossInput_load5 E scratch pos carry bits]
    rw [Func.runFrom_eq, show kernel5.blocks 3 = kernel5.bb3 from rfl,
      kernel5_cross_block _ scratch pos _ bits s hbuffer hbits hshort]
    simp only [PoisonOr.value_bind, Func.continue, loadedEnv5, hshort, ite_false]

theorem kernel8_load_window_run (E : ⟪kernel8.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits) :
    kernel8.runFrom (loopEnv8 E scratch pos carry) 2 s =
      kernel8.runFrom (loadedEnv8 E scratch pos carry bits) 4 s := by
  have hload := kernel8_load_block (loopEnv8 E scratch pos carry) scratch pos bits s hbuffer hbits
  rw [loadInput_loop8] at hload
  rw [Func.runFrom_eq, show kernel8.blocks 2 = kernel8.bb2 from rfl, hload]
  by_cases hshort : pos.val % 64 < 56
  · simp only [hshort, ite_true, PoisonOr.value_bind, Func.continue, loadedEnv8]
  · simp only [hshort, ite_false, PoisonOr.value_bind, Func.continue]
    conv_lhs => rw [← crossInput_load8 E scratch pos carry bits]
    rw [Func.runFrom_eq, show kernel8.blocks 3 = kernel8.bb3 from rfl,
      kernel8_cross_block _ scratch pos _ bits s hbuffer hbits hshort]
    simp only [PoisonOr.value_bind, Func.continue, loadedEnv8, hshort, ite_false]

theorem windowInput_loaded5 (E : ⟪kernel5.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    windowInput5 (loadedEnv5 E scratch pos carry bits) (WordWindow.rawWindow bits pos.val 5) carry =
      loadedEnv5 E scratch pos carry bits := by
  let base := loadedEnv5 E scratch pos carry bits
  have h4 : base.read (%4) = .value 0#64 := by
    dsimp only [base, loadedEnv5, WordWindow.rawWindow]
    split_ifs <;> simp_all [loadResult5, loadInput5, loopEnv5, crossResult5, crossInput5, mlir_env, BitVec.or_comm]
  have h9 : base.read (%9) = .value 31#64 := by
    dsimp only [base, loadedEnv5, WordWindow.rawWindow]
    split_ifs <;> simp_all [loadResult5, loadInput5, loopEnv5, crossResult5, crossInput5, mlir_env, BitVec.or_comm]
  have h10 : base.read (%10) = .value 1#64 := by
    dsimp only [base, loadedEnv5, WordWindow.rawWindow]
    split_ifs <;> simp_all [loadResult5, loadInput5, loopEnv5, crossResult5, crossInput5, mlir_env, BitVec.or_comm]
  have h18 : base.read (%18) = .value (BitVec.ofNat 64 carry.val) := by
    dsimp only [base, loadedEnv5, WordWindow.rawWindow]
    split_ifs <;> simp_all [loadResult5, loadInput5, loopEnv5, crossResult5, crossInput5, mlir_env, BitVec.or_comm]
  have h32 : base.read (%32) = .value (WordWindow.rawWindow bits pos.val 5) := by
    dsimp only [base, loadedEnv5, WordWindow.rawWindow]
    split_ifs <;> simp_all [loadResult5, loadInput5, loopEnv5, crossResult5, crossInput5, mlir_env, BitVec.or_comm]
  change windowInput5 base (WordWindow.rawWindow bits pos.val 5) carry = base
  unfold windowInput5
  rw [Env.write_of_read base (%4) h4, Env.write_of_read base (%9) h9, Env.write_of_read base (%10) h10, Env.write_of_read base (%18) h18, Env.write_of_read base (%32) h32]

theorem windowInput_loaded8 (E : ⟪kernel8.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    windowInput8 (loadedEnv8 E scratch pos carry bits) (WordWindow.rawWindow bits pos.val 8) carry =
      loadedEnv8 E scratch pos carry bits := by
  let base := loadedEnv8 E scratch pos carry bits
  have h4 : base.read (%4) = .value 0#64 := by
    dsimp only [base, loadedEnv8, WordWindow.rawWindow]
    split_ifs <;> simp_all [loadResult8, loadInput8, loopEnv8, crossResult8, crossInput8, mlir_env, BitVec.or_comm]
  have h9 : base.read (%9) = .value 255#64 := by
    dsimp only [base, loadedEnv8, WordWindow.rawWindow]
    split_ifs <;> simp_all [loadResult8, loadInput8, loopEnv8, crossResult8, crossInput8, mlir_env, BitVec.or_comm]
  have h10 : base.read (%10) = .value 1#64 := by
    dsimp only [base, loadedEnv8, WordWindow.rawWindow]
    split_ifs <;> simp_all [loadResult8, loadInput8, loopEnv8, crossResult8, crossInput8, mlir_env, BitVec.or_comm]
  have h16 : base.read (%16) = .value (BitVec.ofNat 64 carry.val) := by
    dsimp only [base, loadedEnv8, WordWindow.rawWindow]
    split_ifs <;> simp_all [loadResult8, loadInput8, loopEnv8, crossResult8, crossInput8, mlir_env, BitVec.or_comm]
  have h30 : base.read (%30) = .value (WordWindow.rawWindow bits pos.val 8) := by
    dsimp only [base, loadedEnv8, WordWindow.rawWindow]
    split_ifs <;> simp_all [loadResult8, loadInput8, loopEnv8, crossResult8, crossInput8, mlir_env, BitVec.or_comm]
  change windowInput8 base (WordWindow.rawWindow bits pos.val 8) carry = base
  unfold windowInput8
  rw [Env.write_of_read base (%4) h4, Env.write_of_read base (%9) h9, Env.write_of_read base (%10) h10, Env.write_of_read base (%16) h16, Env.write_of_read base (%30) h30]

def controlEnv5 (E : ⟪kernel5.Γ⟫) (scratch : Pointer) (pos : Fin 256) (carry : Fin 2)
    (bits : BitVec 320) : ⟪kernel5.Γ⟫ :=
  windowResult5 (loadedEnv5 E scratch pos carry bits) (WordWindow.rawWindow bits pos.val 5) carry

def controlEnv8 (E : ⟪kernel8.Γ⟫) (scratch : Pointer) (pos : Fin 256) (carry : Fin 2)
    (bits : BitVec 320) : ⟪kernel8.Γ⟫ :=
  windowResult8 (loadedEnv8 E scratch pos carry bits) (WordWindow.rawWindow bits pos.val 8) carry

/-- The original load/cross-word/mask/carry/parity CFG prefix, with its exact
successor. Scratch bounds and the one-bit loop carry derive every operation's
definedness; no successful-execution premise is present. -/
theorem kernel5_read_window_run (E : ⟪kernel5.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits) :
    kernel5.runFrom (loopEnv5 E scratch pos carry) 2 s =
      kernel5.runFrom (controlEnv5 E scratch pos carry bits)
        (if (sum5 (mask5 (WordWindow.rawWindow bits pos.val 5)) carry).val % 2 = 0 then 5 else 6) s := by
  rw [kernel5_load_window_run E scratch pos carry bits s hbuffer hbits]
  have hwindow := kernel5_window_block (loadedEnv5 E scratch pos carry bits)
    (WordWindow.rawWindow bits pos.val 5) carry s
  rw [windowInput_loaded5] at hwindow
  rw [Func.runFrom_eq, show kernel5.blocks 4 = kernel5.bb4 from rfl, hwindow]
  rfl

theorem kernel8_read_window_run (E : ⟪kernel8.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits) :
    kernel8.runFrom (loopEnv8 E scratch pos carry) 2 s =
      kernel8.runFrom (controlEnv8 E scratch pos carry bits)
        (if (sum8 (mask8 (WordWindow.rawWindow bits pos.val 8)) carry).val % 2 = 0 then 5 else 6) s := by
  rw [kernel8_load_window_run E scratch pos carry bits s hbuffer hbits]
  have hwindow := kernel8_window_block (loadedEnv8 E scratch pos carry bits)
    (WordWindow.rawWindow bits pos.val 8) carry s
  rw [windowInput_loaded8] at hwindow
  rw [Func.runFrom_eq, show kernel8.blocks 4 = kernel8.bb4 from rfl, hwindow]
  rfl

end Agave.Ed25519.NAF.RIR
