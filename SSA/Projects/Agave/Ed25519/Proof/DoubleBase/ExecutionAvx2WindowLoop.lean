import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2NAF

/-! Composition through the actual AVX2 NAF word-window prefix. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2

open LeanMLIR.RIR RIR
open NAF.Memory (Buffer)
open NAF.RIR

set_option maxRecDepth 10000

def loopEnv5 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) : ⟪avx2Kernel.Γ⟫ :=
  E[%1 := .value 0#8, %2 := .value 256#64, %4 := .value 0#64,
    %5 := .value 6#64, %6 := .value 63#64, %7 := .value 59#64,
    %8 := .value 8#64, %9 := .value 31#64, %10 := .value 1#64,
    %11 := .value 15#64, %12 := .value 224#8, %13 := .value 5#64,
    %14 := .value 251#64, %258 := .value scratch,
    %269 := .value (BitVec.ofNat 64 carry.val), %270 := .value (BitVec.ofNat 64 pos.val)]

def loopEnv8 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) : ⟪avx2Kernel.Γ⟫ :=
  E[%1 := .value 0#8, %2 := .value 256#64, %4 := .value 0#64,
    %5 := .value 6#64, %6 := .value 63#64, %15 := .value 56#64,
    %8 := .value 8#64, %16 := .value 255#64, %10 := .value 1#64,
    %17 := .value 127#64, %18 := .value 248#64, %257 := .value scratch,
    %300 := .value (BitVec.ofNat 64 carry.val), %301 := .value (BitVec.ofNat 64 pos.val)]

theorem loadInput_loop5 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) (carry : Fin 2) :
    loadInput5 (loopEnv5 E scratch pos carry) scratch pos = loopEnv5 E scratch pos carry := by
  let base := loopEnv5 E scratch pos carry
  have h5 : base.read (%5) = .value 6#64 := by
    simp [base, loopEnv5, mlir_env]
  have h6 : base.read (%6) = .value 63#64 := by
    simp [base, loopEnv5, mlir_env]
  have h7 : base.read (%7) = .value 59#64 := by
    simp [base, loopEnv5, mlir_env]
  have h15 : base.read (%258) = .value scratch := by
    simp [base, loopEnv5, mlir_env]
  have h19 : base.read (%270) = .value (BitVec.ofNat 64 pos.val) := by
    simp [base, loopEnv5, mlir_env]
  change loadInput5 base scratch pos = base
  unfold loadInput5
  rw [Env.write_of_read base (%5) h5, Env.write_of_read base (%6) h6, Env.write_of_read base (%7) h7, Env.write_of_read base (%258) h15, Env.write_of_read base (%270) h19]

theorem loadInput_loop8 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) (carry : Fin 2) :
    loadInput8 (loopEnv8 E scratch pos carry) scratch pos = loopEnv8 E scratch pos carry := by
  let base := loopEnv8 E scratch pos carry
  have h5 : base.read (%5) = .value 6#64 := by
    simp [base, loopEnv8, mlir_env]
  have h6 : base.read (%6) = .value 63#64 := by
    simp [base, loopEnv8, mlir_env]
  have h7 : base.read (%15) = .value 56#64 := by
    simp [base, loopEnv8, mlir_env]
  have h13 : base.read (%257) = .value scratch := by
    simp [base, loopEnv8, mlir_env]
  have h17 : base.read (%301) = .value (BitVec.ofNat 64 pos.val) := by
    simp [base, loopEnv8, mlir_env]
  change loadInput8 base scratch pos = base
  unfold loadInput8
  rw [Env.write_of_read base (%5) h5, Env.write_of_read base (%6) h6, Env.write_of_read base (%15) h7, Env.write_of_read base (%257) h13, Env.write_of_read base (%301) h17]

theorem crossInput_load5 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    crossInput5 (loadResult5 (loopEnv5 E scratch pos carry) scratch pos bits) scratch pos
      (NAF.WordWindow.word bits (pos.val / 64) >>> (pos.val % 64)) =
      loadResult5 (loopEnv5 E scratch pos carry) scratch pos bits := by
  let base := loadResult5 (loopEnv5 E scratch pos carry) scratch pos bits
  have h4 : base.read (%4) = .value 0#64 := by
    simp [base, loadResult5, loadInput5, loopEnv5, mlir_env]
  have h6 : base.read (%6) = .value 63#64 := by
    simp [base, loadResult5, loadInput5, loopEnv5, mlir_env]
  have h8 : base.read (%8) = .value 8#64 := by
    simp [base, loadResult5, loadInput5, loopEnv5, mlir_env]
  have h19 : base.read (%270) = .value (BitVec.ofNat 64 pos.val) := by
    simp [base, loadResult5, loadInput5, loopEnv5, mlir_env]
  have h23 : base.read (%274) = .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64)))) := by
    simp [base, loadResult5, loadInput5, loopEnv5, mlir_env]
  have h25 : base.read (%276) = .value (NAF.WordWindow.word bits (pos.val / 64) >>> (pos.val % 64)) := by
    simp [base, loadResult5, loadInput5, loopEnv5, mlir_env]
  change crossInput5 base scratch pos (NAF.WordWindow.word bits (pos.val / 64) >>> (pos.val % 64)) = base
  unfold crossInput5
  rw [Env.write_of_read base (%4) h4, Env.write_of_read base (%6) h6, Env.write_of_read base (%8) h8, Env.write_of_read base (%270) h19, Env.write_of_read base (%274) h23, Env.write_of_read base (%276) h25]

theorem crossInput_load8 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    crossInput8 (loadResult8 (loopEnv8 E scratch pos carry) scratch pos bits) scratch pos
      (NAF.WordWindow.word bits (pos.val / 64) >>> (pos.val % 64)) =
      loadResult8 (loopEnv8 E scratch pos carry) scratch pos bits := by
  let base := loadResult8 (loopEnv8 E scratch pos carry) scratch pos bits
  have h4 : base.read (%4) = .value 0#64 := by
    simp [base, loadResult8, loadInput8, loopEnv8, mlir_env]
  have h6 : base.read (%6) = .value 63#64 := by
    simp [base, loadResult8, loadInput8, loopEnv8, mlir_env]
  have h8 : base.read (%8) = .value 8#64 := by
    simp [base, loadResult8, loadInput8, loopEnv8, mlir_env]
  have h17 : base.read (%301) = .value (BitVec.ofNat 64 pos.val) := by
    simp [base, loadResult8, loadInput8, loopEnv8, mlir_env]
  have h21 : base.read (%305) = .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64)))) := by
    simp [base, loadResult8, loadInput8, loopEnv8, mlir_env]
  have h23 : base.read (%307) = .value (NAF.WordWindow.word bits (pos.val / 64) >>> (pos.val % 64)) := by
    simp [base, loadResult8, loadInput8, loopEnv8, mlir_env]
  change crossInput8 base scratch pos (NAF.WordWindow.word bits (pos.val / 64) >>> (pos.val % 64)) = base
  unfold crossInput8
  rw [Env.write_of_read base (%4) h4, Env.write_of_read base (%6) h6, Env.write_of_read base (%8) h8, Env.write_of_read base (%301) h17, Env.write_of_read base (%305) h21, Env.write_of_read base (%307) h23]

def loadedEnv5 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) (carry : Fin 2)
    (bits : BitVec 320) : ⟪avx2Kernel.Γ⟫ :=
  let low := NAF.WordWindow.word bits (pos.val / 64) >>> (pos.val % 64)
  let loaded := loadResult5 (loopEnv5 E scratch pos carry) scratch pos bits
  if pos.val % 64 < 59 then loaded[%283 := .value low]
  else
    (crossResult5 loaded scratch pos low bits)[%283 :=
      .value ((NAF.WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)) ||| low)]

def loadedEnv8 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) (carry : Fin 2)
    (bits : BitVec 320) : ⟪avx2Kernel.Γ⟫ :=
  let low := NAF.WordWindow.word bits (pos.val / 64) >>> (pos.val % 64)
  let loaded := loadResult8 (loopEnv8 E scratch pos carry) scratch pos bits
  if pos.val % 64 < 56 then loaded[%314 := .value low]
  else
    (crossResult8 loaded scratch pos low bits)[%314 :=
      .value ((NAF.WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)) ||| low)]

/-- Actual execution through either one or two word loads reaches the same
window block, with the original compiler register values on both paths. -/
theorem avx2_naf5_load_window_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits) :
    (avx2Kernel p g).runFrom (loopEnv5 E scratch pos carry) 2 s =
      (avx2Kernel p g).runFrom (loadedEnv5 E scratch pos carry bits) 4 s := by
  have hload := load5_block (loopEnv5 E scratch pos carry) scratch pos bits s hbuffer hbits
  rw [loadInput_loop5] at hload
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 2 = avx2Kernel.bb2 from rfl, hload]
  by_cases hshort : pos.val % 64 < 59
  · simp only [hshort, ite_true, PoisonOr.value_bind, Func.continue, loadedEnv5]
  · simp only [hshort, ite_false, PoisonOr.value_bind, Func.continue]
    conv_lhs => rw [← crossInput_load5 E scratch pos carry bits]
    rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 3 = avx2Kernel.bb3 from rfl,
      cross5_block _ scratch pos _ bits s hbuffer hbits hshort]
    simp only [PoisonOr.value_bind, Func.continue, loadedEnv5, hshort, ite_false]

theorem avx2_naf8_load_window_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits) :
    (avx2Kernel p g).runFrom (loopEnv8 E scratch pos carry) 9 s =
      (avx2Kernel p g).runFrom (loadedEnv8 E scratch pos carry bits) 11 s := by
  have hload := load8_block (loopEnv8 E scratch pos carry) scratch pos bits s hbuffer hbits
  rw [loadInput_loop8] at hload
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 9 = avx2Kernel.bb9 from rfl, hload]
  by_cases hshort : pos.val % 64 < 56
  · simp only [hshort, ite_true, PoisonOr.value_bind, Func.continue, loadedEnv8]
  · simp only [hshort, ite_false, PoisonOr.value_bind, Func.continue]
    conv_lhs => rw [← crossInput_load8 E scratch pos carry bits]
    rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 10 = avx2Kernel.bb10 from rfl,
      cross8_block _ scratch pos _ bits s hbuffer hbits hshort]
    simp only [PoisonOr.value_bind, Func.continue, loadedEnv8, hshort, ite_false]

theorem windowInput_loaded5 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    windowInput5 (loadedEnv5 E scratch pos carry bits) (NAF.WordWindow.rawWindow bits pos.val 5) carry =
      loadedEnv5 E scratch pos carry bits := by
  unfold windowInput5
  repeat' (first | rfl | apply Env.write_eq_of)
  all_goals
    simp only [loadedEnv5, NAF.WordWindow.rawWindow]
    split_ifs <;> simp_all [loadResult5, loadInput5, loopEnv5, crossResult5,
      crossInput5, mlir_env, BitVec.or_comm]

theorem windowInput_loaded8 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    windowInput8 (loadedEnv8 E scratch pos carry bits) (NAF.WordWindow.rawWindow bits pos.val 8) carry =
      loadedEnv8 E scratch pos carry bits := by
  unfold windowInput8
  repeat' (first | rfl | apply Env.write_eq_of)
  all_goals
    simp only [loadedEnv8, NAF.WordWindow.rawWindow]
    split_ifs <;> simp_all [loadResult8, loadInput8, loopEnv8, crossResult8,
      crossInput8, mlir_env, BitVec.or_comm]

def controlEnv5 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) (carry : Fin 2)
    (bits : BitVec 320) : ⟪avx2Kernel.Γ⟫ :=
  windowResult5 (loadedEnv5 E scratch pos carry bits) (NAF.WordWindow.rawWindow bits pos.val 5) carry

def controlEnv8 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) (carry : Fin 2)
    (bits : BitVec 320) : ⟪avx2Kernel.Γ⟫ :=
  windowResult8 (loadedEnv8 E scratch pos carry bits) (NAF.WordWindow.rawWindow bits pos.val 8) carry

/-- The original load/cross-word/mask/carry/parity CFG prefix, with its exact
successor. Scratch bounds and the one-bit loop carry derive every operation's
definedness; no successful-execution premise is present. -/
theorem avx2_naf5_read_window_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits) :
    (avx2Kernel p g).runFrom (loopEnv5 E scratch pos carry) 2 s =
      (avx2Kernel p g).runFrom (controlEnv5 E scratch pos carry bits)
        (if (sum5 (mask5 (NAF.WordWindow.rawWindow bits pos.val 5)) carry).val % 2 = 0 then 5 else 6) s := by
  rw [avx2_naf5_load_window_run p g E scratch pos carry bits s hbuffer hbits]
  have hwindow := window5_block (loadedEnv5 E scratch pos carry bits)
    (NAF.WordWindow.rawWindow bits pos.val 5) carry s
  rw [windowInput_loaded5] at hwindow
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 4 = avx2Kernel.bb4 from rfl, hwindow]
  rfl

theorem avx2_naf8_read_window_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits) :
    (avx2Kernel p g).runFrom (loopEnv8 E scratch pos carry) 9 s =
      (avx2Kernel p g).runFrom (controlEnv8 E scratch pos carry bits)
        (if (sum8 (mask8 (NAF.WordWindow.rawWindow bits pos.val 8)) carry).val % 2 = 0 then 12 else 13) s := by
  rw [avx2_naf8_load_window_run p g E scratch pos carry bits s hbuffer hbits]
  have hwindow := window8_block (loadedEnv8 E scratch pos carry bits)
    (NAF.WordWindow.rawWindow bits pos.val 8) carry s
  rw [windowInput_loaded8] at hwindow
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 11 = avx2Kernel.bb11 from rfl, hwindow]
  rfl


end Agave.Ed25519.DoubleBase.ExecutionAvx2
