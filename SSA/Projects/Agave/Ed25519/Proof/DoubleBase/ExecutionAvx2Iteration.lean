import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2WindowLoop

/-! One full iteration of each inlined AVX2 NAF loop. The final branch remains
an invocation of the real successor (7 or 14); no synthetic return replaces it. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR NAF NAF.RIR
open NAF.Memory (Buffer)
set_option maxRecDepth 10000

theorem store5_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (out : Pointer) (pos : Fin 256) (window : Fin 33)
    (s : GlobalState) (hbuffer : Buffer s.mem out 256)
    (hout : E.read (%266) = .value out) :
    (avx2Kernel p g).runFrom (storeInput5 E pos window) 6 s =
      if pos.val < 251 then (avx2Kernel p g).runFrom
        ((storeResult5 E out pos window)[%268 := .value (BitVec.ofNat 64 (pos.val + 5)), %269 := .value (carry5 window)]) 1
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte5 window)}
      else (avx2Kernel p g).runFrom (storeResult5 E out pos window) 7
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte5 window)} := by
  have hblock : (avx2Kernel p g).blocks 6 = avx2Kernel.bb6 := rfl
  rw [Func.runFrom_eq, hblock, store5_block E out pos window s hbuffer hout]
  by_cases hnext : pos.val < 251 <;>
    simp only [hnext, ite_true, ite_false, PoisonOr.value_bind, Func.continue]

theorem store8_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (out : Pointer) (pos : Fin 256) (window : Fin 257)
    (s : GlobalState) (hbuffer : Buffer s.mem out 256)
    (hout : E.read (%265) = .value out) :
    (avx2Kernel p g).runFrom (storeInput8 E pos window) 13 s =
      if pos.val < 248 then (avx2Kernel p g).runFrom
        ((storeResult8 E out pos window)[%299 := .value (BitVec.ofNat 64 (pos.val + 8)), %300 := .value (carry8 window)]) 8
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)}
      else (avx2Kernel p g).runFrom (storeResult8 E out pos window) 14
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)} := by
  have hblock : (avx2Kernel p g).blocks 13 = avx2Kernel.bb13 := rfl
  rw [Func.runFrom_eq, hblock, store8_block E out pos window s hbuffer hout]
  by_cases hnext : pos.val < 248 <;>
    simp only [hnext, ite_true, ite_false, PoisonOr.value_bind, Func.continue]


theorem loopEnv5_of_reads (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2)
    (h1 : E.read (%1) = .value 0#8)
    (h2 : E.read (%2) = .value 256#64)
    (h4 : E.read (%4) = .value 0#64)
    (h5 : E.read (%5) = .value 6#64)
    (h6 : E.read (%6) = .value 63#64)
    (h7 : E.read (%7) = .value 59#64)
    (h8 : E.read (%8) = .value 8#64)
    (h9 : E.read (%9) = .value 31#64)
    (h10 : E.read (%10) = .value 1#64)
    (h11 : E.read (%11) = .value 15#64)
    (h12 : E.read (%12) = .value 224#8)
    (h13 : E.read (%13) = .value 5#64)
    (h14 : E.read (%14) = .value 251#64)
    (h15 : E.read (%258) = .value scratch)
    (h18 : E.read (%269) = .value (BitVec.ofNat 64 carry.val))
    (h19 : E.read (%270) = .value (BitVec.ofNat 64 pos.val))
    : loopEnv5 E scratch pos carry = E := by
  unfold loopEnv5
  rw [Env.write_of_read E (%1) h1, Env.write_of_read E (%2) h2, Env.write_of_read E (%4) h4, Env.write_of_read E (%5) h5, Env.write_of_read E (%6) h6, Env.write_of_read E (%7) h7, Env.write_of_read E (%8) h8, Env.write_of_read E (%9) h9, Env.write_of_read E (%10) h10, Env.write_of_read E (%11) h11, Env.write_of_read E (%12) h12, Env.write_of_read E (%13) h13, Env.write_of_read E (%14) h14, Env.write_of_read E (%258) h15, Env.write_of_read E (%269) h18, Env.write_of_read E (%270) h19]

theorem evenInput_control5 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    evenInput5 (controlEnv5 E scratch pos carry bits) pos =
      controlEnv5 E scratch pos carry bits := by
  let base := controlEnv5 E scratch pos carry bits
  have h2 : base.read (%2) = .value 256#64 := by
    by_cases hshort : pos.val % 64 < 59
    all_goals simp [base, controlEnv5, windowResult5, windowInput5, loadedEnv5, loadResult5, loadInput5, crossResult5, crossInput5, loopEnv5, hshort, mlir_env]
  have h10 : base.read (%10) = .value 1#64 := by
    by_cases hshort : pos.val % 64 < 59
    all_goals simp [base, controlEnv5, windowResult5, windowInput5, loadedEnv5, loadResult5, loadInput5, crossResult5, crossInput5, loopEnv5, hshort, mlir_env]
  have h19 : base.read (%270) = .value (BitVec.ofNat 64 pos.val) := by
    by_cases hshort : pos.val % 64 < 59
    all_goals simp [base, controlEnv5, windowResult5, windowInput5, loadedEnv5, loadResult5, loadInput5, crossResult5, crossInput5, loopEnv5, hshort, mlir_env]
  change evenInput5 base pos = base
  unfold evenInput5
  rw [Env.write_of_read base (%2) h2, Env.write_of_read base (%10) h10, Env.write_of_read base (%270) h19]

theorem storeInput_control5 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    storeInput5 (controlEnv5 E scratch pos carry bits) pos (sum5 (mask5 (WordWindow.rawWindow bits pos.val 5)) carry) =
      controlEnv5 E scratch pos carry bits := by
  let base := controlEnv5 E scratch pos carry bits
  have h1 : base.read (%1) = .value 0#8 := by
    by_cases hshort : pos.val % 64 < 59
    all_goals simp [base, controlEnv5, windowResult5, windowInput5, loadedEnv5, loadResult5, loadInput5, crossResult5, crossInput5, loopEnv5, hshort, mlir_env]
  have h11 : base.read (%11) = .value 15#64 := by
    by_cases hshort : pos.val % 64 < 59
    all_goals simp [base, controlEnv5, windowResult5, windowInput5, loadedEnv5, loadResult5, loadInput5, crossResult5, crossInput5, loopEnv5, hshort, mlir_env]
  have h12 : base.read (%12) = .value (-32 : BitVec 8) := by
    by_cases hshort : pos.val % 64 < 59
    all_goals simp [base, controlEnv5, windowResult5, windowInput5, loadedEnv5, loadResult5, loadInput5, crossResult5, crossInput5, loopEnv5, hshort, mlir_env]
  have h13 : base.read (%13) = .value 5#64 := by
    by_cases hshort : pos.val % 64 < 59
    all_goals simp [base, controlEnv5, windowResult5, windowInput5, loadedEnv5, loadResult5, loadInput5, crossResult5, crossInput5, loopEnv5, hshort, mlir_env]
  have h14 : base.read (%14) = .value 251#64 := by
    by_cases hshort : pos.val % 64 < 59
    all_goals simp [base, controlEnv5, windowResult5, windowInput5, loadedEnv5, loadResult5, loadInput5, crossResult5, crossInput5, loopEnv5, hshort, mlir_env]
  have h19 : base.read (%270) = .value (BitVec.ofNat 64 pos.val) := by
    by_cases hshort : pos.val % 64 < 59
    all_goals simp [base, controlEnv5, windowResult5, windowInput5, loadedEnv5, loadResult5, loadInput5, crossResult5, crossInput5, loopEnv5, hshort, mlir_env]
  have h34 : base.read (%285) = .value (BitVec.ofNat 64 (sum5 (mask5 (WordWindow.rawWindow bits pos.val 5)) carry).val) := by
    by_cases hshort : pos.val % 64 < 59
    all_goals simp [base, controlEnv5, windowResult5, windowInput5, loadedEnv5, loadResult5, loadInput5, crossResult5, crossInput5, loopEnv5, hshort, mlir_env]
  change storeInput5 base pos (sum5 (mask5 (WordWindow.rawWindow bits pos.val 5)) carry) = base
  unfold storeInput5
  rw [Env.write_of_read base (%1) h1, Env.write_of_read base (%11) h11, Env.write_of_read base (%12) h12, Env.write_of_read base (%13) h13, Env.write_of_read base (%14) h14, Env.write_of_read base (%270) h19, Env.write_of_read base (%285) h34]

def nextCarry5 (window : Fin 33) : Fin 2 :=
  ⟨if 15 < window.val then 1 else 0, by split_ifs <;> decide⟩

theorem carry5_nextCarry (window : Fin 33) :
    carry5 window = BitVec.ofNat 64 (nextCarry5 window).val := by
  unfold carry5 nextCarry5
  split_ifs <;> rfl

def evenNextEnv5 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) : ⟪avx2Kernel.Γ⟫ :=
  (evenResult5 (controlEnv5 E scratch pos carry bits) pos)[%270 := .value (BitVec.ofNat 64 (pos.val + 1))]

def oddNextEnv5 (E : ⟪avx2Kernel.Γ⟫) (scratch out : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) : ⟪avx2Kernel.Γ⟫ :=
  let window := sum5 (mask5 (WordWindow.rawWindow bits pos.val 5)) carry
  (storeResult5 (controlEnv5 E scratch pos carry bits) out pos window)[
    %268 := .value (BitVec.ofNat 64 (pos.val + 5)), %269 := .value (carry5 window),
    %270 := .value (BitVec.ofNat 64 (pos.val + 5))]

theorem evenNextEnv5_normalized (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) (hnext : pos.val + 1 < 256) :
    loopEnv5 (evenNextEnv5 E scratch pos carry bits) scratch ⟨pos.val + 1, hnext⟩ carry =
      evenNextEnv5 E scratch pos carry bits := by
  apply loopEnv5_of_reads
  all_goals
    by_cases hshort : pos.val % 64 < 59
    all_goals simp [evenNextEnv5, evenResult5, evenInput5, controlEnv5, windowResult5, windowInput5, loadedEnv5, loadResult5, loadInput5, crossResult5, crossInput5, loopEnv5, hshort, mlir_env]

theorem oddNextEnv5_normalized (E : ⟪avx2Kernel.Γ⟫) (scratch out : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) (hnext : pos.val + 5 < 256) :
    loopEnv5 (oddNextEnv5 E scratch out pos carry bits) scratch ⟨pos.val + 5, hnext⟩
      (nextCarry5 (sum5 (mask5 (WordWindow.rawWindow bits pos.val 5)) carry)) =
      oddNextEnv5 E scratch out pos carry bits := by
  apply loopEnv5_of_reads
  all_goals
    by_cases hshort : pos.val % 64 < 59
    all_goals simp [oddNextEnv5, storeResult5, storeInput5, controlEnv5, windowResult5, windowInput5, loadedEnv5, loadResult5, loadInput5, crossResult5, crossInput5, loopEnv5, hshort, mlir_env,
      carry5_nextCarry]

theorem controlEnv5_arg (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    (controlEnv5 E scratch pos carry bits).read (%266) = E.read (%266) := by
  by_cases hshort : pos.val % 64 < 59
  all_goals simp [controlEnv5, windowResult5, windowInput5, loadedEnv5, loadResult5, loadInput5, crossResult5, crossInput5, loopEnv5, hshort, mlir_env]

theorem evenNextEnv5_arg (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    (evenNextEnv5 E scratch pos carry bits).read (%266) = E.read (%266) := by
  simp [evenNextEnv5, evenResult5, evenInput5, mlir_env, controlEnv5_arg]

theorem oddNextEnv5_arg (E : ⟪avx2Kernel.Γ⟫) (scratch out : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    (oddNextEnv5 E scratch out pos carry bits).read (%266) = E.read (%266) := by
  simp [oddNextEnv5, storeResult5, storeInput5, mlir_env, controlEnv5_arg]

/-- The even path executes its original backedge or final exit. -/
theorem avx2_naf5_even_iteration (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits)
    (heven : (sum5 (mask5 (WordWindow.rawWindow bits pos.val 5)) carry).val % 2 = 0) :
    (avx2Kernel p g).runFrom (loopEnv5 E scratch pos carry) 2 s =
      if hnext : pos.val + 1 < 256 then
        (avx2Kernel p g).runFrom (loopEnv5 (evenNextEnv5 E scratch pos carry bits) scratch
          ⟨pos.val + 1, hnext⟩ carry) 2 s
      else (avx2Kernel p g).runFrom
        (evenResult5 (controlEnv5 E scratch pos carry bits) pos) 7 s := by
  rw [avx2_naf5_read_window_run p g E scratch pos carry bits s hbuffer hbits, if_pos heven]
  conv_lhs => rw [← evenInput_control5 E scratch pos carry bits]
  rw [even5_run]
  by_cases hnext : pos.val + 1 < 256
  · have hend : ¬pos.val + 1 = 256 := by omega
    rw [if_neg hend, dif_pos hnext, evenNextEnv5_normalized]
    rfl
  · have hend : pos.val + 1 = 256 := by have := pos.isLt; omega
    rw [if_pos hend, dif_neg hnext]

/-- The odd path executes its actual store and outer carry edge. -/
theorem avx2_naf5_odd_iteration (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (scratch out : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits)
    (houtbuf : Buffer s.mem out 256) (hout : E.read (%266) = .value out)
    (hodd : ¬(sum5 (mask5 (WordWindow.rawWindow bits pos.val 5)) carry).val % 2 = 0) :
    (avx2Kernel p g).runFrom (loopEnv5 E scratch pos carry) 2 s =
      let window := sum5 (mask5 (WordWindow.rawWindow bits pos.val 5)) carry
      let s' := {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte5 window)}
      if hnext : pos.val + 5 < 256 then
        (avx2Kernel p g).runFrom (loopEnv5 (oddNextEnv5 E scratch out pos carry bits) scratch
          ⟨pos.val + 5, hnext⟩ (nextCarry5 window)) 2 s'
      else (avx2Kernel p g).runFrom
        (storeResult5 (controlEnv5 E scratch pos carry bits) out pos window) 7 s' := by
  rw [avx2_naf5_read_window_run p g E scratch pos carry bits s hbuffer hbits, if_neg hodd]
  conv_lhs => rw [← storeInput_control5 E scratch pos carry bits]
  rw [store5_run p g _ out pos _ s houtbuf (by rw [controlEnv5_arg]; exact hout)]
  dsimp only
  by_cases hnext : pos.val + 5 < 256
  · have hguard : pos.val < 251 := by omega
    rw [if_pos hguard, dif_pos hnext, carry5_run, oddNextEnv5_normalized]
    simp [oddNextEnv5, mlir_env]
  · have hguard : ¬pos.val < 251 := by omega
    rw [if_neg hguard, dif_neg hnext]

theorem loopEnv8_of_reads (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2)
    (h1 : E.read (%1) = .value 0#8)
    (h2 : E.read (%2) = .value 256#64)
    (h4 : E.read (%4) = .value 0#64)
    (h5 : E.read (%5) = .value 6#64)
    (h6 : E.read (%6) = .value 63#64)
    (h7 : E.read (%15) = .value 56#64)
    (h8 : E.read (%8) = .value 8#64)
    (h9 : E.read (%16) = .value 255#64)
    (h10 : E.read (%10) = .value 1#64)
    (h11 : E.read (%17) = .value 127#64)
    (h12 : E.read (%18) = .value 248#64)
    (h13 : E.read (%257) = .value scratch)
    (h16 : E.read (%300) = .value (BitVec.ofNat 64 carry.val))
    (h17 : E.read (%301) = .value (BitVec.ofNat 64 pos.val))
    : loopEnv8 E scratch pos carry = E := by
  unfold loopEnv8
  rw [Env.write_of_read E (%1) h1, Env.write_of_read E (%2) h2, Env.write_of_read E (%4) h4, Env.write_of_read E (%5) h5, Env.write_of_read E (%6) h6, Env.write_of_read E (%15) h7, Env.write_of_read E (%8) h8, Env.write_of_read E (%16) h9, Env.write_of_read E (%10) h10, Env.write_of_read E (%17) h11, Env.write_of_read E (%18) h12, Env.write_of_read E (%257) h13, Env.write_of_read E (%300) h16, Env.write_of_read E (%301) h17]

theorem evenInput_control8 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    evenInput8 (controlEnv8 E scratch pos carry bits) pos =
      controlEnv8 E scratch pos carry bits := by
  let base := controlEnv8 E scratch pos carry bits
  have h2 : base.read (%2) = .value 256#64 := by
    by_cases hshort : pos.val % 64 < 56
    all_goals simp [base, controlEnv8, windowResult8, windowInput8, loadedEnv8, loadResult8, loadInput8, crossResult8, crossInput8, loopEnv8, hshort, mlir_env]
  have h10 : base.read (%10) = .value 1#64 := by
    by_cases hshort : pos.val % 64 < 56
    all_goals simp [base, controlEnv8, windowResult8, windowInput8, loadedEnv8, loadResult8, loadInput8, crossResult8, crossInput8, loopEnv8, hshort, mlir_env]
  have h17 : base.read (%301) = .value (BitVec.ofNat 64 pos.val) := by
    by_cases hshort : pos.val % 64 < 56
    all_goals simp [base, controlEnv8, windowResult8, windowInput8, loadedEnv8, loadResult8, loadInput8, crossResult8, crossInput8, loopEnv8, hshort, mlir_env]
  change evenInput8 base pos = base
  unfold evenInput8
  rw [Env.write_of_read base (%2) h2, Env.write_of_read base (%10) h10, Env.write_of_read base (%301) h17]

theorem storeInput_control8 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    storeInput8 (controlEnv8 E scratch pos carry bits) pos (sum8 (mask8 (WordWindow.rawWindow bits pos.val 8)) carry) =
      controlEnv8 E scratch pos carry bits := by
  let base := controlEnv8 E scratch pos carry bits
  have h8 : base.read (%8) = .value 8#64 := by
    by_cases hshort : pos.val % 64 < 56
    all_goals simp [base, controlEnv8, windowResult8, windowInput8, loadedEnv8, loadResult8, loadInput8, crossResult8, crossInput8, loopEnv8, hshort, mlir_env]
  have h11 : base.read (%17) = .value 127#64 := by
    by_cases hshort : pos.val % 64 < 56
    all_goals simp [base, controlEnv8, windowResult8, windowInput8, loadedEnv8, loadResult8, loadInput8, crossResult8, crossInput8, loopEnv8, hshort, mlir_env]
  have h12 : base.read (%18) = .value 248#64 := by
    by_cases hshort : pos.val % 64 < 56
    all_goals simp [base, controlEnv8, windowResult8, windowInput8, loadedEnv8, loadResult8, loadInput8, crossResult8, crossInput8, loopEnv8, hshort, mlir_env]
  have h17 : base.read (%301) = .value (BitVec.ofNat 64 pos.val) := by
    by_cases hshort : pos.val % 64 < 56
    all_goals simp [base, controlEnv8, windowResult8, windowInput8, loadedEnv8, loadResult8, loadInput8, crossResult8, crossInput8, loopEnv8, hshort, mlir_env]
  have h32 : base.read (%316) = .value (BitVec.ofNat 64 (sum8 (mask8 (WordWindow.rawWindow bits pos.val 8)) carry).val) := by
    by_cases hshort : pos.val % 64 < 56
    all_goals simp [base, controlEnv8, windowResult8, windowInput8, loadedEnv8, loadResult8, loadInput8, crossResult8, crossInput8, loopEnv8, hshort, mlir_env]
  change storeInput8 base pos (sum8 (mask8 (WordWindow.rawWindow bits pos.val 8)) carry) = base
  unfold storeInput8
  rw [Env.write_of_read base (%8) h8, Env.write_of_read base (%17) h11, Env.write_of_read base (%18) h12, Env.write_of_read base (%301) h17, Env.write_of_read base (%316) h32]

def nextCarry8 (window : Fin 257) : Fin 2 :=
  ⟨if 127 < window.val then 1 else 0, by split_ifs <;> decide⟩

theorem carry8_nextCarry (window : Fin 257) :
    carry8 window = BitVec.ofNat 64 (nextCarry8 window).val := by
  unfold carry8 nextCarry8
  split_ifs <;> rfl

def evenNextEnv8 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) : ⟪avx2Kernel.Γ⟫ :=
  (evenResult8 (controlEnv8 E scratch pos carry bits) pos)[%301 := .value (BitVec.ofNat 64 (pos.val + 1))]

def oddNextEnv8 (E : ⟪avx2Kernel.Γ⟫) (scratch out : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) : ⟪avx2Kernel.Γ⟫ :=
  let window := sum8 (mask8 (WordWindow.rawWindow bits pos.val 8)) carry
  (storeResult8 (controlEnv8 E scratch pos carry bits) out pos window)[
    %299 := .value (BitVec.ofNat 64 (pos.val + 8)), %300 := .value (carry8 window),
    %301 := .value (BitVec.ofNat 64 (pos.val + 8))]

theorem evenNextEnv8_normalized (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) (hnext : pos.val + 1 < 256) :
    loopEnv8 (evenNextEnv8 E scratch pos carry bits) scratch ⟨pos.val + 1, hnext⟩ carry =
      evenNextEnv8 E scratch pos carry bits := by
  apply loopEnv8_of_reads
  all_goals
    by_cases hshort : pos.val % 64 < 56
    all_goals simp [evenNextEnv8, evenResult8, evenInput8, controlEnv8, windowResult8, windowInput8, loadedEnv8, loadResult8, loadInput8, crossResult8, crossInput8, loopEnv8, hshort, mlir_env]

theorem oddNextEnv8_normalized (E : ⟪avx2Kernel.Γ⟫) (scratch out : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) (hnext : pos.val + 8 < 256) :
    loopEnv8 (oddNextEnv8 E scratch out pos carry bits) scratch ⟨pos.val + 8, hnext⟩
      (nextCarry8 (sum8 (mask8 (WordWindow.rawWindow bits pos.val 8)) carry)) =
      oddNextEnv8 E scratch out pos carry bits := by
  apply loopEnv8_of_reads
  all_goals
    by_cases hshort : pos.val % 64 < 56
    all_goals simp [oddNextEnv8, storeResult8, storeInput8, controlEnv8, windowResult8, windowInput8, loadedEnv8, loadResult8, loadInput8, crossResult8, crossInput8, loopEnv8, hshort, mlir_env,
      carry8_nextCarry]

theorem controlEnv8_arg (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    (controlEnv8 E scratch pos carry bits).read (%265) = E.read (%265) := by
  by_cases hshort : pos.val % 64 < 56
  all_goals simp [controlEnv8, windowResult8, windowInput8, loadedEnv8, loadResult8, loadInput8, crossResult8, crossInput8, loopEnv8, hshort, mlir_env]

theorem evenNextEnv8_arg (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    (evenNextEnv8 E scratch pos carry bits).read (%265) = E.read (%265) := by
  simp [evenNextEnv8, evenResult8, evenInput8, mlir_env, controlEnv8_arg]

theorem oddNextEnv8_arg (E : ⟪avx2Kernel.Γ⟫) (scratch out : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) :
    (oddNextEnv8 E scratch out pos carry bits).read (%265) = E.read (%265) := by
  simp [oddNextEnv8, storeResult8, storeInput8, mlir_env, controlEnv8_arg]

/-- The even path executes its original backedge or final exit. -/
theorem avx2_naf8_even_iteration (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits)
    (heven : (sum8 (mask8 (WordWindow.rawWindow bits pos.val 8)) carry).val % 2 = 0) :
    (avx2Kernel p g).runFrom (loopEnv8 E scratch pos carry) 9 s =
      if hnext : pos.val + 1 < 256 then
        (avx2Kernel p g).runFrom (loopEnv8 (evenNextEnv8 E scratch pos carry bits) scratch
          ⟨pos.val + 1, hnext⟩ carry) 9 s
      else (avx2Kernel p g).runFrom
        (evenResult8 (controlEnv8 E scratch pos carry bits) pos) 14 s := by
  rw [avx2_naf8_read_window_run p g E scratch pos carry bits s hbuffer hbits, if_pos heven]
  conv_lhs => rw [← evenInput_control8 E scratch pos carry bits]
  rw [even8_run]
  by_cases hnext : pos.val + 1 < 256
  · have hend : ¬pos.val + 1 = 256 := by omega
    rw [if_neg hend, dif_pos hnext, evenNextEnv8_normalized]
    rfl
  · have hend : pos.val + 1 = 256 := by have := pos.isLt; omega
    rw [if_pos hend, dif_neg hnext]

/-- The odd path executes its actual store and outer carry edge. -/
theorem avx2_naf8_odd_iteration (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (scratch out : Pointer) (pos : Fin 256)
    (carry : Fin 2) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits)
    (houtbuf : Buffer s.mem out 256) (hout : E.read (%265) = .value out)
    (hodd : ¬(sum8 (mask8 (WordWindow.rawWindow bits pos.val 8)) carry).val % 2 = 0) :
    (avx2Kernel p g).runFrom (loopEnv8 E scratch pos carry) 9 s =
      let window := sum8 (mask8 (WordWindow.rawWindow bits pos.val 8)) carry
      let s' := {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)}
      if hnext : pos.val + 8 < 256 then
        (avx2Kernel p g).runFrom (loopEnv8 (oddNextEnv8 E scratch out pos carry bits) scratch
          ⟨pos.val + 8, hnext⟩ (nextCarry8 window)) 9 s'
      else (avx2Kernel p g).runFrom
        (storeResult8 (controlEnv8 E scratch pos carry bits) out pos window) 14 s' := by
  rw [avx2_naf8_read_window_run p g E scratch pos carry bits s hbuffer hbits, if_neg hodd]
  conv_lhs => rw [← storeInput_control8 E scratch pos carry bits]
  rw [store8_run p g _ out pos _ s houtbuf (by rw [controlEnv8_arg]; exact hout)]
  dsimp only
  by_cases hnext : pos.val + 8 < 256
  · have hguard : pos.val < 248 := by omega
    rw [if_pos hguard, dif_pos hnext, carry8_run, oddNextEnv8_normalized]
    simp [oddNextEnv8, mlir_env]
  · have hguard : ¬pos.val < 248 := by omega
    rw [if_neg hguard, dif_neg hnext]


end Agave.Ed25519.DoubleBase.ExecutionAvx2
