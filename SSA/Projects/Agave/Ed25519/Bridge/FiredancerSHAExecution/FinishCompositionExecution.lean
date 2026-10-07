import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishOutput

/-! Compose the actual three-block finalizer CFG. Compression calls remain
explicit local call equations, so this layer does not assume a finalizer result. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

structure LastReady (E : Env program.Γ) (context output : Pointer)
    (n : Nat) (lo hi : Word) : Prop extends OutputReady E context output where
  one : E.read (%5) = .value 1#64
  limit : E.read (%6) = .value 112#64
  zeroByte : E.read (%8) = .value 0#8
  endLength : E.read (%10) = .value 120#64
  low : E.read (%29) = .value lo
  high : E.read (%31) = .value hi
  count : E.read (%37) = .value (BitVec.ofNat 64 n)

def lastEntry (E : Env program.Γ) (n : Nat) : Env program.Γ :=
  E[%37 := .value (BitVec.ofNat 64 n)]

@[simp] theorem params1 : program.blockParams 1 = .nil := rfl

@[simp] theorem params2 : program.blockParams 2 = .cons (%37) .nil := rfl

/-- Entry reaches the short-path final block with the marker byte installed. -/
theorem entry_short (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (E : Env program.Γ) (state : GlobalState) (context : Pointer)
    (used : Nat) (lo hi : Word) (hc : E.read (%arg0) = .value context)
    (hn : used < 112) (hr : SmallRange state.mem context 224)
    (hu : state.mem.readAt (context.add 200#64) 64 = BitVec.ofNat 64 used)
    (hlo : state.mem.readAt (context.add 208#64) 64 = lo)
    (hhi : state.mem.readAt (context.add 216#64) 64 = hi) :
    program.bb0.run (program core).blockParams E state =
      .value ((lastEntry (entryEnv E context used lo hi) (used + 1), .inr 2),
        {state with mem := markerMemory state.mem context used}) := by
  have hb := entry_body E state context used lo hi hc (by omega) hr hu hlo hhi
  have hchoice := entry_choice E context used lo hi (by omega)
  simp only [BasicBlock.run, EffectM.bind_eq, hb, PoisonOr.value_bind]
  simp only [program.bb0, Exit.run, hchoice]
  simp [hn, show ¬112 ≤ used by omega, Jump.run, lastEntry, entryEnv,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, EffectM.bind_eq, mlir_env, mlir_effect, BitVec.ofNat_add]

/-- Entry takes the source's extra-block edge exactly at the 112-byte cutoff. -/
theorem entry_long (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (E : Env program.Γ) (state : GlobalState) (context : Pointer)
    (used : Nat) (lo hi : Word) (hc : E.read (%arg0) = .value context)
    (hn : used < 128) (hl : 112 ≤ used) (hr : SmallRange state.mem context 224)
    (hu : state.mem.readAt (context.add 200#64) 64 = BitVec.ofNat 64 used)
    (hlo : state.mem.readAt (context.add 208#64) 64 = lo)
    (hhi : state.mem.readAt (context.add 216#64) 64 = hi) :
    program.bb0.run (program core).blockParams E state =
      .value ((entryEnv E context used lo hi, .inr 1),
        {state with mem := markerMemory state.mem context used}) := by
  have hb := entry_body E state context used lo hi hc hn hr hu hlo hhi
  have hchoice := entry_choice E context used lo hi hn
  simp only [BasicBlock.run, EffectM.bind_eq, hb, PoisonOr.value_bind]
  simp only [program.bb0, Exit.run, hchoice]
  simp [hl, Jump.run, Regs.read_nil, Env.writeMany_nil, EffectM.pure_eq, mlir_effect]

theorem entry_lastReady (E : Env program.Γ) (context output : Pointer)
    (used n : Nat) (lo hi : Word)
    (hc : E.read (%arg0) = .value context) (ho : E.read (%arg1) = .value output) :
    LastReady (lastEntry (entryEnv E context used lo hi) n) context output n lo hi := by
  have ha0 : E.args 0 = .value context := hc
  have ha1 : E.args 1 = .value output := ho
  constructor
  · constructor <;> simp [lastEntry, entryEnv, ha0, ha1, mlir_env]
  all_goals simp [lastEntry, entryEnv, mlir_env]

theorem long_lastReady (E : Env program.Γ) (context output : Pointer)
    (used : Nat) (lo hi : Word)
    (hc : E.read (%arg0) = .value context) (ho : E.read (%arg1) = .value output) :
    LastReady (lastEntry (longEnv (entryEnv E context used lo hi) context used) 0)
      context output 0 lo hi := by
  have ha0 : E.args 0 = .value context := hc
  have ha1 : E.args 1 = .value output := ho
  constructor
  · constructor <;> simp [lastEntry, longEnv, entryEnv, ha0, ha1, mlir_env]
  all_goals simp [lastEntry, longEnv, entryEnv, mlir_env]

/-- The long block zeroes the tail and executes its actual compression call. -/
theorem long_block (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (E : Env program.Γ) (state after : GlobalState) (context : Pointer) (used : Nat)
    (hn : used < 128) (hr : SmallRange state.mem context 224)
    (hc : E.read (%arg0) = .value context)
    (hu : E.read (%27) = .value (BitVec.ofNat 64 used))
    (hu1 : E.read (%33) = .value (BitVec.ofNat 64 (used + 1)))
    (h127 : E.read (%7) = .value 127#64) (hz : E.read (%8) = .value 0#8)
    (hchain : E.read (%25) = .value (context.add 128#64))
    (hone : E.read (%5) = .value 1#64) (hzero : E.read (%9) = .value 0#64)
    (hcore : core (.cons (.value (context.add 128#64))
      (.cons (.value context) (.cons (.value 1#64) .nil)))
      {state with mem := longMemory state.mem context used} = .value (.nil, after)) :
    (program.bb1 core).run (program core).blockParams E state =
      .value ((lastEntry (longEnv E context used) 0, .inr 2), after) := by
  have ha0 : E.args 0 = .value context := hc
  have hb := long_prefix core E state context used hn hr hc hu hu1 h127 hz
  have hsplit : (program.bb1 core).body =
      (program.bb1 core).body.take 3 ++ (program.bb1 core).body.drop 3 :=
    (List.take_append_drop 3 _).symm
  unfold BasicBlock.run
  conv_lhs => rw [hsplit, List.foldlM_append]
  simp only [EffectM.bind_eq, hb, PoisonOr.value_bind]
  simp [program.bb1, Instr.run, Exit.run, Jump.run, longEnv, lastEntry,
    ha0, hchain, hone, hzero, hcore, List.foldlM_cons, List.foldlM_nil,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, EffectM.bind_eq, mlir_env, mlir_effect]

/-- Actual final-block execution through its core call, eight output stores,
and return of the caller's output pointer. -/
theorem last_block (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (E : Env program.Γ) (state after : GlobalState) (context output : Pointer)
    (n : Nat) (lo hi : Word) (s : State)
    (h : LastReady E context output n lo hi) (hn : n ≤ 112)
    (hc : SmallRange state.mem context 224)
    (hc' : SmallRange after.mem context 224) (ho' : SmallRange after.mem output 64)
    (hne : output.id ≠ context.id) (hs : readState after.mem context = s)
    (hcore : core (.cons (.value (context.add 128#64))
      (.cons (.value context) (.cons (.value 1#64) .nil)))
      {state with mem := lastMemory state.mem context n lo hi} = .value (.nil, after)) :
    (program.bb2 core).run (program core).blockParams E state =
      .value ((outputEnv (lastEnv E context n lo hi) context output s,
        .inl (.cons (.value output) .nil)),
        {after with mem := outputMemory after.mem output s}) := by
  have ha0 : E.args 0 = .value context := h.contextReg
  have ha1 : E.args 1 = .value output := h.outputReg
  have hp := last_prefix core E state context n lo hi hn hc h.contextReg
    h.limit h.zeroByte h.endLength h.low h.high h.count
  have hout : OutputReady (lastEnv E context n lo hi) context output := by
    constructor <;> simp [lastEnv, ha0, ha1, h.chain, h.c11, h.c12,
      h.c13, h.c14, h.c15, h.c16, h.c17, h.c18, h.c19, h.c20, h.c21, h.c22,
      h.c23, h.c24, mlir_env]
  have hb := output_body core (lastEnv E context n lo hi) after context output s
    hout hc' ho' hne hs
  have hsplit : (program.bb2 core).body = (program.bb2 core).body.take 9 ++
      [(program.bb2 core).body[9]'(by simp [program.bb2])] ++ (program.bb2 core).body.drop 10 := rfl
  have hcall : List.foldlM Instr.run (lastEnv E context n lo hi)
      [(program.bb2 core).body[9]'(by simp [program.bb2])]
      {state with mem := lastMemory state.mem context n lo hi} =
      .value (lastEnv E context n lo hi, after) := by
    simp [program.bb2, Instr.run, lastEnv, ha0, h.chain, h.one, hcore,
      List.foldlM_cons, List.foldlM_nil, Regs.read_cons, Regs.read_nil,
      Env.writeMany_nil, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]
  unfold BasicBlock.run
  conv_lhs => rw [hsplit, List.foldlM_append, List.foldlM_append]
  simp only [EffectM.bind_eq, hp, PoisonOr.value_bind, hcall, hb]
  simp [program.bb2, Exit.run, outputEnv, lastEnv, ha1,
    Regs.read_cons, Regs.read_nil, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
