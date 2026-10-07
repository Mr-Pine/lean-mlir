import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreSchedule

/-! Compose the exact schedule and round instructions of the second core loop.
The K allocation is distinct from the private ring, so the ring update preserves
its value. This closes the complete bb3 body, including its exit comparison. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

structure LaterStateReady (E : Env program.Γ) (s : State) : Prop where
  a : E.read (%97) = .value s.a
  b : E.read (%98) = .value s.b
  c : E.read (%99) = .value s.c
  d : E.read (%100) = .value s.d
  e : E.read (%101) = .value s.e
  f : E.read (%102) = .value s.f
  g : E.read (%105) = .value s.g
  h : E.read (%104) = .value s.h

theorem schedule_ready_round (E : Env program.Γ) (stack : Pointer) (q : Ring) (r : Nat)
    (s : State) (h : LaterStateReady E s) (hr : E.read (%103) = .value (BitVec.ofNat 64 r)) :
    LaterReady (scheduleEnv E stack q r) s (ringWord q r) r := by
  constructor
  · simpa [scheduleEnv, mlir_env] using h.a
  · simpa [scheduleEnv, mlir_env] using h.b
  · simpa [scheduleEnv, mlir_env] using h.c
  · simpa [scheduleEnv, mlir_env] using h.d
  · simpa [scheduleEnv, mlir_env] using h.e
  · simpa [scheduleEnv, mlir_env] using h.f
  · simpa [scheduleEnv, mlir_env] using h.g
  · simpa [scheduleEnv, mlir_env] using h.h
  · simp [scheduleEnv, ringWord, scheduleWord, smallSigma0, smallSigma1, mlir_env]
  · simpa [scheduleEnv, mlir_env] using hr

theorem schedule_constants (E : Env program.Γ) (stack kp : Pointer) (q : Ring) (r : Nat)
    (h : Constants E kp) : Constants (scheduleEnv E stack q r) kp := by
  constructor
  · simpa [scheduleEnv, mlir_env] using h.zero
  · simpa [scheduleEnv, mlir_env] using h.rot14
  · simpa [scheduleEnv, mlir_env] using h.rot18
  · simpa [scheduleEnv, mlir_env] using h.rot41
  · simpa [scheduleEnv, mlir_env] using h.notMask
  · simpa [scheduleEnv, mlir_env] using h.kp
  · simpa [scheduleEnv, mlir_env] using h.rot28
  · simpa [scheduleEnv, mlir_env] using h.rot34
  · simpa [scheduleEnv, mlir_env] using h.rot39

def laterBodyEnv (E : Env program.Γ) (stack kp : Pointer) (q : Ring) (r : Nat)
    (s : State) (constant : Word) : Env program.Γ :=
  (laterEnv (scheduleEnv E stack q r) s (ringWord q r) constant kp r)[
    %161 := .value (BitVec.ofBool (BitVec.ofNat 64 (r + 1) == 80#64))]

theorem later_body_full (E : Env program.Γ) (state : GlobalState) (stack kp : Pointer)
    (q : Ring) (r : Nat) (s : State) (constant : Word)
    (hstate : LaterStateReady E s) (hsc : ScheduleReady E stack r) (hc : Constants E kp)
    (h80 : E.read (%26) = .value 80#64) (hr : r < 80)
    (hs : SmallRange state.mem stack 128) (hk : SmallRange state.mem kp 640)
    (hne : stack.id ≠ kp.id)
    (hread : ∀ j, j < 16 → state.mem.readAt (stack.add (BitVec.ofNat 64 (8 * j))) 64 = q j)
    (hkread : state.mem.readAt (kp.add (BitVec.ofNat 64 (8 * r))) 64 = constant) :
    List.foldlM Instr.run E program.bb3.body state =
      .value (laterBodyEnv E stack kp q r s constant,
        {state with mem := scheduleMemory state.mem stack q r}) := by
  let ES := scheduleEnv E stack q r
  let SS : GlobalState := {state with mem := scheduleMemory state.mem stack q r}
  have hfirst := schedule_body E state stack q r hsc hr hs hread
  have hready : LaterReady ES s (ringWord q r) r :=
    schedule_ready_round E stack q r s hstate hsc.index
  have hconst : Constants ES kp := schedule_constants E stack kp q r hc
  have hks : SmallRange SS.mem kp 640 := hk.storeAt _ _
  have hkread' : SS.mem.readAt (kp.add (BitVec.ofNat 64 (8 * r))) 64 = constant := by
    dsimp only [SS, scheduleMemory]
    have hdis : (Range.of (stack.add (BitVec.ofNat 64 (8 * (r % 16)))) 64).Disjoint
        (Range.of (kp.add (BitVec.ofNat 64 (8 * r))) 64) := Or.inl hne
    rw [MemoryState.readAt_storeAt_disjoint hdis]
    exact hkread
  have hround := later_body ES SS s (ringWord q r) constant kp r hready hconst hr hks hkread'
  have hsplit : program.bb3.body = program.bb3.body.take 29 ++
      ((program.bb3.body.drop 29).take 27 ++ program.bb3.body.drop 56) := by rfl
  rw [hsplit, List.foldlM_append]
  change (List.foldlM Instr.run E (program.bb3.body.take 29) state >>= _) = _
  rw [hfirst]
  change List.foldlM Instr.run ES
    ((program.bb3.body.drop 29).take 27 ++ program.bb3.body.drop 56) SS = _
  rw [List.foldlM_append]
  change (List.foldlM Instr.run ES ((program.bb3.body.drop 29).take 27) SS >>= _) = _
  rw [hround]
  simp [program.bb3, List.foldlM_cons, List.foldlM_nil, Instr.run, laterBodyEnv,
    laterEnv, scheduleEnv, ES, SS, h80, Operation.icmp, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

theorem later_body_result (E : Env program.Γ) (stack kp : Pointer) (q : Ring) (r : Nat)
    (s : State) (constant : Word) :
    (laterBodyEnv E stack kp q r s constant).read (%160) =
      .value (Spec.round s (ringWord q r) constant).a ∧
    (laterBodyEnv E stack kp q r s constant).read (%159) =
      .value (Spec.round s (ringWord q r) constant).e := by
  rw [← laterRound_eq]
  simp [laterBodyEnv, laterEnv, scheduleEnv, laterRound, bigSigma0, bigSigma1, mlir_env]

theorem later_exit_test (r : Nat) (hr : r < 80) :
    (BitVec.ofNat 64 (r + 1) == 80#64) = decide (r + 1 = 80) := by
  interval_cases r <;> decide

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
