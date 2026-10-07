import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreLaterLoop
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreInputMemory

/-! Actual first-loop execution initializes the circular schedule from input
bytes and executes the first sixteen FIPS rounds. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization (swapBytes)
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

structure FirstLoopReady (E : Env program.Γ) (stack data kp : Pointer) (r : Nat) (s : State) : Prop where
  state : FirstStateReady E s
  input : InputReady E stack data r
  constants : Constants E kp
  futureSchedule : ScheduleReady (laterNextEnv E 16 s) stack 16
  limit16 : E.read (%2) = .value 16#64
  limit80 : E.read (%26) = .value 80#64

theorem FirstLoopReady.one {E : Env program.Γ} {stack data kp : Pointer} {r : Nat} {s : State}
    (h : FirstLoopReady E stack data kp r s) : E.read (%18) = .value 1#64 := by
  simpa [laterNextEnv, mlir_env] using h.futureSchedule.c18

structure FirstMemory (m : MemoryState) (stack data kp : Pointer) (block : Bytes) (r : Nat) : Prop where
  liveStack : SmallRange m stack 128
  liveData : SmallRange m data 128
  liveConstants : SmallRange m kp 640
  distinct : stack.id ≠ kp.id
  dataDistinct : stack.id ≠ data.id
  ring : InitialRingMemory m stack block r
  table : ∀ j, j < 80 → m.readAt (kp.add (BitVec.ofNat 64 (8 * j))) 64 = constants.toList.getD j 0
  bytes : readBytes m data 128 = block

theorem FirstMemory.word {m : MemoryState} {stack data kp : Pointer} {block : Bytes} {r : Nat}
    (h : FirstMemory m stack data kp block r) (hr : r < 16) :
    swapBytes (m.readAt (data.add (BitVec.ofNat 64 (8 * r))) 64) = (schedule block).getD r 0 := by
  rw [input_swap_eq m data r h.liveData hr, h.bytes, schedule_initial block r hr]

theorem FirstMemory.step {m : MemoryState} {stack data kp : Pointer} {block : Bytes} {r : Nat}
    (h : FirstMemory m stack data kp block r) (hr : r < 16) :
    FirstMemory (inputMemory m stack r (m.readAt (data.add (BitVec.ofNat 64 (8 * r))) 64))
      stack data kp block (r + 1) := by
  refine ⟨h.liveStack.storeAt _ _, h.liveData.storeAt _ _, h.liveConstants.storeAt _ _,
    h.distinct, h.dataDistinct, ?_, ?_, ?_⟩
  · apply inputMemory_initial_step m stack block r _ hr h.liveStack h.ring
    rw [input_swap_eq m data r h.liveData hr, h.bytes]
  · intro j hj
    have hd : (Range.of (stack.add (BitVec.ofNat 64 (8 * r))) 64).Disjoint
        (Range.of (kp.add (BitVec.ofNat 64 (8 * j))) 64) := Or.inl h.distinct
    simpa only [inputMemory, MemoryState.readAt_storeAt_disjoint hd] using h.table j hj
  · rw [inputMemory_preserves_data m stack data r _ h.liveData h.dataDistinct, h.bytes]

theorem FirstMemory.complete {m : MemoryState} {stack data kp : Pointer} {block : Bytes}
    (h : FirstMemory m stack data kp block 16) : LaterMemory m stack kp (initialRing block) :=
  ⟨h.liveStack, h.liveConstants, h.distinct, initialRingMemory_full m stack block h.ring, h.table⟩

theorem firstNext_loopReady (E : Env program.Γ) (stack data kp : Pointer)
    (r : Nat) (s : State) (native constant : Word) (h : FirstLoopReady E stack data kp r s) :
    FirstLoopReady (firstNextEnv (firstBodyEnv E stack data kp r s native constant)
      (r + 1) (firstRound s (swapBytes native) constant)) stack data kp (r + 1)
      (firstRound s (swapBytes native) constant) := by
  obtain ⟨hstate, hin, hc, hsc, h16, h80⟩ := h
  refine ⟨firstNext_ready _ _ _, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hin with ⟨hstack, hdata, hindex, hzero, hshift⟩
    constructor <;> simp_all [firstNextEnv, firstBodyEnv, firstEnv, inputEnv, mlir_env]
  · rcases hc with ⟨hzero, h14, h18, h41, hmask, hkp, h28, h34, h39⟩
    constructor <;> simp_all [firstNextEnv, firstBodyEnv, firstEnv, inputEnv, mlir_env]
  · rcases hsc with ⟨hindex, hstack, h7, h8, h9, h18, h19, h20, h21, h22, h23, h24, h25⟩
    constructor <;> simp_all [laterNextEnv, firstNextEnv, firstBodyEnv, firstEnv, inputEnv, mlir_env]
  · simpa [firstNextEnv, firstBodyEnv, firstEnv, inputEnv, mlir_env] using h16
  · simpa [firstNextEnv, firstBodyEnv, firstEnv, inputEnv, mlir_env] using h80

theorem firstExit_loopReady (E : Env program.Γ) (stack data kp : Pointer)
    (s : State) (native constant : Word) (h : FirstLoopReady E stack data kp 15 s) :
    LaterLoopReady (laterNextEnv (firstBodyEnv E stack data kp 15 s native constant)
      16 (firstRound s (swapBytes native) constant)) stack kp 16
      (firstRound s (swapBytes native) constant) := by
  obtain ⟨hstate, hin, hc, hsc, h16, h80⟩ := h
  refine ⟨laterNext_ready _ _ _, ?_, ?_, ?_⟩
  · rcases hsc with ⟨hindex, hstack, h7, h8, h9, h18, h19, h20, h21, h22, h23, h24, h25⟩
    constructor <;> simp_all [laterNextEnv, firstBodyEnv, firstEnv, inputEnv, mlir_env]
  · rcases hc with ⟨hzero, h14, h18, h41, hmask, hkp, h28, h34, h39⟩
    constructor <;> simp_all [laterNextEnv, firstBodyEnv, firstEnv, inputEnv, mlir_env]
  · simpa [laterNextEnv, firstBodyEnv, firstEnv, inputEnv, mlir_env] using h80

inductive FirstTrace : Nat → Env program.Γ → GlobalState → Env program.Γ → GlobalState → Prop
  | last {E before F after}
      (step : program.bb2.run program.blockParams E before = .value ((F, .inr 3), after)) :
      FirstTrace 1 E before F after
  | more {n E before F middle G after}
      (step : program.bb2.run program.blockParams E before = .value ((F, .inr 2), middle))
      (rest : FirstTrace n F middle G after) : FirstTrace (n + 1) E before G after

theorem FirstTrace.runFrom {n : Nat} {E F : Env program.Γ} {before after : GlobalState}
    (h : FirstTrace n E before F after) (kp : Pointer) :
    (program kp).runFrom E 2 before = (program kp).runFrom F 3 after := by
  induction h with
  | last step =>
    rw [Func.runFrom_eq]
    change (program.bb2.run program.blockParams _ _ >>= _) = _
    rw [step]
    rfl
  | more step rest ih =>
    rw [Func.runFrom_eq]
    change (program.bb2.run program.blockParams _ _ >>= _) = _
    rw [step]
    exact ih

theorem FirstTrace.evalFrom {n : Nat} {E F : Env program.Γ} {before after : GlobalState}
    (h : FirstTrace n E before F after) (kp : Pointer) (fuel : Nat) :
    (program kp).evalFrom (n + fuel) E 2 before = (program kp).evalFrom fuel F 3 after := by
  induction h with
  | last step =>
    rw [Nat.add_comm 1 fuel]
    simp only [Func.evalFrom, EffectM.bind_eq]
    change (program.bb2.run program.blockParams _ _ >>= _) = _
    rw [step]
    rfl
  | @more n E before F middle G after step rest ih =>
    rw [show n + 1 + fuel = (n + fuel) + 1 by omega]
    simp only [Func.evalFrom, EffectM.bind_eq]
    change (program.bb2.run program.blockParams E before >>= _) = _
    rw [step]
    exact ih

private theorem roundsFrom_head (s : State) (words : List Word) (r n : Nat) :
    roundsFrom s words r (n + 1) =
      roundsFrom (Spec.round s (words.getD r 0) (constants.toList.getD r 0)) words (r + 1) n := by
  simpa only [Nat.add_comm 1 n, roundsFrom, Nat.add_zero] using roundsFrom_add s words r 1 n

theorem first_suffix (block : Bytes) (stack data kp : Pointer) (n : Nat) :
    ∀ (r : Nat), r + n = 15 →
      ∀ (E : Env program.Γ) (before : GlobalState) (s : State),
      FirstLoopReady E stack data kp r s → FirstMemory before.mem stack data kp block r →
      ∃ F after, FirstTrace (n + 1) E before F after ∧
        LaterLoopReady F stack kp 16 (roundsFrom s (schedule block) r (n + 1)) ∧
        FirstMemory after.mem stack data kp block 16 ∧
        RingWrites stack before after ∧ LoopFrame E F := by
  induction n with
  | zero =>
    intro r hend E before s h hm
    have hr : r = 15 := by omega
    subst r
    let native := before.mem.readAt (data.add 120#64) 64
    let c := constants.toList.getD 15 0
    refine ⟨laterNextEnv (firstBodyEnv E stack data kp 15 s native c) 16
      (firstRound s (swapBytes native) c),
      {before with mem := inputMemory before.mem stack 15 native},
      .last (first_exit E before stack data kp s native c h.state h.input h.constants
        h.limit16 h.one hm.liveStack hm.liveData hm.liveConstants hm.distinct rfl
        (hm.table 15 (by decide))), ?_, hm.step (by decide),
      .input (.refl before) 15 native,
      (firstBody_frame E stack data kp 15 s native c).trans (laterNext_frame _ _ _)⟩
    have hf := firstExit_loopReady E stack data kp s native c h
    have hw : swapBytes native = (schedule block).getD 15 0 := hm.word (by decide)
    simpa only [firstRound_eq, hw, roundsFrom, Nat.add_zero, c] using hf
  | succ n ih =>
    intro r hend E before s h hm
    have hr : r < 15 := by omega
    let native := before.mem.readAt (data.add (BitVec.ofNat 64 (8 * r))) 64
    let c := constants.toList.getD r 0
    let F := firstNextEnv (firstBodyEnv E stack data kp r s native c) (r + 1)
      (firstRound s (swapBytes native) c)
    let middle : GlobalState := {before with mem := inputMemory before.mem stack r native}
    obtain ⟨G, after, ht, hf, hmem, hw, he⟩ := ih (r + 1) (by omega) F middle
      (firstRound s (swapBytes native) c) (firstNext_loopReady E stack data kp r s native c h)
      (hm.step (by omega))
    refine ⟨G, after, .more (first_backedge E before stack data kp r s native c
      h.state h.input h.constants h.limit16 h.one hr hm.liveStack hm.liveData hm.liveConstants
      hm.distinct rfl (hm.table r (by omega))) ht, ?_, hmem,
      (RingWrites.input (.refl before) r native).trans hw,
      ((firstBody_frame E stack data kp r s native c).trans (firstNext_frame _ _ _)).trans he⟩
    rw [roundsFrom_head]
    simpa only [firstRound_eq, hm.word (by omega), c, native] using hf

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
