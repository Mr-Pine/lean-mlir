import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreLoopFrame

/-! Finite execution of the actual second SHA core loop. Every trace edge runs
bb3, including its concrete schedule loads, store, round, and terminator. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

structure LaterLoopReady (E : Env program.Γ) (stack kp : Pointer) (r : Nat) (s : State) : Prop where
  state : LaterStateReady E s
  schedule : ScheduleReady E stack r
  constants : Constants E kp
  limit : E.read (%26) = .value 80#64

structure LaterMemory (m : MemoryState) (stack kp : Pointer) (q : Ring) : Prop where
  liveStack : SmallRange m stack 128
  liveConstants : SmallRange m kp 640
  distinct : stack.id ≠ kp.id
  ring : ∀ j, j < 16 → m.readAt (stack.add (BitVec.ofNat 64 (8 * j))) 64 = q j
  table : ∀ j, j < 80 → m.readAt (kp.add (BitVec.ofNat 64 (8 * j))) 64 = Spec.constants.toList.getD j 0

theorem laterNext_loopReady (E : Env program.Γ) (stack kp : Pointer) (q : Ring)
    (r : Nat) (s : State) (constant : Word) (h : LaterLoopReady E stack kp r s) :
    LaterLoopReady (laterNextEnv (laterBodyEnv E stack kp q r s constant)
      (r + 1) (laterRound s (ringWord q r) constant)) stack kp (r + 1)
      (laterRound s (ringWord q r) constant) := by
  obtain ⟨hstate, hsc, hc, h80⟩ := h
  refine ⟨laterNext_ready _ _ _, ?_, ?_, ?_⟩
  · rcases hsc with ⟨hindex, hstack, h7, h8, h9, h18, h19, h20, h21, h22, h23, h24, h25⟩
    constructor <;> simp_all [laterNextEnv, laterBodyEnv, laterEnv, scheduleEnv, mlir_env]
  · rcases hc with ⟨hzero, h14, h18, h41, hmask, hkp, h28, h34, h39⟩
    constructor <;> simp_all [laterNextEnv, laterBodyEnv, laterEnv, scheduleEnv, mlir_env]
  · simpa [laterNextEnv, laterBodyEnv, laterEnv, scheduleEnv, mlir_env] using h80

theorem LaterMemory.step {m : MemoryState} {stack kp : Pointer} {q : Ring}
    (h : LaterMemory m stack kp q) (r : Nat) :
    LaterMemory (scheduleMemory m stack q r) stack kp (ringStep q r) := by
  refine ⟨h.liveStack.storeAt _ _, h.liveConstants.storeAt _ _, h.distinct, ?_, ?_⟩
  · intro j hj
    exact scheduleMemory_read m stack q r j h.liveStack hj (h.ring j hj)
  · intro j hj
    have hd : (Range.of (stack.add (BitVec.ofNat 64 (8 * (r % 16)))) 64).Disjoint
        (Range.of (kp.add (BitVec.ofNat 64 (8 * j))) 64) := Or.inl h.distinct
    simpa only [scheduleMemory, MemoryState.readAt_storeAt_disjoint hd] using h.table j hj

/-- Memory changes confined to writes into the private ring allocation. -/
inductive RingWrites (stack : Pointer) : GlobalState → GlobalState → Prop
  | refl (state) : RingWrites stack state state
  | step {before middle} (h : RingWrites stack before middle) (q : Ring) (r : Nat) :
      RingWrites stack before {middle with mem := scheduleMemory middle.mem stack q r}
  | input {before middle} (h : RingWrites stack before middle) (r : Nat) (native : Word) :
      RingWrites stack before {middle with mem := inputMemory middle.mem stack r native}

theorem RingWrites.trans {stack : Pointer} {a b c : GlobalState}
    (hab : RingWrites stack a b) (hbc : RingWrites stack b c) : RingWrites stack a c := by
  induction hbc with
  | refl => exact hab
  | step h q r ih => exact .step ih q r
  | input h r native ih => exact .input ih r native

theorem RingWrites.readAt {stack : Pointer} {a b : GlobalState}
    (h : RingWrites stack a b) (p : Pointer) (bits : Nat) (hp : stack.id ≠ p.id) :
    b.mem.readAt p bits = a.mem.readAt p bits := by
  induction h with
  | refl => rfl
  | @step middle h q r ih =>
    have hd : (Range.of (stack.add (BitVec.ofNat 64 (8 * (r % 16)))) 64).Disjoint
        (Range.of p bits) := Or.inl hp
    simpa only [scheduleMemory, MemoryState.readAt_storeAt_disjoint hd] using ih
  | @input middle h r native ih =>
    have hd : (Range.of (stack.add (BitVec.ofNat 64 (8 * r))) 64).Disjoint
        (Range.of p bits) := Or.inl hp
    simpa only [inputMemory, MemoryState.readAt_storeAt_disjoint hd] using ih

inductive LaterTrace : Nat → Env program.Γ → GlobalState → Env program.Γ → GlobalState → Prop
  | last {E before F after}
      (step : program.bb3.run program.blockParams E before = .value ((F, .inr 4), after)) :
      LaterTrace 1 E before F after
  | more {n E before F middle G after}
      (step : program.bb3.run program.blockParams E before = .value ((F, .inr 3), middle))
      (rest : LaterTrace n F middle G after) : LaterTrace (n + 1) E before G after

theorem LaterTrace.runFrom {n : Nat} {E F : Env program.Γ} {before after : GlobalState}
    (h : LaterTrace n E before F after) (kp : Pointer) :
    (program kp).runFrom E 3 before = (program kp).runFrom F 4 after := by
  induction h with
  | last step =>
    rw [Func.runFrom_eq]
    change (program.bb3.run program.blockParams _ _ >>= _) = _
    rw [step]
    rfl
  | more step rest ih =>
    rw [Func.runFrom_eq]
    change (program.bb3.run program.blockParams _ _ >>= _) = _
    rw [step]
    exact ih

theorem LaterTrace.evalFrom {n : Nat} {E F : Env program.Γ} {before after : GlobalState}
    (h : LaterTrace n E before F after) (kp : Pointer) (fuel : Nat) :
    (program kp).evalFrom (n + fuel) E 3 before = (program kp).evalFrom fuel F 4 after := by
  induction h with
  | last step =>
    rw [Nat.add_comm 1 fuel]
    simp only [Func.evalFrom, EffectM.bind_eq]
    change (program.bb3.run program.blockParams _ _ >>= _) = _
    rw [step]
    rfl
  | @more n E before F middle G after step rest ih =>
    rw [show n + 1 + fuel = (n + fuel) + 1 by omega]
    simp only [Func.evalFrom, EffectM.bind_eq]
    change (program.bb3.run program.blockParams E before >>= _) = _
    rw [step]
    exact ih

private theorem roundsFrom_head (s : State) (words : List Word) (r n : Nat) :
    roundsFrom s words r (n + 1) =
      roundsFrom (Spec.round s (words.getD r 0) (constants.toList.getD r 0)) words (r + 1) n := by
  simpa only [Nat.add_comm 1 n, roundsFrom, Nat.add_zero] using roundsFrom_add s words r 1 n

/-- Execute any nonempty suffix of rounds 16 through 79. The premises are
local register and live-memory observations, not a compression execution contract. -/
theorem later_suffix (block : Bytes) (stack kp : Pointer) (n : Nat) :
    ∀ (r : Nat), 16 ≤ r → r + n = 79 →
      ∀ (E : Env program.Γ) (before : GlobalState) (q : Ring) (s : State),
      LaterLoopReady E stack kp r s → LaterMemory before.mem stack kp q →
      RingRepresents q block r →
      ∃ F after q', LaterTrace (n + 1) E before F after ∧
        FinalReady F (roundsFrom s (schedule block) r (n + 1)) ∧
        LaterMemory after.mem stack kp q' ∧ RingRepresents q' block 80 ∧
        RingWrites stack before after ∧ LoopFrame E F := by
  induction n with
  | zero =>
    intro r hlo hend E before q s h hm hq
    have hr : r = 79 := by omega
    subst r
    let c := constants.toList.getD 79 0
    refine ⟨laterBodyEnv E stack kp q 79 s c,
      {before with mem := scheduleMemory before.mem stack q 79}, ringStep q 79,
      .last (later_exit E before stack kp q s c h.state h.schedule h.constants h.limit
        hm.liveStack hm.liveConstants hm.distinct hm.ring (hm.table 79 (by decide))), ?_,
      hm.step 79, ?_, .step (.refl before) q 79, laterBody_frame E stack kp q 79 s c⟩
    · have hf := later_final_ready E stack kp q 79 s c h.state
      simpa only [laterRound_eq, ringWord_spec q block 79 hq (by decide) (by decide),
        roundsFrom, Nat.add_zero, c] using hf
    · exact ringStep_represents q block 79 hq (by decide) (by decide)
  | succ n ih =>
    intro r hlo hend E before q s h hm hq
    have hr : r < 79 := by omega
    let c := constants.toList.getD r 0
    let F := laterNextEnv (laterBodyEnv E stack kp q r s c) (r + 1)
      (laterRound s (ringWord q r) c)
    let middle : GlobalState := {before with mem := scheduleMemory before.mem stack q r}
    obtain ⟨G, after, q', ht, hf, hmem, hring, hw, he⟩ := ih (r + 1) (by omega) (by omega)
      F middle (ringStep q r) (laterRound s (ringWord q r) c)
      (laterNext_loopReady E stack kp q r s c h) (hm.step r)
      (ringStep_represents q block r hq hlo (by omega))
    refine ⟨G, after, q', .more (later_backedge E before stack kp q r s c
      h.state h.schedule h.constants h.limit hr hm.liveStack hm.liveConstants hm.distinct
      hm.ring (hm.table r (by omega))) ht, ?_, hmem, hring,
      (RingWrites.step (.refl before) q r).trans hw,
      ((laterBody_frame E stack kp q r s c).trans (laterNext_frame _ _ _)).trans he⟩
    rw [roundsFrom_head]
    simpa only [laterRound_eq, ringWord_spec q block r hq hlo (by omega), c] using hf

/-- All sixty-four rounds of the actual second loop terminate at the actual
feedforward block, with the standard eighty-round working state. -/
theorem later_sixtyfour (block : Bytes) (stack kp : Pointer) (E : Env program.Γ)
    (before : GlobalState) (initial : State)
    (h : LaterLoopReady E stack kp 16 (roundsFrom initial (schedule block) 0 16))
    (hm : LaterMemory before.mem stack kp (initialRing block)) :
    ∃ F after q', LaterTrace 64 E before F after ∧
      FinalReady F (roundsFrom initial (schedule block) 0 80) ∧
      LaterMemory after.mem stack kp q' ∧ RingRepresents q' block 80 ∧
      RingWrites stack before after ∧ LoopFrame E F := by
  obtain ⟨F, after, q', ht, hf, hm, hq, hw, he⟩ :=
    later_suffix block stack kp 63 16 (by decide) (by decide) E before (initialRing block)
      (roundsFrom initial (schedule block) 0 16) h hm (initialRing_represents block)
  refine ⟨F, after, q', ht, ?_, hm, hq, hw, he⟩
  have hcompose := roundsFrom_add initial (schedule block) 0 16 64
  change roundsFrom initial (schedule block) 0 80 =
    roundsFrom (roundsFrom initial (schedule block) 0 16) (schedule block) 16 64 at hcompose
  rw [hcompose]
  exact hf

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
