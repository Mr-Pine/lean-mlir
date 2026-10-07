import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2378..2416: round 65. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv65 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2578 := (w 50).rotateRight 1
  let v2579 := (w 50).rotateRight 8
  let v2580 := v2578 ^^^ v2579
  let v2581 := (w 50) >>> 7
  let v2582 := v2580 ^^^ v2581
  let v2583 := (w 63).rotateRight 19
  let v2584 := (w 63).rotateRight 61
  let v2585 := v2583 ^^^ v2584
  let v2586 := (w 63) >>> 6
  let v2587 := v2585 ^^^ v2586
  let v2588 := v2582 + (w 49)
  let v2589 := v2588 + (w 58)
  let v2590 := v2589 + v2587
  let v2591 := s.e.rotateRight 14
  let v2592 := s.e.rotateRight 18
  let v2593 := v2591 ^^^ v2592
  let v2594 := s.e.rotateRight 41
  let v2595 := v2593 ^^^ v2594
  let v2596 := s.e &&& s.f
  let v2597 := s.e ^^^ (-1 : Word)
  let v2598 := s.g &&& v2597
  let v2599 := v2596 ||| v2598
  let v2600 := k
  let v2601 := v2590 + v2600
  let v2602 := v2601 + s.h
  let v2603 := v2602 + v2599
  let v2604 := v2603 + v2595
  let v2605 := s.a.rotateRight 28
  let v2606 := s.a.rotateRight 34
  let v2607 := v2605 ^^^ v2606
  let v2608 := s.a.rotateRight 39
  let v2609 := v2607 ^^^ v2608
  let v2610 := s.a &&& s.b
  let v2611 := s.b ^^^ s.c
  let v2612 := s.a &&& v2611
  let v2613 := v2612 ^^^ (s.b &&& s.c)
  let v2614 := v2609 + v2613
  let v2615 := v2604 + s.d
  let v2616 := v2614 + v2604
  E[%2578 := .value v2578,
    %2579 := .value v2579,
    %2580 := .value v2580,
    %2581 := .value v2581,
    %2582 := .value v2582,
    %2583 := .value v2583,
    %2584 := .value v2584,
    %2585 := .value v2585,
    %2586 := .value v2586,
    %2587 := .value v2587,
    %2588 := .value v2588,
    %2589 := .value v2589,
    %2590 := .value v2590,
    %2591 := .value v2591,
    %2592 := .value v2592,
    %2593 := .value v2593,
    %2594 := .value v2594,
    %2595 := .value v2595,
    %2596 := .value v2596,
    %2597 := .value v2597,
    %2598 := .value v2598,
    %2599 := .value v2599,
    %2600 := .value v2600,
    %2601 := .value v2601,
    %2602 := .value v2602,
    %2603 := .value v2603,
    %2604 := .value v2604,
    %2605 := .value v2605,
    %2606 := .value v2606,
    %2607 := .value v2607,
    %2608 := .value v2608,
    %2609 := .value v2609,
    %2610 := .value v2610,
    %2611 := .value v2611,
    %2612 := .value v2612,
    %2613 := .value v2613,
    %2614 := .value v2614,
    %2615 := .value v2615,
    %2616 := .value v2616]

def fullOut65 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2578 := (w 50).rotateRight 1
  let v2579 := (w 50).rotateRight 8
  let v2580 := v2578 ^^^ v2579
  let v2581 := (w 50) >>> 7
  let v2582 := v2580 ^^^ v2581
  let v2583 := (w 63).rotateRight 19
  let v2584 := (w 63).rotateRight 61
  let v2585 := v2583 ^^^ v2584
  let v2586 := (w 63) >>> 6
  let v2587 := v2585 ^^^ v2586
  let v2588 := v2582 + (w 49)
  let v2589 := v2588 + (w 58)
  let v2590 := v2589 + v2587
  let v2591 := s.e.rotateRight 14
  let v2592 := s.e.rotateRight 18
  let v2593 := v2591 ^^^ v2592
  let v2594 := s.e.rotateRight 41
  let v2595 := v2593 ^^^ v2594
  let v2596 := s.e &&& s.f
  let v2597 := s.e ^^^ (-1 : Word)
  let v2598 := s.g &&& v2597
  let v2599 := v2596 ||| v2598
  let v2600 := k
  let v2601 := v2590 + v2600
  let v2602 := v2601 + s.h
  let v2603 := v2602 + v2599
  let v2604 := v2603 + v2595
  let v2605 := s.a.rotateRight 28
  let v2606 := s.a.rotateRight 34
  let v2607 := v2605 ^^^ v2606
  let v2608 := s.a.rotateRight 39
  let v2609 := v2607 ^^^ v2608
  let v2610 := s.a &&& s.b
  let v2611 := s.b ^^^ s.c
  let v2612 := s.a &&& v2611
  let v2613 := v2612 ^^^ (s.b &&& s.c)
  let v2614 := v2609 + v2613
  let v2615 := v2604 + s.d
  let v2616 := v2614 + v2604
  ⟨v2616, s.a, s.b, s.c, v2615, s.e, s.f, s.g⟩

theorem fullOut65_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut65 s w k = Spec.round s (w 65) k := by
  have hw65 := hw 65 (by decide) (by decide)
  dsimp only [fullOut65, Spec.round]
  rw [hw65]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv65_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2578 E (fullEnv65 E s w k) := by
  unfold fullEnv65
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv65_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv65 E s w k) := by
  exact (fullEnv65_before E s w k).frame (by decide)

theorem full_body65 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready65 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 520#64) 64)
    (hk : state.mem.readAt (kp.add 520#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2378 |>.take 39) state =
      .value (fullEnv65 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv65, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w49, h.w50, h.w51, h.w52, h.w53, h.w54, h.w55, h.w56, h.w57, h.w58, h.w59, h.w60, h.w61, h.w62, h.w63, h.w64, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k65, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready65 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready65 E s w) (hw : ScheduleReady w) :
    Ready66 (fullEnv65 E s w k) (Spec.round s (w 65) k) w := by
  have hb := fullEnv65_before E s w k
  have hout := fullOut65_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv65, fullOut65, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2577 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2538 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2499 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv65, fullOut65, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2576 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2537 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2498 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv65, Spec.round, mlir_env]
  · rw [hb.read_val 2005 (by decide) (by rfl)]; exact h.w50
  · rw [hb.read_val 2044 (by decide) (by rfl)]; exact h.w51
  · rw [hb.read_val 2083 (by decide) (by rfl)]; exact h.w52
  · rw [hb.read_val 2122 (by decide) (by rfl)]; exact h.w53
  · rw [hb.read_val 2161 (by decide) (by rfl)]; exact h.w54
  · rw [hb.read_val 2200 (by decide) (by rfl)]; exact h.w55
  · rw [hb.read_val 2239 (by decide) (by rfl)]; exact h.w56
  · rw [hb.read_val 2278 (by decide) (by rfl)]; exact h.w57
  · rw [hb.read_val 2317 (by decide) (by rfl)]; exact h.w58
  · rw [hb.read_val 2356 (by decide) (by rfl)]; exact h.w59
  · rw [hb.read_val 2395 (by decide) (by rfl)]; exact h.w60
  · rw [hb.read_val 2434 (by decide) (by rfl)]; exact h.w61
  · rw [hb.read_val 2473 (by decide) (by rfl)]; exact h.w62
  · rw [hb.read_val 2512 (by decide) (by rfl)]; exact h.w63
  · rw [hb.read_val 2551 (by decide) (by rfl)]; exact h.w64
  · have hwr := hw 65 (by decide) (by decide)
    simp [fullEnv65, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step65 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready65 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2378 |>.take 39) state =
      .value (E', state) ∧
      Ready66 E' (Spec.round s (w 65) (constants.toList.getD 65 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 65 0
  have hf := fullEnv65_frame E s w k
  refine ⟨fullEnv65 E s w k,
    full_body65 E state s w kp k h hc (hk 65).1 (hk 65).2,
    full_ready65 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
