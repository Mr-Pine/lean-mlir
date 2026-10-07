import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2456..2494: round 67. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv67 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2656 := (w 52).rotateRight 1
  let v2657 := (w 52).rotateRight 8
  let v2658 := v2656 ^^^ v2657
  let v2659 := (w 52) >>> 7
  let v2660 := v2658 ^^^ v2659
  let v2661 := (w 65).rotateRight 19
  let v2662 := (w 65).rotateRight 61
  let v2663 := v2661 ^^^ v2662
  let v2664 := (w 65) >>> 6
  let v2665 := v2663 ^^^ v2664
  let v2666 := v2660 + (w 51)
  let v2667 := v2666 + (w 60)
  let v2668 := v2667 + v2665
  let v2669 := s.e.rotateRight 14
  let v2670 := s.e.rotateRight 18
  let v2671 := v2669 ^^^ v2670
  let v2672 := s.e.rotateRight 41
  let v2673 := v2671 ^^^ v2672
  let v2674 := s.e &&& s.f
  let v2675 := s.e ^^^ (-1 : Word)
  let v2676 := s.g &&& v2675
  let v2677 := v2674 ||| v2676
  let v2678 := k
  let v2679 := v2668 + v2678
  let v2680 := v2679 + s.h
  let v2681 := v2680 + v2677
  let v2682 := v2681 + v2673
  let v2683 := s.a.rotateRight 28
  let v2684 := s.a.rotateRight 34
  let v2685 := v2683 ^^^ v2684
  let v2686 := s.a.rotateRight 39
  let v2687 := v2685 ^^^ v2686
  let v2688 := s.a &&& s.b
  let v2689 := s.b ^^^ s.c
  let v2690 := s.a &&& v2689
  let v2691 := v2690 ^^^ (s.b &&& s.c)
  let v2692 := v2687 + v2691
  let v2693 := v2682 + s.d
  let v2694 := v2692 + v2682
  E[%2656 := .value v2656,
    %2657 := .value v2657,
    %2658 := .value v2658,
    %2659 := .value v2659,
    %2660 := .value v2660,
    %2661 := .value v2661,
    %2662 := .value v2662,
    %2663 := .value v2663,
    %2664 := .value v2664,
    %2665 := .value v2665,
    %2666 := .value v2666,
    %2667 := .value v2667,
    %2668 := .value v2668,
    %2669 := .value v2669,
    %2670 := .value v2670,
    %2671 := .value v2671,
    %2672 := .value v2672,
    %2673 := .value v2673,
    %2674 := .value v2674,
    %2675 := .value v2675,
    %2676 := .value v2676,
    %2677 := .value v2677,
    %2678 := .value v2678,
    %2679 := .value v2679,
    %2680 := .value v2680,
    %2681 := .value v2681,
    %2682 := .value v2682,
    %2683 := .value v2683,
    %2684 := .value v2684,
    %2685 := .value v2685,
    %2686 := .value v2686,
    %2687 := .value v2687,
    %2688 := .value v2688,
    %2689 := .value v2689,
    %2690 := .value v2690,
    %2691 := .value v2691,
    %2692 := .value v2692,
    %2693 := .value v2693,
    %2694 := .value v2694]

def fullOut67 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2656 := (w 52).rotateRight 1
  let v2657 := (w 52).rotateRight 8
  let v2658 := v2656 ^^^ v2657
  let v2659 := (w 52) >>> 7
  let v2660 := v2658 ^^^ v2659
  let v2661 := (w 65).rotateRight 19
  let v2662 := (w 65).rotateRight 61
  let v2663 := v2661 ^^^ v2662
  let v2664 := (w 65) >>> 6
  let v2665 := v2663 ^^^ v2664
  let v2666 := v2660 + (w 51)
  let v2667 := v2666 + (w 60)
  let v2668 := v2667 + v2665
  let v2669 := s.e.rotateRight 14
  let v2670 := s.e.rotateRight 18
  let v2671 := v2669 ^^^ v2670
  let v2672 := s.e.rotateRight 41
  let v2673 := v2671 ^^^ v2672
  let v2674 := s.e &&& s.f
  let v2675 := s.e ^^^ (-1 : Word)
  let v2676 := s.g &&& v2675
  let v2677 := v2674 ||| v2676
  let v2678 := k
  let v2679 := v2668 + v2678
  let v2680 := v2679 + s.h
  let v2681 := v2680 + v2677
  let v2682 := v2681 + v2673
  let v2683 := s.a.rotateRight 28
  let v2684 := s.a.rotateRight 34
  let v2685 := v2683 ^^^ v2684
  let v2686 := s.a.rotateRight 39
  let v2687 := v2685 ^^^ v2686
  let v2688 := s.a &&& s.b
  let v2689 := s.b ^^^ s.c
  let v2690 := s.a &&& v2689
  let v2691 := v2690 ^^^ (s.b &&& s.c)
  let v2692 := v2687 + v2691
  let v2693 := v2682 + s.d
  let v2694 := v2692 + v2682
  ⟨v2694, s.a, s.b, s.c, v2693, s.e, s.f, s.g⟩

theorem fullOut67_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut67 s w k = Spec.round s (w 67) k := by
  have hw67 := hw 67 (by decide) (by decide)
  dsimp only [fullOut67, Spec.round]
  rw [hw67]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv67_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2656 E (fullEnv67 E s w k) := by
  unfold fullEnv67
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv67_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv67 E s w k) := by
  exact (fullEnv67_before E s w k).frame (by decide)

theorem full_body67 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready67 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 536#64) 64)
    (hk : state.mem.readAt (kp.add 536#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2456 |>.take 39) state =
      .value (fullEnv67 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv67, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w51, h.w52, h.w53, h.w54, h.w55, h.w56, h.w57, h.w58, h.w59, h.w60, h.w61, h.w62, h.w63, h.w64, h.w65, h.w66, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k67, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready67 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready67 E s w) (hw : ScheduleReady w) :
    Ready68 (fullEnv67 E s w k) (Spec.round s (w 67) k) w := by
  have hb := fullEnv67_before E s w k
  have hout := fullOut67_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv67, fullOut67, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2655 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2616 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2577 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv67, fullOut67, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2654 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2615 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2576 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv67, Spec.round, mlir_env]
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
  · rw [hb.read_val 2590 (by decide) (by rfl)]; exact h.w65
  · rw [hb.read_val 2629 (by decide) (by rfl)]; exact h.w66
  · have hwr := hw 67 (by decide) (by decide)
    simp [fullEnv67, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step67 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready67 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2456 |>.take 39) state =
      .value (E', state) ∧
      Ready68 E' (Spec.round s (w 67) (constants.toList.getD 67 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 67 0
  have hf := fullEnv67_frame E s w k
  refine ⟨fullEnv67 E s w k,
    full_body67 E state s w kp k h hc (hk 67).1 (hk 67).2,
    full_ready67 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
