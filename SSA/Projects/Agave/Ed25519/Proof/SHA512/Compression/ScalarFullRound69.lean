import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2534..2572: round 69. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv69 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2734 := (w 54).rotateRight 1
  let v2735 := (w 54).rotateRight 8
  let v2736 := v2734 ^^^ v2735
  let v2737 := (w 54) >>> 7
  let v2738 := v2736 ^^^ v2737
  let v2739 := (w 67).rotateRight 19
  let v2740 := (w 67).rotateRight 61
  let v2741 := v2739 ^^^ v2740
  let v2742 := (w 67) >>> 6
  let v2743 := v2741 ^^^ v2742
  let v2744 := v2738 + (w 53)
  let v2745 := v2744 + (w 62)
  let v2746 := v2745 + v2743
  let v2747 := s.e.rotateRight 14
  let v2748 := s.e.rotateRight 18
  let v2749 := v2747 ^^^ v2748
  let v2750 := s.e.rotateRight 41
  let v2751 := v2749 ^^^ v2750
  let v2752 := s.e &&& s.f
  let v2753 := s.e ^^^ (-1 : Word)
  let v2754 := s.g &&& v2753
  let v2755 := v2752 ||| v2754
  let v2756 := k
  let v2757 := v2746 + v2756
  let v2758 := v2757 + s.h
  let v2759 := v2758 + v2755
  let v2760 := v2759 + v2751
  let v2761 := s.a.rotateRight 28
  let v2762 := s.a.rotateRight 34
  let v2763 := v2761 ^^^ v2762
  let v2764 := s.a.rotateRight 39
  let v2765 := v2763 ^^^ v2764
  let v2766 := s.a &&& s.b
  let v2767 := s.b ^^^ s.c
  let v2768 := s.a &&& v2767
  let v2769 := v2768 ^^^ (s.b &&& s.c)
  let v2770 := v2765 + v2769
  let v2771 := v2760 + s.d
  let v2772 := v2770 + v2760
  E[%2734 := .value v2734,
    %2735 := .value v2735,
    %2736 := .value v2736,
    %2737 := .value v2737,
    %2738 := .value v2738,
    %2739 := .value v2739,
    %2740 := .value v2740,
    %2741 := .value v2741,
    %2742 := .value v2742,
    %2743 := .value v2743,
    %2744 := .value v2744,
    %2745 := .value v2745,
    %2746 := .value v2746,
    %2747 := .value v2747,
    %2748 := .value v2748,
    %2749 := .value v2749,
    %2750 := .value v2750,
    %2751 := .value v2751,
    %2752 := .value v2752,
    %2753 := .value v2753,
    %2754 := .value v2754,
    %2755 := .value v2755,
    %2756 := .value v2756,
    %2757 := .value v2757,
    %2758 := .value v2758,
    %2759 := .value v2759,
    %2760 := .value v2760,
    %2761 := .value v2761,
    %2762 := .value v2762,
    %2763 := .value v2763,
    %2764 := .value v2764,
    %2765 := .value v2765,
    %2766 := .value v2766,
    %2767 := .value v2767,
    %2768 := .value v2768,
    %2769 := .value v2769,
    %2770 := .value v2770,
    %2771 := .value v2771,
    %2772 := .value v2772]

def fullOut69 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2734 := (w 54).rotateRight 1
  let v2735 := (w 54).rotateRight 8
  let v2736 := v2734 ^^^ v2735
  let v2737 := (w 54) >>> 7
  let v2738 := v2736 ^^^ v2737
  let v2739 := (w 67).rotateRight 19
  let v2740 := (w 67).rotateRight 61
  let v2741 := v2739 ^^^ v2740
  let v2742 := (w 67) >>> 6
  let v2743 := v2741 ^^^ v2742
  let v2744 := v2738 + (w 53)
  let v2745 := v2744 + (w 62)
  let v2746 := v2745 + v2743
  let v2747 := s.e.rotateRight 14
  let v2748 := s.e.rotateRight 18
  let v2749 := v2747 ^^^ v2748
  let v2750 := s.e.rotateRight 41
  let v2751 := v2749 ^^^ v2750
  let v2752 := s.e &&& s.f
  let v2753 := s.e ^^^ (-1 : Word)
  let v2754 := s.g &&& v2753
  let v2755 := v2752 ||| v2754
  let v2756 := k
  let v2757 := v2746 + v2756
  let v2758 := v2757 + s.h
  let v2759 := v2758 + v2755
  let v2760 := v2759 + v2751
  let v2761 := s.a.rotateRight 28
  let v2762 := s.a.rotateRight 34
  let v2763 := v2761 ^^^ v2762
  let v2764 := s.a.rotateRight 39
  let v2765 := v2763 ^^^ v2764
  let v2766 := s.a &&& s.b
  let v2767 := s.b ^^^ s.c
  let v2768 := s.a &&& v2767
  let v2769 := v2768 ^^^ (s.b &&& s.c)
  let v2770 := v2765 + v2769
  let v2771 := v2760 + s.d
  let v2772 := v2770 + v2760
  ⟨v2772, s.a, s.b, s.c, v2771, s.e, s.f, s.g⟩

theorem fullOut69_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut69 s w k = Spec.round s (w 69) k := by
  have hw69 := hw 69 (by decide) (by decide)
  dsimp only [fullOut69, Spec.round]
  rw [hw69]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv69_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2734 E (fullEnv69 E s w k) := by
  unfold fullEnv69
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv69_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv69 E s w k) := by
  exact (fullEnv69_before E s w k).frame (by decide)

theorem full_body69 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready69 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 552#64) 64)
    (hk : state.mem.readAt (kp.add 552#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2534 |>.take 39) state =
      .value (fullEnv69 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv69, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w53, h.w54, h.w55, h.w56, h.w57, h.w58, h.w59, h.w60, h.w61, h.w62, h.w63, h.w64, h.w65, h.w66, h.w67, h.w68, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k69, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready69 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready69 E s w) (hw : ScheduleReady w) :
    Ready70 (fullEnv69 E s w k) (Spec.round s (w 69) k) w := by
  have hb := fullEnv69_before E s w k
  have hout := fullOut69_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv69, fullOut69, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2733 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2694 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2655 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv69, fullOut69, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2732 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2693 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2654 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv69, Spec.round, mlir_env]
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
  · rw [hb.read_val 2668 (by decide) (by rfl)]; exact h.w67
  · rw [hb.read_val 2707 (by decide) (by rfl)]; exact h.w68
  · have hwr := hw 69 (by decide) (by decide)
    simp [fullEnv69, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step69 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready69 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2534 |>.take 39) state =
      .value (E', state) ∧
      Ready70 E' (Spec.round s (w 69) (constants.toList.getD 69 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 69 0
  have hf := fullEnv69_frame E s w k
  refine ⟨fullEnv69 E s w k,
    full_body69 E state s w kp k h hc (hk 69).1 (hk 69).2,
    full_ready69 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
