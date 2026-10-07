import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 506..544: round 17. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv17 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v706 := (w 2).rotateRight 1
  let v707 := (w 2).rotateRight 8
  let v708 := v706 ^^^ v707
  let v709 := (w 2) >>> 7
  let v710 := v708 ^^^ v709
  let v711 := (w 15).rotateRight 19
  let v712 := (w 15).rotateRight 61
  let v713 := v711 ^^^ v712
  let v714 := (w 15) >>> 6
  let v715 := v713 ^^^ v714
  let v716 := v710 + (w 1)
  let v717 := v716 + (w 10)
  let v718 := v717 + v715
  let v719 := s.e.rotateRight 14
  let v720 := s.e.rotateRight 18
  let v721 := v719 ^^^ v720
  let v722 := s.e.rotateRight 41
  let v723 := v721 ^^^ v722
  let v724 := s.e &&& s.f
  let v725 := s.e ^^^ (-1 : Word)
  let v726 := s.g &&& v725
  let v727 := v724 ||| v726
  let v728 := k
  let v729 := v728 + v718
  let v730 := v729 + s.h
  let v731 := v730 + v727
  let v732 := v731 + v723
  let v733 := s.a.rotateRight 28
  let v734 := s.a.rotateRight 34
  let v735 := v733 ^^^ v734
  let v736 := s.a.rotateRight 39
  let v737 := v735 ^^^ v736
  let v738 := s.a &&& s.b
  let v739 := s.b ^^^ s.c
  let v740 := s.a &&& v739
  let v741 := v740 ^^^ (s.b &&& s.c)
  let v742 := v737 + v741
  let v743 := v732 + s.d
  let v744 := v742 + v732
  E[%706 := .value v706,
    %707 := .value v707,
    %708 := .value v708,
    %709 := .value v709,
    %710 := .value v710,
    %711 := .value v711,
    %712 := .value v712,
    %713 := .value v713,
    %714 := .value v714,
    %715 := .value v715,
    %716 := .value v716,
    %717 := .value v717,
    %718 := .value v718,
    %719 := .value v719,
    %720 := .value v720,
    %721 := .value v721,
    %722 := .value v722,
    %723 := .value v723,
    %724 := .value v724,
    %725 := .value v725,
    %726 := .value v726,
    %727 := .value v727,
    %728 := .value v728,
    %729 := .value v729,
    %730 := .value v730,
    %731 := .value v731,
    %732 := .value v732,
    %733 := .value v733,
    %734 := .value v734,
    %735 := .value v735,
    %736 := .value v736,
    %737 := .value v737,
    %738 := .value v738,
    %739 := .value v739,
    %740 := .value v740,
    %741 := .value v741,
    %742 := .value v742,
    %743 := .value v743,
    %744 := .value v744]

def fullOut17 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v706 := (w 2).rotateRight 1
  let v707 := (w 2).rotateRight 8
  let v708 := v706 ^^^ v707
  let v709 := (w 2) >>> 7
  let v710 := v708 ^^^ v709
  let v711 := (w 15).rotateRight 19
  let v712 := (w 15).rotateRight 61
  let v713 := v711 ^^^ v712
  let v714 := (w 15) >>> 6
  let v715 := v713 ^^^ v714
  let v716 := v710 + (w 1)
  let v717 := v716 + (w 10)
  let v718 := v717 + v715
  let v719 := s.e.rotateRight 14
  let v720 := s.e.rotateRight 18
  let v721 := v719 ^^^ v720
  let v722 := s.e.rotateRight 41
  let v723 := v721 ^^^ v722
  let v724 := s.e &&& s.f
  let v725 := s.e ^^^ (-1 : Word)
  let v726 := s.g &&& v725
  let v727 := v724 ||| v726
  let v728 := k
  let v729 := v728 + v718
  let v730 := v729 + s.h
  let v731 := v730 + v727
  let v732 := v731 + v723
  let v733 := s.a.rotateRight 28
  let v734 := s.a.rotateRight 34
  let v735 := v733 ^^^ v734
  let v736 := s.a.rotateRight 39
  let v737 := v735 ^^^ v736
  let v738 := s.a &&& s.b
  let v739 := s.b ^^^ s.c
  let v740 := s.a &&& v739
  let v741 := v740 ^^^ (s.b &&& s.c)
  let v742 := v737 + v741
  let v743 := v732 + s.d
  let v744 := v742 + v732
  ⟨v744, s.a, s.b, s.c, v743, s.e, s.f, s.g⟩

theorem fullOut17_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut17 s w k = Spec.round s (w 17) k := by
  have hw17 := hw 17 (by decide) (by decide)
  dsimp only [fullOut17, Spec.round]
  rw [hw17]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv17_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 706 E (fullEnv17 E s w k) := by
  unfold fullEnv17
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv17_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv17 E s w k) := by
  exact (fullEnv17_before E s w k).frame (by decide)

theorem full_body17 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready17 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 136#64) 64)
    (hk : state.mem.readAt (kp.add 136#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 506 |>.take 39) state =
      .value (fullEnv17 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv17, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w1, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, h.w16, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k17, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready17 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready17 E s w) (hw : ScheduleReady w) :
    Ready18 (fullEnv17 E s w k) (Spec.round s (w 17) k) w := by
  have hb := fullEnv17_before E s w k
  have hout := fullOut17_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv17, fullOut17, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 705 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 666 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 640 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv17, fullOut17, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 704 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 665 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 639 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv17, Spec.round, mlir_env]
  · rw [hb.read_val 210 (by decide) (by rfl)]; exact h.w2
  · rw [hb.read_val 213 (by decide) (by rfl)]; exact h.w3
  · rw [hb.read_val 216 (by decide) (by rfl)]; exact h.w4
  · rw [hb.read_val 219 (by decide) (by rfl)]; exact h.w5
  · rw [hb.read_val 222 (by decide) (by rfl)]; exact h.w6
  · rw [hb.read_val 225 (by decide) (by rfl)]; exact h.w7
  · rw [hb.read_val 228 (by decide) (by rfl)]; exact h.w8
  · rw [hb.read_val 231 (by decide) (by rfl)]; exact h.w9
  · rw [hb.read_val 234 (by decide) (by rfl)]; exact h.w10
  · rw [hb.read_val 237 (by decide) (by rfl)]; exact h.w11
  · rw [hb.read_val 240 (by decide) (by rfl)]; exact h.w12
  · rw [hb.read_val 243 (by decide) (by rfl)]; exact h.w13
  · rw [hb.read_val 246 (by decide) (by rfl)]; exact h.w14
  · rw [hb.read_val 249 (by decide) (by rfl)]; exact h.w15
  · rw [hb.read_val 679 (by decide) (by rfl)]; exact h.w16
  · have hwr := hw 17 (by decide) (by decide)
    simp [fullEnv17, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step17 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready17 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 506 |>.take 39) state =
      .value (E', state) ∧
      Ready18 E' (Spec.round s (w 17) (constants.toList.getD 17 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 17 0
  have hf := fullEnv17_frame E s w k
  refine ⟨fullEnv17 E s w k,
    full_body17 E state s w kp k h hc (hk 17).1 (hk 17).2,
    full_ready17 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
