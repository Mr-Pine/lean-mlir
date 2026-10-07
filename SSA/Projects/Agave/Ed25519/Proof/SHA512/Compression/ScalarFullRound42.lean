import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1481..1519: round 42. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv42 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1681 := (w 27).rotateRight 1
  let v1682 := (w 27).rotateRight 8
  let v1683 := v1681 ^^^ v1682
  let v1684 := (w 27) >>> 7
  let v1685 := v1683 ^^^ v1684
  let v1686 := (w 40).rotateRight 19
  let v1687 := (w 40).rotateRight 61
  let v1688 := v1686 ^^^ v1687
  let v1689 := (w 40) >>> 6
  let v1690 := v1688 ^^^ v1689
  let v1691 := v1685 + (w 26)
  let v1692 := v1691 + (w 35)
  let v1693 := v1692 + v1690
  let v1694 := s.e.rotateRight 14
  let v1695 := s.e.rotateRight 18
  let v1696 := v1694 ^^^ v1695
  let v1697 := s.e.rotateRight 41
  let v1698 := v1696 ^^^ v1697
  let v1699 := s.e &&& s.f
  let v1700 := s.e ^^^ (-1 : Word)
  let v1701 := s.g &&& v1700
  let v1702 := v1699 ||| v1701
  let v1703 := k
  let v1704 := v1693 + v1703
  let v1705 := v1704 + s.h
  let v1706 := v1705 + v1702
  let v1707 := v1706 + v1698
  let v1708 := s.a.rotateRight 28
  let v1709 := s.a.rotateRight 34
  let v1710 := v1708 ^^^ v1709
  let v1711 := s.a.rotateRight 39
  let v1712 := v1710 ^^^ v1711
  let v1713 := s.a &&& s.b
  let v1714 := s.b ^^^ s.c
  let v1715 := s.a &&& v1714
  let v1716 := v1715 ^^^ (s.b &&& s.c)
  let v1717 := v1712 + v1716
  let v1718 := v1707 + s.d
  let v1719 := v1717 + v1707
  E[%1681 := .value v1681,
    %1682 := .value v1682,
    %1683 := .value v1683,
    %1684 := .value v1684,
    %1685 := .value v1685,
    %1686 := .value v1686,
    %1687 := .value v1687,
    %1688 := .value v1688,
    %1689 := .value v1689,
    %1690 := .value v1690,
    %1691 := .value v1691,
    %1692 := .value v1692,
    %1693 := .value v1693,
    %1694 := .value v1694,
    %1695 := .value v1695,
    %1696 := .value v1696,
    %1697 := .value v1697,
    %1698 := .value v1698,
    %1699 := .value v1699,
    %1700 := .value v1700,
    %1701 := .value v1701,
    %1702 := .value v1702,
    %1703 := .value v1703,
    %1704 := .value v1704,
    %1705 := .value v1705,
    %1706 := .value v1706,
    %1707 := .value v1707,
    %1708 := .value v1708,
    %1709 := .value v1709,
    %1710 := .value v1710,
    %1711 := .value v1711,
    %1712 := .value v1712,
    %1713 := .value v1713,
    %1714 := .value v1714,
    %1715 := .value v1715,
    %1716 := .value v1716,
    %1717 := .value v1717,
    %1718 := .value v1718,
    %1719 := .value v1719]

def fullOut42 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1681 := (w 27).rotateRight 1
  let v1682 := (w 27).rotateRight 8
  let v1683 := v1681 ^^^ v1682
  let v1684 := (w 27) >>> 7
  let v1685 := v1683 ^^^ v1684
  let v1686 := (w 40).rotateRight 19
  let v1687 := (w 40).rotateRight 61
  let v1688 := v1686 ^^^ v1687
  let v1689 := (w 40) >>> 6
  let v1690 := v1688 ^^^ v1689
  let v1691 := v1685 + (w 26)
  let v1692 := v1691 + (w 35)
  let v1693 := v1692 + v1690
  let v1694 := s.e.rotateRight 14
  let v1695 := s.e.rotateRight 18
  let v1696 := v1694 ^^^ v1695
  let v1697 := s.e.rotateRight 41
  let v1698 := v1696 ^^^ v1697
  let v1699 := s.e &&& s.f
  let v1700 := s.e ^^^ (-1 : Word)
  let v1701 := s.g &&& v1700
  let v1702 := v1699 ||| v1701
  let v1703 := k
  let v1704 := v1693 + v1703
  let v1705 := v1704 + s.h
  let v1706 := v1705 + v1702
  let v1707 := v1706 + v1698
  let v1708 := s.a.rotateRight 28
  let v1709 := s.a.rotateRight 34
  let v1710 := v1708 ^^^ v1709
  let v1711 := s.a.rotateRight 39
  let v1712 := v1710 ^^^ v1711
  let v1713 := s.a &&& s.b
  let v1714 := s.b ^^^ s.c
  let v1715 := s.a &&& v1714
  let v1716 := v1715 ^^^ (s.b &&& s.c)
  let v1717 := v1712 + v1716
  let v1718 := v1707 + s.d
  let v1719 := v1717 + v1707
  ⟨v1719, s.a, s.b, s.c, v1718, s.e, s.f, s.g⟩

theorem fullOut42_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut42 s w k = Spec.round s (w 42) k := by
  have hw42 := hw 42 (by decide) (by decide)
  dsimp only [fullOut42, Spec.round]
  rw [hw42]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv42_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1681 E (fullEnv42 E s w k) := by
  unfold fullEnv42
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv42_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv42 E s w k) := by
  exact (fullEnv42_before E s w k).frame (by decide)

theorem full_body42 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready42 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 336#64) 64)
    (hk : state.mem.readAt (kp.add 336#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1481 |>.take 39) state =
      .value (fullEnv42 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv42, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w26, h.w27, h.w28, h.w29, h.w30, h.w31, h.w32, h.w33, h.w34, h.w35, h.w36, h.w37, h.w38, h.w39, h.w40, h.w41, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k42, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready42 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready42 E s w) (hw : ScheduleReady w) :
    Ready43 (fullEnv42 E s w k) (Spec.round s (w 42) k) w := by
  have hb := fullEnv42_before E s w k
  have hout := fullOut42_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv42, fullOut42, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1680 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1641 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1602 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv42, fullOut42, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1679 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1640 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1601 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv42, Spec.round, mlir_env]
  · rw [hb.read_val 1108 (by decide) (by rfl)]; exact h.w27
  · rw [hb.read_val 1147 (by decide) (by rfl)]; exact h.w28
  · rw [hb.read_val 1186 (by decide) (by rfl)]; exact h.w29
  · rw [hb.read_val 1225 (by decide) (by rfl)]; exact h.w30
  · rw [hb.read_val 1264 (by decide) (by rfl)]; exact h.w31
  · rw [hb.read_val 1303 (by decide) (by rfl)]; exact h.w32
  · rw [hb.read_val 1342 (by decide) (by rfl)]; exact h.w33
  · rw [hb.read_val 1381 (by decide) (by rfl)]; exact h.w34
  · rw [hb.read_val 1420 (by decide) (by rfl)]; exact h.w35
  · rw [hb.read_val 1459 (by decide) (by rfl)]; exact h.w36
  · rw [hb.read_val 1498 (by decide) (by rfl)]; exact h.w37
  · rw [hb.read_val 1537 (by decide) (by rfl)]; exact h.w38
  · rw [hb.read_val 1576 (by decide) (by rfl)]; exact h.w39
  · rw [hb.read_val 1615 (by decide) (by rfl)]; exact h.w40
  · rw [hb.read_val 1654 (by decide) (by rfl)]; exact h.w41
  · have hwr := hw 42 (by decide) (by decide)
    simp [fullEnv42, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step42 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready42 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1481 |>.take 39) state =
      .value (E', state) ∧
      Ready43 E' (Spec.round s (w 42) (constants.toList.getD 42 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 42 0
  have hf := fullEnv42_frame E s w k
  refine ⟨fullEnv42 E s w k,
    full_body42 E state s w kp k h hc (hk 42).1 (hk 42).2,
    full_ready42 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
