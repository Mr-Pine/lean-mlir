import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1364..1402: round 39. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv39 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1564 := (w 24).rotateRight 1
  let v1565 := (w 24).rotateRight 8
  let v1566 := v1564 ^^^ v1565
  let v1567 := (w 24) >>> 7
  let v1568 := v1566 ^^^ v1567
  let v1569 := (w 37).rotateRight 19
  let v1570 := (w 37).rotateRight 61
  let v1571 := v1569 ^^^ v1570
  let v1572 := (w 37) >>> 6
  let v1573 := v1571 ^^^ v1572
  let v1574 := v1568 + (w 23)
  let v1575 := v1574 + (w 32)
  let v1576 := v1575 + v1573
  let v1577 := s.e.rotateRight 14
  let v1578 := s.e.rotateRight 18
  let v1579 := v1577 ^^^ v1578
  let v1580 := s.e.rotateRight 41
  let v1581 := v1579 ^^^ v1580
  let v1582 := s.e &&& s.f
  let v1583 := s.e ^^^ (-1 : Word)
  let v1584 := s.g &&& v1583
  let v1585 := v1582 ||| v1584
  let v1586 := k
  let v1587 := v1576 + v1586
  let v1588 := v1587 + s.h
  let v1589 := v1588 + v1585
  let v1590 := v1589 + v1581
  let v1591 := s.a.rotateRight 28
  let v1592 := s.a.rotateRight 34
  let v1593 := v1591 ^^^ v1592
  let v1594 := s.a.rotateRight 39
  let v1595 := v1593 ^^^ v1594
  let v1596 := s.a &&& s.b
  let v1597 := s.b ^^^ s.c
  let v1598 := s.a &&& v1597
  let v1599 := v1598 ^^^ (s.b &&& s.c)
  let v1600 := v1595 + v1599
  let v1601 := v1590 + s.d
  let v1602 := v1600 + v1590
  E[%1564 := .value v1564,
    %1565 := .value v1565,
    %1566 := .value v1566,
    %1567 := .value v1567,
    %1568 := .value v1568,
    %1569 := .value v1569,
    %1570 := .value v1570,
    %1571 := .value v1571,
    %1572 := .value v1572,
    %1573 := .value v1573,
    %1574 := .value v1574,
    %1575 := .value v1575,
    %1576 := .value v1576,
    %1577 := .value v1577,
    %1578 := .value v1578,
    %1579 := .value v1579,
    %1580 := .value v1580,
    %1581 := .value v1581,
    %1582 := .value v1582,
    %1583 := .value v1583,
    %1584 := .value v1584,
    %1585 := .value v1585,
    %1586 := .value v1586,
    %1587 := .value v1587,
    %1588 := .value v1588,
    %1589 := .value v1589,
    %1590 := .value v1590,
    %1591 := .value v1591,
    %1592 := .value v1592,
    %1593 := .value v1593,
    %1594 := .value v1594,
    %1595 := .value v1595,
    %1596 := .value v1596,
    %1597 := .value v1597,
    %1598 := .value v1598,
    %1599 := .value v1599,
    %1600 := .value v1600,
    %1601 := .value v1601,
    %1602 := .value v1602]

def fullOut39 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1564 := (w 24).rotateRight 1
  let v1565 := (w 24).rotateRight 8
  let v1566 := v1564 ^^^ v1565
  let v1567 := (w 24) >>> 7
  let v1568 := v1566 ^^^ v1567
  let v1569 := (w 37).rotateRight 19
  let v1570 := (w 37).rotateRight 61
  let v1571 := v1569 ^^^ v1570
  let v1572 := (w 37) >>> 6
  let v1573 := v1571 ^^^ v1572
  let v1574 := v1568 + (w 23)
  let v1575 := v1574 + (w 32)
  let v1576 := v1575 + v1573
  let v1577 := s.e.rotateRight 14
  let v1578 := s.e.rotateRight 18
  let v1579 := v1577 ^^^ v1578
  let v1580 := s.e.rotateRight 41
  let v1581 := v1579 ^^^ v1580
  let v1582 := s.e &&& s.f
  let v1583 := s.e ^^^ (-1 : Word)
  let v1584 := s.g &&& v1583
  let v1585 := v1582 ||| v1584
  let v1586 := k
  let v1587 := v1576 + v1586
  let v1588 := v1587 + s.h
  let v1589 := v1588 + v1585
  let v1590 := v1589 + v1581
  let v1591 := s.a.rotateRight 28
  let v1592 := s.a.rotateRight 34
  let v1593 := v1591 ^^^ v1592
  let v1594 := s.a.rotateRight 39
  let v1595 := v1593 ^^^ v1594
  let v1596 := s.a &&& s.b
  let v1597 := s.b ^^^ s.c
  let v1598 := s.a &&& v1597
  let v1599 := v1598 ^^^ (s.b &&& s.c)
  let v1600 := v1595 + v1599
  let v1601 := v1590 + s.d
  let v1602 := v1600 + v1590
  ⟨v1602, s.a, s.b, s.c, v1601, s.e, s.f, s.g⟩

theorem fullOut39_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut39 s w k = Spec.round s (w 39) k := by
  have hw39 := hw 39 (by decide) (by decide)
  dsimp only [fullOut39, Spec.round]
  rw [hw39]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv39_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1564 E (fullEnv39 E s w k) := by
  unfold fullEnv39
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv39_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv39 E s w k) := by
  exact (fullEnv39_before E s w k).frame (by decide)

theorem full_body39 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready39 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 312#64) 64)
    (hk : state.mem.readAt (kp.add 312#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1364 |>.take 39) state =
      .value (fullEnv39 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv39, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w23, h.w24, h.w25, h.w26, h.w27, h.w28, h.w29, h.w30, h.w31, h.w32, h.w33, h.w34, h.w35, h.w36, h.w37, h.w38, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k39, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready39 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready39 E s w) (hw : ScheduleReady w) :
    Ready40 (fullEnv39 E s w k) (Spec.round s (w 39) k) w := by
  have hb := fullEnv39_before E s w k
  have hout := fullOut39_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv39, fullOut39, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1563 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1524 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1485 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv39, fullOut39, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1562 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1523 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1484 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv39, Spec.round, mlir_env]
  · rw [hb.read_val 991 (by decide) (by rfl)]; exact h.w24
  · rw [hb.read_val 1030 (by decide) (by rfl)]; exact h.w25
  · rw [hb.read_val 1069 (by decide) (by rfl)]; exact h.w26
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
  · have hwr := hw 39 (by decide) (by decide)
    simp [fullEnv39, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step39 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready39 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1364 |>.take 39) state =
      .value (E', state) ∧
      Ready40 E' (Spec.round s (w 39) (constants.toList.getD 39 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 39 0
  have hf := fullEnv39_frame E s w k
  refine ⟨fullEnv39 E s w k,
    full_body39 E state s w kp k h hc (hk 39).1 (hk 39).2,
    full_ready39 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
