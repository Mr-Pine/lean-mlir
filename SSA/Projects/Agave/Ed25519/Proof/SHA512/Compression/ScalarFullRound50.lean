import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1793..1831: round 50. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv50 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1993 := (w 35).rotateRight 1
  let v1994 := (w 35).rotateRight 8
  let v1995 := v1993 ^^^ v1994
  let v1996 := (w 35) >>> 7
  let v1997 := v1995 ^^^ v1996
  let v1998 := (w 48).rotateRight 19
  let v1999 := (w 48).rotateRight 61
  let v2000 := v1998 ^^^ v1999
  let v2001 := (w 48) >>> 6
  let v2002 := v2000 ^^^ v2001
  let v2003 := v1997 + (w 34)
  let v2004 := v2003 + (w 43)
  let v2005 := v2004 + v2002
  let v2006 := s.e.rotateRight 14
  let v2007 := s.e.rotateRight 18
  let v2008 := v2006 ^^^ v2007
  let v2009 := s.e.rotateRight 41
  let v2010 := v2008 ^^^ v2009
  let v2011 := s.e &&& s.f
  let v2012 := s.e ^^^ (-1 : Word)
  let v2013 := s.g &&& v2012
  let v2014 := v2011 ||| v2013
  let v2015 := k
  let v2016 := v2005 + v2015
  let v2017 := v2016 + s.h
  let v2018 := v2017 + v2014
  let v2019 := v2018 + v2010
  let v2020 := s.a.rotateRight 28
  let v2021 := s.a.rotateRight 34
  let v2022 := v2020 ^^^ v2021
  let v2023 := s.a.rotateRight 39
  let v2024 := v2022 ^^^ v2023
  let v2025 := s.a &&& s.b
  let v2026 := s.b ^^^ s.c
  let v2027 := s.a &&& v2026
  let v2028 := v2027 ^^^ (s.b &&& s.c)
  let v2029 := v2024 + v2028
  let v2030 := v2019 + s.d
  let v2031 := v2029 + v2019
  E[%1993 := .value v1993,
    %1994 := .value v1994,
    %1995 := .value v1995,
    %1996 := .value v1996,
    %1997 := .value v1997,
    %1998 := .value v1998,
    %1999 := .value v1999,
    %2000 := .value v2000,
    %2001 := .value v2001,
    %2002 := .value v2002,
    %2003 := .value v2003,
    %2004 := .value v2004,
    %2005 := .value v2005,
    %2006 := .value v2006,
    %2007 := .value v2007,
    %2008 := .value v2008,
    %2009 := .value v2009,
    %2010 := .value v2010,
    %2011 := .value v2011,
    %2012 := .value v2012,
    %2013 := .value v2013,
    %2014 := .value v2014,
    %2015 := .value v2015,
    %2016 := .value v2016,
    %2017 := .value v2017,
    %2018 := .value v2018,
    %2019 := .value v2019,
    %2020 := .value v2020,
    %2021 := .value v2021,
    %2022 := .value v2022,
    %2023 := .value v2023,
    %2024 := .value v2024,
    %2025 := .value v2025,
    %2026 := .value v2026,
    %2027 := .value v2027,
    %2028 := .value v2028,
    %2029 := .value v2029,
    %2030 := .value v2030,
    %2031 := .value v2031]

def fullOut50 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1993 := (w 35).rotateRight 1
  let v1994 := (w 35).rotateRight 8
  let v1995 := v1993 ^^^ v1994
  let v1996 := (w 35) >>> 7
  let v1997 := v1995 ^^^ v1996
  let v1998 := (w 48).rotateRight 19
  let v1999 := (w 48).rotateRight 61
  let v2000 := v1998 ^^^ v1999
  let v2001 := (w 48) >>> 6
  let v2002 := v2000 ^^^ v2001
  let v2003 := v1997 + (w 34)
  let v2004 := v2003 + (w 43)
  let v2005 := v2004 + v2002
  let v2006 := s.e.rotateRight 14
  let v2007 := s.e.rotateRight 18
  let v2008 := v2006 ^^^ v2007
  let v2009 := s.e.rotateRight 41
  let v2010 := v2008 ^^^ v2009
  let v2011 := s.e &&& s.f
  let v2012 := s.e ^^^ (-1 : Word)
  let v2013 := s.g &&& v2012
  let v2014 := v2011 ||| v2013
  let v2015 := k
  let v2016 := v2005 + v2015
  let v2017 := v2016 + s.h
  let v2018 := v2017 + v2014
  let v2019 := v2018 + v2010
  let v2020 := s.a.rotateRight 28
  let v2021 := s.a.rotateRight 34
  let v2022 := v2020 ^^^ v2021
  let v2023 := s.a.rotateRight 39
  let v2024 := v2022 ^^^ v2023
  let v2025 := s.a &&& s.b
  let v2026 := s.b ^^^ s.c
  let v2027 := s.a &&& v2026
  let v2028 := v2027 ^^^ (s.b &&& s.c)
  let v2029 := v2024 + v2028
  let v2030 := v2019 + s.d
  let v2031 := v2029 + v2019
  ⟨v2031, s.a, s.b, s.c, v2030, s.e, s.f, s.g⟩

theorem fullOut50_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut50 s w k = Spec.round s (w 50) k := by
  have hw50 := hw 50 (by decide) (by decide)
  dsimp only [fullOut50, Spec.round]
  rw [hw50]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv50_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1993 E (fullEnv50 E s w k) := by
  unfold fullEnv50
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv50_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv50 E s w k) := by
  exact (fullEnv50_before E s w k).frame (by decide)

theorem full_body50 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready50 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 400#64) 64)
    (hk : state.mem.readAt (kp.add 400#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1793 |>.take 39) state =
      .value (fullEnv50 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv50, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w34, h.w35, h.w36, h.w37, h.w38, h.w39, h.w40, h.w41, h.w42, h.w43, h.w44, h.w45, h.w46, h.w47, h.w48, h.w49, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k50, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready50 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready50 E s w) (hw : ScheduleReady w) :
    Ready51 (fullEnv50 E s w k) (Spec.round s (w 50) k) w := by
  have hb := fullEnv50_before E s w k
  have hout := fullOut50_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv50, fullOut50, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1992 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1953 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1914 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv50, fullOut50, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1991 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1952 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1913 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv50, Spec.round, mlir_env]
  · rw [hb.read_val 1420 (by decide) (by rfl)]; exact h.w35
  · rw [hb.read_val 1459 (by decide) (by rfl)]; exact h.w36
  · rw [hb.read_val 1498 (by decide) (by rfl)]; exact h.w37
  · rw [hb.read_val 1537 (by decide) (by rfl)]; exact h.w38
  · rw [hb.read_val 1576 (by decide) (by rfl)]; exact h.w39
  · rw [hb.read_val 1615 (by decide) (by rfl)]; exact h.w40
  · rw [hb.read_val 1654 (by decide) (by rfl)]; exact h.w41
  · rw [hb.read_val 1693 (by decide) (by rfl)]; exact h.w42
  · rw [hb.read_val 1732 (by decide) (by rfl)]; exact h.w43
  · rw [hb.read_val 1771 (by decide) (by rfl)]; exact h.w44
  · rw [hb.read_val 1810 (by decide) (by rfl)]; exact h.w45
  · rw [hb.read_val 1849 (by decide) (by rfl)]; exact h.w46
  · rw [hb.read_val 1888 (by decide) (by rfl)]; exact h.w47
  · rw [hb.read_val 1927 (by decide) (by rfl)]; exact h.w48
  · rw [hb.read_val 1966 (by decide) (by rfl)]; exact h.w49
  · have hwr := hw 50 (by decide) (by decide)
    simp [fullEnv50, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step50 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready50 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1793 |>.take 39) state =
      .value (E', state) ∧
      Ready51 E' (Spec.round s (w 50) (constants.toList.getD 50 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 50 0
  have hf := fullEnv50_frame E s w k
  refine ⟨fullEnv50 E s w k,
    full_body50 E state s w kp k h hc (hk 50).1 (hk 50).2,
    full_ready50 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
