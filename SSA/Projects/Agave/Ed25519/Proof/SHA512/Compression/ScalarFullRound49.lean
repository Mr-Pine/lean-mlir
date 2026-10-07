import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1754..1792: round 49. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv49 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1954 := (w 34).rotateRight 1
  let v1955 := (w 34).rotateRight 8
  let v1956 := v1954 ^^^ v1955
  let v1957 := (w 34) >>> 7
  let v1958 := v1956 ^^^ v1957
  let v1959 := (w 47).rotateRight 19
  let v1960 := (w 47).rotateRight 61
  let v1961 := v1959 ^^^ v1960
  let v1962 := (w 47) >>> 6
  let v1963 := v1961 ^^^ v1962
  let v1964 := v1958 + (w 33)
  let v1965 := v1964 + (w 42)
  let v1966 := v1965 + v1963
  let v1967 := s.e.rotateRight 14
  let v1968 := s.e.rotateRight 18
  let v1969 := v1967 ^^^ v1968
  let v1970 := s.e.rotateRight 41
  let v1971 := v1969 ^^^ v1970
  let v1972 := s.e &&& s.f
  let v1973 := s.e ^^^ (-1 : Word)
  let v1974 := s.g &&& v1973
  let v1975 := v1972 ||| v1974
  let v1976 := k
  let v1977 := v1966 + v1976
  let v1978 := v1977 + s.h
  let v1979 := v1978 + v1975
  let v1980 := v1979 + v1971
  let v1981 := s.a.rotateRight 28
  let v1982 := s.a.rotateRight 34
  let v1983 := v1981 ^^^ v1982
  let v1984 := s.a.rotateRight 39
  let v1985 := v1983 ^^^ v1984
  let v1986 := s.a &&& s.b
  let v1987 := s.b ^^^ s.c
  let v1988 := s.a &&& v1987
  let v1989 := v1988 ^^^ (s.b &&& s.c)
  let v1990 := v1985 + v1989
  let v1991 := v1980 + s.d
  let v1992 := v1990 + v1980
  E[%1954 := .value v1954,
    %1955 := .value v1955,
    %1956 := .value v1956,
    %1957 := .value v1957,
    %1958 := .value v1958,
    %1959 := .value v1959,
    %1960 := .value v1960,
    %1961 := .value v1961,
    %1962 := .value v1962,
    %1963 := .value v1963,
    %1964 := .value v1964,
    %1965 := .value v1965,
    %1966 := .value v1966,
    %1967 := .value v1967,
    %1968 := .value v1968,
    %1969 := .value v1969,
    %1970 := .value v1970,
    %1971 := .value v1971,
    %1972 := .value v1972,
    %1973 := .value v1973,
    %1974 := .value v1974,
    %1975 := .value v1975,
    %1976 := .value v1976,
    %1977 := .value v1977,
    %1978 := .value v1978,
    %1979 := .value v1979,
    %1980 := .value v1980,
    %1981 := .value v1981,
    %1982 := .value v1982,
    %1983 := .value v1983,
    %1984 := .value v1984,
    %1985 := .value v1985,
    %1986 := .value v1986,
    %1987 := .value v1987,
    %1988 := .value v1988,
    %1989 := .value v1989,
    %1990 := .value v1990,
    %1991 := .value v1991,
    %1992 := .value v1992]

def fullOut49 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1954 := (w 34).rotateRight 1
  let v1955 := (w 34).rotateRight 8
  let v1956 := v1954 ^^^ v1955
  let v1957 := (w 34) >>> 7
  let v1958 := v1956 ^^^ v1957
  let v1959 := (w 47).rotateRight 19
  let v1960 := (w 47).rotateRight 61
  let v1961 := v1959 ^^^ v1960
  let v1962 := (w 47) >>> 6
  let v1963 := v1961 ^^^ v1962
  let v1964 := v1958 + (w 33)
  let v1965 := v1964 + (w 42)
  let v1966 := v1965 + v1963
  let v1967 := s.e.rotateRight 14
  let v1968 := s.e.rotateRight 18
  let v1969 := v1967 ^^^ v1968
  let v1970 := s.e.rotateRight 41
  let v1971 := v1969 ^^^ v1970
  let v1972 := s.e &&& s.f
  let v1973 := s.e ^^^ (-1 : Word)
  let v1974 := s.g &&& v1973
  let v1975 := v1972 ||| v1974
  let v1976 := k
  let v1977 := v1966 + v1976
  let v1978 := v1977 + s.h
  let v1979 := v1978 + v1975
  let v1980 := v1979 + v1971
  let v1981 := s.a.rotateRight 28
  let v1982 := s.a.rotateRight 34
  let v1983 := v1981 ^^^ v1982
  let v1984 := s.a.rotateRight 39
  let v1985 := v1983 ^^^ v1984
  let v1986 := s.a &&& s.b
  let v1987 := s.b ^^^ s.c
  let v1988 := s.a &&& v1987
  let v1989 := v1988 ^^^ (s.b &&& s.c)
  let v1990 := v1985 + v1989
  let v1991 := v1980 + s.d
  let v1992 := v1990 + v1980
  ⟨v1992, s.a, s.b, s.c, v1991, s.e, s.f, s.g⟩

theorem fullOut49_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut49 s w k = Spec.round s (w 49) k := by
  have hw49 := hw 49 (by decide) (by decide)
  dsimp only [fullOut49, Spec.round]
  rw [hw49]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv49_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1954 E (fullEnv49 E s w k) := by
  unfold fullEnv49
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv49_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv49 E s w k) := by
  exact (fullEnv49_before E s w k).frame (by decide)

theorem full_body49 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready49 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 392#64) 64)
    (hk : state.mem.readAt (kp.add 392#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1754 |>.take 39) state =
      .value (fullEnv49 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv49, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w33, h.w34, h.w35, h.w36, h.w37, h.w38, h.w39, h.w40, h.w41, h.w42, h.w43, h.w44, h.w45, h.w46, h.w47, h.w48, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k49, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready49 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready49 E s w) (hw : ScheduleReady w) :
    Ready50 (fullEnv49 E s w k) (Spec.round s (w 49) k) w := by
  have hb := fullEnv49_before E s w k
  have hout := fullOut49_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv49, fullOut49, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1953 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1914 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1875 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv49, fullOut49, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1952 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1913 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1874 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv49, Spec.round, mlir_env]
  · rw [hb.read_val 1381 (by decide) (by rfl)]; exact h.w34
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
  · have hwr := hw 49 (by decide) (by decide)
    simp [fullEnv49, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step49 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready49 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1754 |>.take 39) state =
      .value (E', state) ∧
      Ready50 E' (Spec.round s (w 49) (constants.toList.getD 49 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 49 0
  have hf := fullEnv49_frame E s w k
  refine ⟨fullEnv49 E s w k,
    full_body49 E state s w kp k h hc (hk 49).1 (hk 49).2,
    full_ready49 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
