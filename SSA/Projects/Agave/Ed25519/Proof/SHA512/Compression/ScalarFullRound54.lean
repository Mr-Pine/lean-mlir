import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1949..1987: round 54. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv54 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2149 := (w 39).rotateRight 1
  let v2150 := (w 39).rotateRight 8
  let v2151 := v2149 ^^^ v2150
  let v2152 := (w 39) >>> 7
  let v2153 := v2151 ^^^ v2152
  let v2154 := (w 52).rotateRight 19
  let v2155 := (w 52).rotateRight 61
  let v2156 := v2154 ^^^ v2155
  let v2157 := (w 52) >>> 6
  let v2158 := v2156 ^^^ v2157
  let v2159 := v2153 + (w 38)
  let v2160 := v2159 + (w 47)
  let v2161 := v2160 + v2158
  let v2162 := s.e.rotateRight 14
  let v2163 := s.e.rotateRight 18
  let v2164 := v2162 ^^^ v2163
  let v2165 := s.e.rotateRight 41
  let v2166 := v2164 ^^^ v2165
  let v2167 := s.e &&& s.f
  let v2168 := s.e ^^^ (-1 : Word)
  let v2169 := s.g &&& v2168
  let v2170 := v2167 ||| v2169
  let v2171 := k
  let v2172 := v2161 + v2171
  let v2173 := v2172 + s.h
  let v2174 := v2173 + v2170
  let v2175 := v2174 + v2166
  let v2176 := s.a.rotateRight 28
  let v2177 := s.a.rotateRight 34
  let v2178 := v2176 ^^^ v2177
  let v2179 := s.a.rotateRight 39
  let v2180 := v2178 ^^^ v2179
  let v2181 := s.a &&& s.b
  let v2182 := s.b ^^^ s.c
  let v2183 := s.a &&& v2182
  let v2184 := v2183 ^^^ (s.b &&& s.c)
  let v2185 := v2180 + v2184
  let v2186 := v2175 + s.d
  let v2187 := v2185 + v2175
  E[%2149 := .value v2149,
    %2150 := .value v2150,
    %2151 := .value v2151,
    %2152 := .value v2152,
    %2153 := .value v2153,
    %2154 := .value v2154,
    %2155 := .value v2155,
    %2156 := .value v2156,
    %2157 := .value v2157,
    %2158 := .value v2158,
    %2159 := .value v2159,
    %2160 := .value v2160,
    %2161 := .value v2161,
    %2162 := .value v2162,
    %2163 := .value v2163,
    %2164 := .value v2164,
    %2165 := .value v2165,
    %2166 := .value v2166,
    %2167 := .value v2167,
    %2168 := .value v2168,
    %2169 := .value v2169,
    %2170 := .value v2170,
    %2171 := .value v2171,
    %2172 := .value v2172,
    %2173 := .value v2173,
    %2174 := .value v2174,
    %2175 := .value v2175,
    %2176 := .value v2176,
    %2177 := .value v2177,
    %2178 := .value v2178,
    %2179 := .value v2179,
    %2180 := .value v2180,
    %2181 := .value v2181,
    %2182 := .value v2182,
    %2183 := .value v2183,
    %2184 := .value v2184,
    %2185 := .value v2185,
    %2186 := .value v2186,
    %2187 := .value v2187]

def fullOut54 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2149 := (w 39).rotateRight 1
  let v2150 := (w 39).rotateRight 8
  let v2151 := v2149 ^^^ v2150
  let v2152 := (w 39) >>> 7
  let v2153 := v2151 ^^^ v2152
  let v2154 := (w 52).rotateRight 19
  let v2155 := (w 52).rotateRight 61
  let v2156 := v2154 ^^^ v2155
  let v2157 := (w 52) >>> 6
  let v2158 := v2156 ^^^ v2157
  let v2159 := v2153 + (w 38)
  let v2160 := v2159 + (w 47)
  let v2161 := v2160 + v2158
  let v2162 := s.e.rotateRight 14
  let v2163 := s.e.rotateRight 18
  let v2164 := v2162 ^^^ v2163
  let v2165 := s.e.rotateRight 41
  let v2166 := v2164 ^^^ v2165
  let v2167 := s.e &&& s.f
  let v2168 := s.e ^^^ (-1 : Word)
  let v2169 := s.g &&& v2168
  let v2170 := v2167 ||| v2169
  let v2171 := k
  let v2172 := v2161 + v2171
  let v2173 := v2172 + s.h
  let v2174 := v2173 + v2170
  let v2175 := v2174 + v2166
  let v2176 := s.a.rotateRight 28
  let v2177 := s.a.rotateRight 34
  let v2178 := v2176 ^^^ v2177
  let v2179 := s.a.rotateRight 39
  let v2180 := v2178 ^^^ v2179
  let v2181 := s.a &&& s.b
  let v2182 := s.b ^^^ s.c
  let v2183 := s.a &&& v2182
  let v2184 := v2183 ^^^ (s.b &&& s.c)
  let v2185 := v2180 + v2184
  let v2186 := v2175 + s.d
  let v2187 := v2185 + v2175
  ⟨v2187, s.a, s.b, s.c, v2186, s.e, s.f, s.g⟩

theorem fullOut54_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut54 s w k = Spec.round s (w 54) k := by
  have hw54 := hw 54 (by decide) (by decide)
  dsimp only [fullOut54, Spec.round]
  rw [hw54]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv54_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2149 E (fullEnv54 E s w k) := by
  unfold fullEnv54
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv54_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv54 E s w k) := by
  exact (fullEnv54_before E s w k).frame (by decide)

theorem full_body54 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready54 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 432#64) 64)
    (hk : state.mem.readAt (kp.add 432#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1949 |>.take 39) state =
      .value (fullEnv54 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv54, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w38, h.w39, h.w40, h.w41, h.w42, h.w43, h.w44, h.w45, h.w46, h.w47, h.w48, h.w49, h.w50, h.w51, h.w52, h.w53, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k54, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready54 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready54 E s w) (hw : ScheduleReady w) :
    Ready55 (fullEnv54 E s w k) (Spec.round s (w 54) k) w := by
  have hb := fullEnv54_before E s w k
  have hout := fullOut54_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv54, fullOut54, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2148 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2109 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2070 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv54, fullOut54, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2147 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2108 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2069 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv54, Spec.round, mlir_env]
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
  · rw [hb.read_val 2005 (by decide) (by rfl)]; exact h.w50
  · rw [hb.read_val 2044 (by decide) (by rfl)]; exact h.w51
  · rw [hb.read_val 2083 (by decide) (by rfl)]; exact h.w52
  · rw [hb.read_val 2122 (by decide) (by rfl)]; exact h.w53
  · have hwr := hw 54 (by decide) (by decide)
    simp [fullEnv54, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step54 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready54 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1949 |>.take 39) state =
      .value (E', state) ∧
      Ready55 E' (Spec.round s (w 54) (constants.toList.getD 54 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 54 0
  have hf := fullEnv54_frame E s w k
  refine ⟨fullEnv54 E s w k,
    full_body54 E state s w kp k h hc (hk 54).1 (hk 54).2,
    full_ready54 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
