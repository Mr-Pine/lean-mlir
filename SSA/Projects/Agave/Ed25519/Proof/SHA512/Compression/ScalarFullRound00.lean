import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 50..76: round 0. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv00 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v250 := s.e.rotateRight 14
  let v251 := s.e.rotateRight 18
  let v252 := v250 ^^^ v251
  let v253 := s.e.rotateRight 41
  let v254 := v252 ^^^ v253
  let v255 := s.e &&& s.f
  let v256 := s.e ^^^ (-1 : Word)
  let v257 := s.g &&& v256
  let v258 := k
  let v259 := v255 + s.h
  let v260 := v259 + v257
  let v261 := v260 + v254
  let v262 := v261 + (w 0)
  let v263 := v262 + v258
  let v264 := s.a.rotateRight 28
  let v265 := s.a.rotateRight 34
  let v266 := v264 ^^^ v265
  let v267 := s.a.rotateRight 39
  let v268 := v266 ^^^ v267
  let v269 := s.a &&& s.b
  let v270 := s.b ^^^ s.c
  let v271 := s.a &&& v270
  let v272 := s.b &&& s.c
  let v273 := v271 ^^^ v272
  let v274 := v268 + v273
  let v275 := v263 + s.d
  let v276 := v274 + v263
  E[%250 := .value v250,
    %251 := .value v251,
    %252 := .value v252,
    %253 := .value v253,
    %254 := .value v254,
    %255 := .value v255,
    %256 := .value v256,
    %257 := .value v257,
    %258 := .value v258,
    %259 := .value v259,
    %260 := .value v260,
    %261 := .value v261,
    %262 := .value v262,
    %263 := .value v263,
    %264 := .value v264,
    %265 := .value v265,
    %266 := .value v266,
    %267 := .value v267,
    %268 := .value v268,
    %269 := .value v269,
    %270 := .value v270,
    %271 := .value v271,
    %272 := .value v272,
    %273 := .value v273,
    %274 := .value v274,
    %275 := .value v275,
    %276 := .value v276]

def fullOut00 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v250 := s.e.rotateRight 14
  let v251 := s.e.rotateRight 18
  let v252 := v250 ^^^ v251
  let v253 := s.e.rotateRight 41
  let v254 := v252 ^^^ v253
  let v255 := s.e &&& s.f
  let v256 := s.e ^^^ (-1 : Word)
  let v257 := s.g &&& v256
  let v258 := k
  let v259 := v255 + s.h
  let v260 := v259 + v257
  let v261 := v260 + v254
  let v262 := v261 + (w 0)
  let v263 := v262 + v258
  let v264 := s.a.rotateRight 28
  let v265 := s.a.rotateRight 34
  let v266 := v264 ^^^ v265
  let v267 := s.a.rotateRight 39
  let v268 := v266 ^^^ v267
  let v269 := s.a &&& s.b
  let v270 := s.b ^^^ s.c
  let v271 := s.a &&& v270
  let v272 := s.b &&& s.c
  let v273 := v271 ^^^ v272
  let v274 := v268 + v273
  let v275 := v263 + s.d
  let v276 := v274 + v263
  ⟨v276, s.a, s.b, s.c, v275, s.e, s.f, s.g⟩

theorem fullOut00_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut00 s w k = Spec.round s (w 0) k := by
  dsimp only [fullOut00, Spec.round]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv00_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 250 E (fullEnv00 E s w k) := by
  unfold fullEnv00
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv00_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv00 E s w k) := by
  exact (fullEnv00_before E s w k).frame (by decide)

theorem full_body00 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready00 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 0#64) 64)
    (hk : state.mem.readAt (kp.add 0#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 50 |>.take 27) state =
      .value (fullEnv00 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv00, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.w0, h.w1, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k00, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready00 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready00 E s w) (hw : ScheduleReady w) :
    Ready01 (fullEnv00 E s w k) (Spec.round s (w 0) k) w := by
  have hb := fullEnv00_before E s w k
  have hout := fullOut00_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv00, fullOut00, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 201 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 199 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 198 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv00, fullOut00, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 196 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 195 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 194 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv00, Spec.round, mlir_env]
  · rw [hb.read_val 204 (by decide) (by rfl)]; exact h.w0
  · rw [hb.read_val 207 (by decide) (by rfl)]; exact h.w1
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

theorem full_step00 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready00 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 50 |>.take 27) state =
      .value (E', state) ∧
      Ready01 E' (Spec.round s (w 0) (constants.toList.getD 0 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 0 0
  have hf := fullEnv00_frame E s w k
  refine ⟨fullEnv00 E s w k,
    full_body00 E state s w kp k h hc (hk 0).1 (hk 0).2,
    full_ready00 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
