import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 129..154: round 3. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv03 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v329 := s.e.rotateRight 14
  let v330 := s.e.rotateRight 18
  let v331 := v329 ^^^ v330
  let v332 := s.e.rotateRight 41
  let v333 := v331 ^^^ v332
  let v334 := s.e &&& s.f
  let v335 := s.e ^^^ (-1 : Word)
  let v336 := s.g &&& v335
  let v337 := k
  let v338 := (w 3) + s.h
  let v339 := v338 + v337
  let v340 := v339 + v336
  let v341 := v340 + v334
  let v342 := v341 + v333
  let v343 := s.a.rotateRight 28
  let v344 := s.a.rotateRight 34
  let v345 := v343 ^^^ v344
  let v346 := s.a.rotateRight 39
  let v347 := v345 ^^^ v346
  let v348 := s.a &&& s.b
  let v349 := s.b ^^^ s.c
  let v350 := s.a &&& v349
  let v351 := v350 ^^^ (s.b &&& s.c)
  let v352 := v347 + v351
  let v353 := v342 + s.d
  let v354 := v352 + v342
  E[%329 := .value v329,
    %330 := .value v330,
    %331 := .value v331,
    %332 := .value v332,
    %333 := .value v333,
    %334 := .value v334,
    %335 := .value v335,
    %336 := .value v336,
    %337 := .value v337,
    %338 := .value v338,
    %339 := .value v339,
    %340 := .value v340,
    %341 := .value v341,
    %342 := .value v342,
    %343 := .value v343,
    %344 := .value v344,
    %345 := .value v345,
    %346 := .value v346,
    %347 := .value v347,
    %348 := .value v348,
    %349 := .value v349,
    %350 := .value v350,
    %351 := .value v351,
    %352 := .value v352,
    %353 := .value v353,
    %354 := .value v354]

def fullOut03 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v329 := s.e.rotateRight 14
  let v330 := s.e.rotateRight 18
  let v331 := v329 ^^^ v330
  let v332 := s.e.rotateRight 41
  let v333 := v331 ^^^ v332
  let v334 := s.e &&& s.f
  let v335 := s.e ^^^ (-1 : Word)
  let v336 := s.g &&& v335
  let v337 := k
  let v338 := (w 3) + s.h
  let v339 := v338 + v337
  let v340 := v339 + v336
  let v341 := v340 + v334
  let v342 := v341 + v333
  let v343 := s.a.rotateRight 28
  let v344 := s.a.rotateRight 34
  let v345 := v343 ^^^ v344
  let v346 := s.a.rotateRight 39
  let v347 := v345 ^^^ v346
  let v348 := s.a &&& s.b
  let v349 := s.b ^^^ s.c
  let v350 := s.a &&& v349
  let v351 := v350 ^^^ (s.b &&& s.c)
  let v352 := v347 + v351
  let v353 := v342 + s.d
  let v354 := v352 + v342
  ⟨v354, s.a, s.b, s.c, v353, s.e, s.f, s.g⟩

theorem fullOut03_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut03 s w k = Spec.round s (w 3) k := by
  dsimp only [fullOut03, Spec.round]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv03_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 329 E (fullEnv03 E s w k) := by
  unfold fullEnv03
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv03_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv03 E s w k) := by
  exact (fullEnv03_before E s w k).frame (by decide)

theorem full_body03 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready03 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 24#64) 64)
    (hk : state.mem.readAt (kp.add 24#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 129 |>.take 26) state =
      .value (fullEnv03 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv03, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w0, h.w1, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k03, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready03 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready03 E s w) (hw : ScheduleReady w) :
    Ready04 (fullEnv03 E s w k) (Spec.round s (w 3) k) w := by
  have hb := fullEnv03_before E s w k
  have hout := fullOut03_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv03, fullOut03, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 328 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 302 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 276 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv03, fullOut03, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 327 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 301 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 275 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv03, Spec.round, mlir_env]
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

theorem full_step03 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready03 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 129 |>.take 26) state =
      .value (E', state) ∧
      Ready04 E' (Spec.round s (w 3) (constants.toList.getD 3 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 3 0
  have hf := fullEnv03_frame E s w k
  refine ⟨fullEnv03 E s w k,
    full_body03 E state s w kp k h hc (hk 3).1 (hk 3).2,
    full_ready03 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
