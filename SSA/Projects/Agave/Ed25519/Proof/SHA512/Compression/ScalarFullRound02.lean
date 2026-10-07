import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 103..128: round 2. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv02 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v303 := s.e.rotateRight 14
  let v304 := s.e.rotateRight 18
  let v305 := v303 ^^^ v304
  let v306 := s.e.rotateRight 41
  let v307 := v305 ^^^ v306
  let v308 := s.e &&& s.f
  let v309 := s.e ^^^ (-1 : Word)
  let v310 := s.g &&& v309
  let v311 := k
  let v312 := (w 2) + s.h
  let v313 := v312 + v311
  let v314 := v313 + v310
  let v315 := v314 + v308
  let v316 := v315 + v307
  let v317 := s.a.rotateRight 28
  let v318 := s.a.rotateRight 34
  let v319 := v317 ^^^ v318
  let v320 := s.a.rotateRight 39
  let v321 := v319 ^^^ v320
  let v322 := s.a &&& s.b
  let v323 := s.b ^^^ s.c
  let v324 := s.a &&& v323
  let v325 := v324 ^^^ (s.b &&& s.c)
  let v326 := v321 + v325
  let v327 := v316 + s.d
  let v328 := v326 + v316
  E[%303 := .value v303,
    %304 := .value v304,
    %305 := .value v305,
    %306 := .value v306,
    %307 := .value v307,
    %308 := .value v308,
    %309 := .value v309,
    %310 := .value v310,
    %311 := .value v311,
    %312 := .value v312,
    %313 := .value v313,
    %314 := .value v314,
    %315 := .value v315,
    %316 := .value v316,
    %317 := .value v317,
    %318 := .value v318,
    %319 := .value v319,
    %320 := .value v320,
    %321 := .value v321,
    %322 := .value v322,
    %323 := .value v323,
    %324 := .value v324,
    %325 := .value v325,
    %326 := .value v326,
    %327 := .value v327,
    %328 := .value v328]

def fullOut02 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v303 := s.e.rotateRight 14
  let v304 := s.e.rotateRight 18
  let v305 := v303 ^^^ v304
  let v306 := s.e.rotateRight 41
  let v307 := v305 ^^^ v306
  let v308 := s.e &&& s.f
  let v309 := s.e ^^^ (-1 : Word)
  let v310 := s.g &&& v309
  let v311 := k
  let v312 := (w 2) + s.h
  let v313 := v312 + v311
  let v314 := v313 + v310
  let v315 := v314 + v308
  let v316 := v315 + v307
  let v317 := s.a.rotateRight 28
  let v318 := s.a.rotateRight 34
  let v319 := v317 ^^^ v318
  let v320 := s.a.rotateRight 39
  let v321 := v319 ^^^ v320
  let v322 := s.a &&& s.b
  let v323 := s.b ^^^ s.c
  let v324 := s.a &&& v323
  let v325 := v324 ^^^ (s.b &&& s.c)
  let v326 := v321 + v325
  let v327 := v316 + s.d
  let v328 := v326 + v316
  ⟨v328, s.a, s.b, s.c, v327, s.e, s.f, s.g⟩

theorem fullOut02_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut02 s w k = Spec.round s (w 2) k := by
  dsimp only [fullOut02, Spec.round]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv02_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 303 E (fullEnv02 E s w k) := by
  unfold fullEnv02
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv02_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv02 E s w k) := by
  exact (fullEnv02_before E s w k).frame (by decide)

theorem full_body02 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready02 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 16#64) 64)
    (hk : state.mem.readAt (kp.add 16#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 103 |>.take 26) state =
      .value (fullEnv02 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv02, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w0, h.w1, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k02, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready02 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready02 E s w) (hw : ScheduleReady w) :
    Ready03 (fullEnv02 E s w k) (Spec.round s (w 2) k) w := by
  have hb := fullEnv02_before E s w k
  have hout := fullOut02_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv02, fullOut02, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 302 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 276 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 201 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv02, fullOut02, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 301 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 275 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 196 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv02, Spec.round, mlir_env]
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

theorem full_step02 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready02 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 103 |>.take 26) state =
      .value (E', state) ∧
      Ready03 E' (Spec.round s (w 2) (constants.toList.getD 2 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 2 0
  have hf := fullEnv02_frame E s w k
  refine ⟨fullEnv02 E s w k,
    full_body02 E state s w kp k h hc (hk 2).1 (hk 2).2,
    full_ready02 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
