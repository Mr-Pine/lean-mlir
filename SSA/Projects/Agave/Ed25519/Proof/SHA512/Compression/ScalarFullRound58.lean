import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2105..2143: round 58. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv58 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2305 := (w 43).rotateRight 1
  let v2306 := (w 43).rotateRight 8
  let v2307 := v2305 ^^^ v2306
  let v2308 := (w 43) >>> 7
  let v2309 := v2307 ^^^ v2308
  let v2310 := (w 56).rotateRight 19
  let v2311 := (w 56).rotateRight 61
  let v2312 := v2310 ^^^ v2311
  let v2313 := (w 56) >>> 6
  let v2314 := v2312 ^^^ v2313
  let v2315 := v2309 + (w 42)
  let v2316 := v2315 + (w 51)
  let v2317 := v2316 + v2314
  let v2318 := s.e.rotateRight 14
  let v2319 := s.e.rotateRight 18
  let v2320 := v2318 ^^^ v2319
  let v2321 := s.e.rotateRight 41
  let v2322 := v2320 ^^^ v2321
  let v2323 := s.e &&& s.f
  let v2324 := s.e ^^^ (-1 : Word)
  let v2325 := s.g &&& v2324
  let v2326 := v2323 ||| v2325
  let v2327 := k
  let v2328 := v2317 + v2327
  let v2329 := v2328 + s.h
  let v2330 := v2329 + v2326
  let v2331 := v2330 + v2322
  let v2332 := s.a.rotateRight 28
  let v2333 := s.a.rotateRight 34
  let v2334 := v2332 ^^^ v2333
  let v2335 := s.a.rotateRight 39
  let v2336 := v2334 ^^^ v2335
  let v2337 := s.a &&& s.b
  let v2338 := s.b ^^^ s.c
  let v2339 := s.a &&& v2338
  let v2340 := v2339 ^^^ (s.b &&& s.c)
  let v2341 := v2336 + v2340
  let v2342 := v2331 + s.d
  let v2343 := v2341 + v2331
  E[%2305 := .value v2305,
    %2306 := .value v2306,
    %2307 := .value v2307,
    %2308 := .value v2308,
    %2309 := .value v2309,
    %2310 := .value v2310,
    %2311 := .value v2311,
    %2312 := .value v2312,
    %2313 := .value v2313,
    %2314 := .value v2314,
    %2315 := .value v2315,
    %2316 := .value v2316,
    %2317 := .value v2317,
    %2318 := .value v2318,
    %2319 := .value v2319,
    %2320 := .value v2320,
    %2321 := .value v2321,
    %2322 := .value v2322,
    %2323 := .value v2323,
    %2324 := .value v2324,
    %2325 := .value v2325,
    %2326 := .value v2326,
    %2327 := .value v2327,
    %2328 := .value v2328,
    %2329 := .value v2329,
    %2330 := .value v2330,
    %2331 := .value v2331,
    %2332 := .value v2332,
    %2333 := .value v2333,
    %2334 := .value v2334,
    %2335 := .value v2335,
    %2336 := .value v2336,
    %2337 := .value v2337,
    %2338 := .value v2338,
    %2339 := .value v2339,
    %2340 := .value v2340,
    %2341 := .value v2341,
    %2342 := .value v2342,
    %2343 := .value v2343]

def fullOut58 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2305 := (w 43).rotateRight 1
  let v2306 := (w 43).rotateRight 8
  let v2307 := v2305 ^^^ v2306
  let v2308 := (w 43) >>> 7
  let v2309 := v2307 ^^^ v2308
  let v2310 := (w 56).rotateRight 19
  let v2311 := (w 56).rotateRight 61
  let v2312 := v2310 ^^^ v2311
  let v2313 := (w 56) >>> 6
  let v2314 := v2312 ^^^ v2313
  let v2315 := v2309 + (w 42)
  let v2316 := v2315 + (w 51)
  let v2317 := v2316 + v2314
  let v2318 := s.e.rotateRight 14
  let v2319 := s.e.rotateRight 18
  let v2320 := v2318 ^^^ v2319
  let v2321 := s.e.rotateRight 41
  let v2322 := v2320 ^^^ v2321
  let v2323 := s.e &&& s.f
  let v2324 := s.e ^^^ (-1 : Word)
  let v2325 := s.g &&& v2324
  let v2326 := v2323 ||| v2325
  let v2327 := k
  let v2328 := v2317 + v2327
  let v2329 := v2328 + s.h
  let v2330 := v2329 + v2326
  let v2331 := v2330 + v2322
  let v2332 := s.a.rotateRight 28
  let v2333 := s.a.rotateRight 34
  let v2334 := v2332 ^^^ v2333
  let v2335 := s.a.rotateRight 39
  let v2336 := v2334 ^^^ v2335
  let v2337 := s.a &&& s.b
  let v2338 := s.b ^^^ s.c
  let v2339 := s.a &&& v2338
  let v2340 := v2339 ^^^ (s.b &&& s.c)
  let v2341 := v2336 + v2340
  let v2342 := v2331 + s.d
  let v2343 := v2341 + v2331
  ⟨v2343, s.a, s.b, s.c, v2342, s.e, s.f, s.g⟩

theorem fullOut58_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut58 s w k = Spec.round s (w 58) k := by
  have hw58 := hw 58 (by decide) (by decide)
  dsimp only [fullOut58, Spec.round]
  rw [hw58]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv58_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2305 E (fullEnv58 E s w k) := by
  unfold fullEnv58
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv58_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv58 E s w k) := by
  exact (fullEnv58_before E s w k).frame (by decide)

theorem full_body58 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready58 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 464#64) 64)
    (hk : state.mem.readAt (kp.add 464#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2105 |>.take 39) state =
      .value (fullEnv58 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv58, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w42, h.w43, h.w44, h.w45, h.w46, h.w47, h.w48, h.w49, h.w50, h.w51, h.w52, h.w53, h.w54, h.w55, h.w56, h.w57, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k58, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready58 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready58 E s w) (hw : ScheduleReady w) :
    Ready59 (fullEnv58 E s w k) (Spec.round s (w 58) k) w := by
  have hb := fullEnv58_before E s w k
  have hout := fullOut58_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv58, fullOut58, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2304 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2265 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2226 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv58, fullOut58, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2303 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2264 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2225 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv58, Spec.round, mlir_env]
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
  · rw [hb.read_val 2161 (by decide) (by rfl)]; exact h.w54
  · rw [hb.read_val 2200 (by decide) (by rfl)]; exact h.w55
  · rw [hb.read_val 2239 (by decide) (by rfl)]; exact h.w56
  · rw [hb.read_val 2278 (by decide) (by rfl)]; exact h.w57
  · have hwr := hw 58 (by decide) (by decide)
    simp [fullEnv58, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step58 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready58 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2105 |>.take 39) state =
      .value (E', state) ∧
      Ready59 E' (Spec.round s (w 58) (constants.toList.getD 58 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 58 0
  have hf := fullEnv58_frame E s w k
  refine ⟨fullEnv58 E s w k,
    full_body58 E state s w kp k h hc (hk 58).1 (hk 58).2,
    full_ready58 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
