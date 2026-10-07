import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2144..2182: round 59. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv59 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2344 := (w 44).rotateRight 1
  let v2345 := (w 44).rotateRight 8
  let v2346 := v2344 ^^^ v2345
  let v2347 := (w 44) >>> 7
  let v2348 := v2346 ^^^ v2347
  let v2349 := (w 57).rotateRight 19
  let v2350 := (w 57).rotateRight 61
  let v2351 := v2349 ^^^ v2350
  let v2352 := (w 57) >>> 6
  let v2353 := v2351 ^^^ v2352
  let v2354 := v2348 + (w 43)
  let v2355 := v2354 + (w 52)
  let v2356 := v2355 + v2353
  let v2357 := s.e.rotateRight 14
  let v2358 := s.e.rotateRight 18
  let v2359 := v2357 ^^^ v2358
  let v2360 := s.e.rotateRight 41
  let v2361 := v2359 ^^^ v2360
  let v2362 := s.e &&& s.f
  let v2363 := s.e ^^^ (-1 : Word)
  let v2364 := s.g &&& v2363
  let v2365 := v2362 ||| v2364
  let v2366 := k
  let v2367 := v2356 + v2366
  let v2368 := v2367 + s.h
  let v2369 := v2368 + v2365
  let v2370 := v2369 + v2361
  let v2371 := s.a.rotateRight 28
  let v2372 := s.a.rotateRight 34
  let v2373 := v2371 ^^^ v2372
  let v2374 := s.a.rotateRight 39
  let v2375 := v2373 ^^^ v2374
  let v2376 := s.a &&& s.b
  let v2377 := s.b ^^^ s.c
  let v2378 := s.a &&& v2377
  let v2379 := v2378 ^^^ (s.b &&& s.c)
  let v2380 := v2375 + v2379
  let v2381 := v2370 + s.d
  let v2382 := v2380 + v2370
  E[%2344 := .value v2344,
    %2345 := .value v2345,
    %2346 := .value v2346,
    %2347 := .value v2347,
    %2348 := .value v2348,
    %2349 := .value v2349,
    %2350 := .value v2350,
    %2351 := .value v2351,
    %2352 := .value v2352,
    %2353 := .value v2353,
    %2354 := .value v2354,
    %2355 := .value v2355,
    %2356 := .value v2356,
    %2357 := .value v2357,
    %2358 := .value v2358,
    %2359 := .value v2359,
    %2360 := .value v2360,
    %2361 := .value v2361,
    %2362 := .value v2362,
    %2363 := .value v2363,
    %2364 := .value v2364,
    %2365 := .value v2365,
    %2366 := .value v2366,
    %2367 := .value v2367,
    %2368 := .value v2368,
    %2369 := .value v2369,
    %2370 := .value v2370,
    %2371 := .value v2371,
    %2372 := .value v2372,
    %2373 := .value v2373,
    %2374 := .value v2374,
    %2375 := .value v2375,
    %2376 := .value v2376,
    %2377 := .value v2377,
    %2378 := .value v2378,
    %2379 := .value v2379,
    %2380 := .value v2380,
    %2381 := .value v2381,
    %2382 := .value v2382]

def fullOut59 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2344 := (w 44).rotateRight 1
  let v2345 := (w 44).rotateRight 8
  let v2346 := v2344 ^^^ v2345
  let v2347 := (w 44) >>> 7
  let v2348 := v2346 ^^^ v2347
  let v2349 := (w 57).rotateRight 19
  let v2350 := (w 57).rotateRight 61
  let v2351 := v2349 ^^^ v2350
  let v2352 := (w 57) >>> 6
  let v2353 := v2351 ^^^ v2352
  let v2354 := v2348 + (w 43)
  let v2355 := v2354 + (w 52)
  let v2356 := v2355 + v2353
  let v2357 := s.e.rotateRight 14
  let v2358 := s.e.rotateRight 18
  let v2359 := v2357 ^^^ v2358
  let v2360 := s.e.rotateRight 41
  let v2361 := v2359 ^^^ v2360
  let v2362 := s.e &&& s.f
  let v2363 := s.e ^^^ (-1 : Word)
  let v2364 := s.g &&& v2363
  let v2365 := v2362 ||| v2364
  let v2366 := k
  let v2367 := v2356 + v2366
  let v2368 := v2367 + s.h
  let v2369 := v2368 + v2365
  let v2370 := v2369 + v2361
  let v2371 := s.a.rotateRight 28
  let v2372 := s.a.rotateRight 34
  let v2373 := v2371 ^^^ v2372
  let v2374 := s.a.rotateRight 39
  let v2375 := v2373 ^^^ v2374
  let v2376 := s.a &&& s.b
  let v2377 := s.b ^^^ s.c
  let v2378 := s.a &&& v2377
  let v2379 := v2378 ^^^ (s.b &&& s.c)
  let v2380 := v2375 + v2379
  let v2381 := v2370 + s.d
  let v2382 := v2380 + v2370
  ⟨v2382, s.a, s.b, s.c, v2381, s.e, s.f, s.g⟩

theorem fullOut59_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut59 s w k = Spec.round s (w 59) k := by
  have hw59 := hw 59 (by decide) (by decide)
  dsimp only [fullOut59, Spec.round]
  rw [hw59]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv59_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2344 E (fullEnv59 E s w k) := by
  unfold fullEnv59
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv59_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv59 E s w k) := by
  exact (fullEnv59_before E s w k).frame (by decide)

theorem full_body59 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready59 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 472#64) 64)
    (hk : state.mem.readAt (kp.add 472#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2144 |>.take 39) state =
      .value (fullEnv59 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv59, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w43, h.w44, h.w45, h.w46, h.w47, h.w48, h.w49, h.w50, h.w51, h.w52, h.w53, h.w54, h.w55, h.w56, h.w57, h.w58, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k59, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready59 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready59 E s w) (hw : ScheduleReady w) :
    Ready60 (fullEnv59 E s w k) (Spec.round s (w 59) k) w := by
  have hb := fullEnv59_before E s w k
  have hout := fullOut59_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv59, fullOut59, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2343 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2304 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2265 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv59, fullOut59, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2342 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2303 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2264 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv59, Spec.round, mlir_env]
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
  · rw [hb.read_val 2317 (by decide) (by rfl)]; exact h.w58
  · have hwr := hw 59 (by decide) (by decide)
    simp [fullEnv59, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step59 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready59 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2144 |>.take 39) state =
      .value (E', state) ∧
      Ready60 E' (Spec.round s (w 59) (constants.toList.getD 59 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 59 0
  have hf := fullEnv59_frame E s w k
  refine ⟨fullEnv59 E s w k,
    full_body59 E state s w kp k h hc (hk 59).1 (hk 59).2,
    full_ready59 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
