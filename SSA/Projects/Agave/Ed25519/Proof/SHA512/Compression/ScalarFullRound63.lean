import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2300..2338: round 63. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv63 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2500 := (w 48).rotateRight 1
  let v2501 := (w 48).rotateRight 8
  let v2502 := v2500 ^^^ v2501
  let v2503 := (w 48) >>> 7
  let v2504 := v2502 ^^^ v2503
  let v2505 := (w 61).rotateRight 19
  let v2506 := (w 61).rotateRight 61
  let v2507 := v2505 ^^^ v2506
  let v2508 := (w 61) >>> 6
  let v2509 := v2507 ^^^ v2508
  let v2510 := v2504 + (w 47)
  let v2511 := v2510 + (w 56)
  let v2512 := v2511 + v2509
  let v2513 := s.e.rotateRight 14
  let v2514 := s.e.rotateRight 18
  let v2515 := v2513 ^^^ v2514
  let v2516 := s.e.rotateRight 41
  let v2517 := v2515 ^^^ v2516
  let v2518 := s.e &&& s.f
  let v2519 := s.e ^^^ (-1 : Word)
  let v2520 := s.g &&& v2519
  let v2521 := v2518 ||| v2520
  let v2522 := k
  let v2523 := v2512 + v2522
  let v2524 := v2523 + s.h
  let v2525 := v2524 + v2521
  let v2526 := v2525 + v2517
  let v2527 := s.a.rotateRight 28
  let v2528 := s.a.rotateRight 34
  let v2529 := v2527 ^^^ v2528
  let v2530 := s.a.rotateRight 39
  let v2531 := v2529 ^^^ v2530
  let v2532 := s.a &&& s.b
  let v2533 := s.b ^^^ s.c
  let v2534 := s.a &&& v2533
  let v2535 := v2534 ^^^ (s.b &&& s.c)
  let v2536 := v2531 + v2535
  let v2537 := v2526 + s.d
  let v2538 := v2536 + v2526
  E[%2500 := .value v2500,
    %2501 := .value v2501,
    %2502 := .value v2502,
    %2503 := .value v2503,
    %2504 := .value v2504,
    %2505 := .value v2505,
    %2506 := .value v2506,
    %2507 := .value v2507,
    %2508 := .value v2508,
    %2509 := .value v2509,
    %2510 := .value v2510,
    %2511 := .value v2511,
    %2512 := .value v2512,
    %2513 := .value v2513,
    %2514 := .value v2514,
    %2515 := .value v2515,
    %2516 := .value v2516,
    %2517 := .value v2517,
    %2518 := .value v2518,
    %2519 := .value v2519,
    %2520 := .value v2520,
    %2521 := .value v2521,
    %2522 := .value v2522,
    %2523 := .value v2523,
    %2524 := .value v2524,
    %2525 := .value v2525,
    %2526 := .value v2526,
    %2527 := .value v2527,
    %2528 := .value v2528,
    %2529 := .value v2529,
    %2530 := .value v2530,
    %2531 := .value v2531,
    %2532 := .value v2532,
    %2533 := .value v2533,
    %2534 := .value v2534,
    %2535 := .value v2535,
    %2536 := .value v2536,
    %2537 := .value v2537,
    %2538 := .value v2538]

def fullOut63 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2500 := (w 48).rotateRight 1
  let v2501 := (w 48).rotateRight 8
  let v2502 := v2500 ^^^ v2501
  let v2503 := (w 48) >>> 7
  let v2504 := v2502 ^^^ v2503
  let v2505 := (w 61).rotateRight 19
  let v2506 := (w 61).rotateRight 61
  let v2507 := v2505 ^^^ v2506
  let v2508 := (w 61) >>> 6
  let v2509 := v2507 ^^^ v2508
  let v2510 := v2504 + (w 47)
  let v2511 := v2510 + (w 56)
  let v2512 := v2511 + v2509
  let v2513 := s.e.rotateRight 14
  let v2514 := s.e.rotateRight 18
  let v2515 := v2513 ^^^ v2514
  let v2516 := s.e.rotateRight 41
  let v2517 := v2515 ^^^ v2516
  let v2518 := s.e &&& s.f
  let v2519 := s.e ^^^ (-1 : Word)
  let v2520 := s.g &&& v2519
  let v2521 := v2518 ||| v2520
  let v2522 := k
  let v2523 := v2512 + v2522
  let v2524 := v2523 + s.h
  let v2525 := v2524 + v2521
  let v2526 := v2525 + v2517
  let v2527 := s.a.rotateRight 28
  let v2528 := s.a.rotateRight 34
  let v2529 := v2527 ^^^ v2528
  let v2530 := s.a.rotateRight 39
  let v2531 := v2529 ^^^ v2530
  let v2532 := s.a &&& s.b
  let v2533 := s.b ^^^ s.c
  let v2534 := s.a &&& v2533
  let v2535 := v2534 ^^^ (s.b &&& s.c)
  let v2536 := v2531 + v2535
  let v2537 := v2526 + s.d
  let v2538 := v2536 + v2526
  ⟨v2538, s.a, s.b, s.c, v2537, s.e, s.f, s.g⟩

theorem fullOut63_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut63 s w k = Spec.round s (w 63) k := by
  have hw63 := hw 63 (by decide) (by decide)
  dsimp only [fullOut63, Spec.round]
  rw [hw63]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv63_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2500 E (fullEnv63 E s w k) := by
  unfold fullEnv63
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv63_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv63 E s w k) := by
  exact (fullEnv63_before E s w k).frame (by decide)

theorem full_body63 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready63 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 504#64) 64)
    (hk : state.mem.readAt (kp.add 504#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2300 |>.take 39) state =
      .value (fullEnv63 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv63, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w47, h.w48, h.w49, h.w50, h.w51, h.w52, h.w53, h.w54, h.w55, h.w56, h.w57, h.w58, h.w59, h.w60, h.w61, h.w62, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k63, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready63 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready63 E s w) (hw : ScheduleReady w) :
    Ready64 (fullEnv63 E s w k) (Spec.round s (w 63) k) w := by
  have hb := fullEnv63_before E s w k
  have hout := fullOut63_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv63, fullOut63, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2499 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2460 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2421 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv63, fullOut63, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2498 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2459 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2420 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv63, Spec.round, mlir_env]
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
  · rw [hb.read_val 2356 (by decide) (by rfl)]; exact h.w59
  · rw [hb.read_val 2395 (by decide) (by rfl)]; exact h.w60
  · rw [hb.read_val 2434 (by decide) (by rfl)]; exact h.w61
  · rw [hb.read_val 2473 (by decide) (by rfl)]; exact h.w62
  · have hwr := hw 63 (by decide) (by decide)
    simp [fullEnv63, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step63 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready63 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2300 |>.take 39) state =
      .value (E', state) ∧
      Ready64 E' (Spec.round s (w 63) (constants.toList.getD 63 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 63 0
  have hf := fullEnv63_frame E s w k
  refine ⟨fullEnv63 E s w k,
    full_body63 E state s w kp k h hc (hk 63).1 (hk 63).2,
    full_ready63 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
