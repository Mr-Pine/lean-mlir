import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairVectors
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairFrame

/-! Exact four-lane schedule prefix of imported bb12 (instructions 0..27).
The two windows are arbitrary and independent; the only loaded values are a
concrete pair of round constants. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000

structure BulkPairWindowReady (E : Env program.Γ) (q u : Window) : Prop where
  p0 : E.read (%473) = bulkVec (q 0) (q 1) (u 0) (u 1)
  p1 : E.read (%472) = bulkVec (q 2) (q 3) (u 2) (u 3)
  p2 : E.read (%477) = bulkVec (q 4) (q 5) (u 4) (u 5)
  p3 : E.read (%478) = bulkVec (q 6) (q 7) (u 6) (u 7)
  p4 : E.read (%475) = bulkVec (q 8) (q 9) (u 8) (u 9)
  p5 : E.read (%474) = bulkVec (q 10) (q 11) (u 10) (u 11)
  p6 : E.read (%479) = bulkVec (q 12) (q 13) (u 12) (u 13)
  p7 : E.read (%476) = bulkVec (q 14) (q 15) (u 14) (u 15)

structure BulkPairScheduleReady (E : Env program.Γ) (k : Pointer) (r j : Nat) : Prop where
  constantPtr : E.read (%24) = .value k
  nextIndex : E.read (%470) = .value (BitVec.ofNat 64 (r+16))
  slot : E.read (%471) = .value (BitVec.ofNat 64 j)
  one : E.read (%1) = .value 1#64
  c1 : E.read (%68) = bulkVec 1 1 1 1
  c7 : E.read (%69) = bulkVec 7 7 7 7
  c56 : E.read (%70) = bulkVec 56 56 56 56
  c8 : E.read (%71) = bulkVec 8 8 8 8
  c63 : E.read (%72) = bulkVec 63 63 63 63
  c6 : E.read (%73) = bulkVec 6 6 6 6
  c3 : E.read (%74) = bulkVec 3 3 3 3
  c19 : E.read (%75) = bulkVec 19 19 19 19
  c45 : E.read (%76) = bulkVec 45 45 45 45
  c61 : E.read (%77) = bulkVec 61 61 61 61

def bulkPairScheduleEnv (E : Env program.Γ) (k : Pointer) (r j : Nat)
    (q u : Window) (k0 k1 : Word) : Env program.Γ :=
  let v492 (q : Window) : Word × Word := (q 1, q 2)
  let v493 (q : Window) : Word × Word := (q 9, q 10)
  let v494 (q : Window) : Word × Word := ((v492 q).1 >>> 1, (v492 q).2 >>> 1)
  let v495 (q : Window) : Word × Word := (q 0 + (v493 q).1, q 1 + (v493 q).2)
  let v496 (q : Window) : Word × Word := ((v492 q).1 >>> 7, (v492 q).2 >>> 7)
  let v497 (q : Window) : Word × Word := ((v492 q).1 <<< 56, (v492 q).2 <<< 56)
  let v498 (q : Window) : Word × Word := ((v494 q).1 ^^^ (v496 q).1, (v494 q).2 ^^^ (v496 q).2)
  let v499 (q : Window) : Word × Word := ((v492 q).1 >>> 8, (v492 q).2 >>> 8)
  let v500 (q : Window) : Word × Word := ((v498 q).1 ^^^ (v497 q).1, (v498 q).2 ^^^ (v497 q).2)
  let v501 (q : Window) : Word × Word := ((v492 q).1 <<< 63, (v492 q).2 <<< 63)
  let v502 (q : Window) : Word × Word := ((v500 q).1 ^^^ (v499 q).1, (v500 q).2 ^^^ (v499 q).2)
  let v503 (q : Window) : Word × Word := ((v502 q).1 ^^^ (v501 q).1, (v502 q).2 ^^^ (v501 q).2)
  let v504 (q : Window) : Word × Word := (q 14 >>> 6, q 15 >>> 6)
  let v505 (q : Window) : Word × Word := (q 14 <<< 3, q 15 <<< 3)
  let v506 (q : Window) : Word × Word := ((v495 q).1 + (v503 q).1, (v495 q).2 + (v503 q).2)
  let v507 (q : Window) : Word × Word := (q 14 >>> 19, q 15 >>> 19)
  let v508 (q : Window) : Word × Word := ((v505 q).1 ^^^ (v504 q).1, (v505 q).2 ^^^ (v504 q).2)
  let v509 (q : Window) : Word × Word := (q 14 <<< 45, q 15 <<< 45)
  let v510 (q : Window) : Word × Word := ((v508 q).1 ^^^ (v507 q).1, (v508 q).2 ^^^ (v507 q).2)
  let v511 (q : Window) : Word × Word := (q 14 >>> 61, q 15 >>> 61)
  let v512 (q : Window) : Word × Word := ((v510 q).1 ^^^ (v509 q).1, (v510 q).2 ^^^ (v509 q).2)
  let v513 (q : Window) : Word × Word := ((v512 q).1 ^^^ (v511 q).1, (v512 q).2 ^^^ (v511 q).2)
  let v514 (q : Window) : Word × Word := ((v506 q).1 + (v513 q).1, (v506 q).2 + (v513 q).2)
  let v515 (q : Window) : Word × Word := ((v514 q).1 + k0, (v514 q).2 + k1)
  E[%488 := .value (BitVec.ofNat 64 (j+1)),
    %489 := .value (k.add (BitVec.ofNat 64 (8*(r+16)))),
    %490 := pairVec k0 k1, %491 := bulkVec k0 k1 k0 k1,
    %492 := bulkPairVec (v492 q) (v492 u),
    %493 := bulkPairVec (v493 q) (v493 u),
    %494 := bulkPairVec (v494 q) (v494 u),
    %495 := bulkPairVec (v495 q) (v495 u),
    %496 := bulkPairVec (v496 q) (v496 u),
    %497 := bulkPairVec (v497 q) (v497 u),
    %498 := bulkPairVec (v498 q) (v498 u),
    %499 := bulkPairVec (v499 q) (v499 u),
    %500 := bulkPairVec (v500 q) (v500 u),
    %501 := bulkPairVec (v501 q) (v501 u),
    %502 := bulkPairVec (v502 q) (v502 u),
    %503 := bulkPairVec (v503 q) (v503 u),
    %504 := bulkPairVec (v504 q) (v504 u),
    %505 := bulkPairVec (v505 q) (v505 u),
    %506 := bulkPairVec (v506 q) (v506 u),
    %507 := bulkPairVec (v507 q) (v507 u),
    %508 := bulkPairVec (v508 q) (v508 u),
    %509 := bulkPairVec (v509 q) (v509 u),
    %510 := bulkPairVec (v510 q) (v510 u),
    %511 := bulkPairVec (v511 q) (v511 u),
    %512 := bulkPairVec (v512 q) (v512 u),
    %513 := bulkPairVec (v513 q) (v513 u),
    %514 := bulkPairVec (v514 q) (v514 u),
    %515 := bulkPairVec (v515 q) (v515 u)]

private theorem bulk_pair_counter_add (j : Nat) (hj : j < 8) :
    Operation.add {nsw := true, nuw := true} (.value (BitVec.ofNat 64 j)) (.value 1#64) =
      .value (BitVec.ofNat 64 (j+1)) := by
  interval_cases j <;> decide

private theorem bulk_pair_constant_gep (r : Nat) (hr : r < 64) :
    Operation.gepInboundsIndex 8 (.value (BitVec.ofNat 64 (r+16))) =
      .value (Int.ofNat (8*(r+16))) := by
  interval_cases r <;> decide

theorem bulk_pair_schedule_prefix (E : Env program.Γ) (mem : GlobalState)
    (k : Pointer) (r j : Nat) (q u : Window) (k0 k1 : Word)
    (hr : r + 1 < 64) (hj : j < 8)
    (h : BulkPairScheduleReady E k r j) (hw : BulkPairWindowReady E q u)
    (hk : SmallRange mem.mem k 640)
    (hread : mem.mem.readAt (k.add (BitVec.ofNat 64 (8*(r+16)))) 128 = k1 ++ k0) :
    List.foldlM Instr.run E (program.bb12.body.take 28) mem =
      .value (bulkPairScheduleEnv E k r j q u k0 k1, mem) := by
  have hinc := bulk_pair_counter_add j hj
  change (BinOp.add {nsw := true, nuw := true}).compute
    (.value (BitVec.ofNat 64 j)) (.value 1#64) =
      .value (BitVec.ofNat 64 (j+1)) at hinc
  have hidx := bulk_pair_constant_gep r (by omega)
  have hgep := hk.gep (k := 8*(r+16)) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add] at hgep
  have hfit := hk.fits_add (k := 8*(r+16)) (count := 16) (by omega)
  have hunflat : Ty.wrap (Vector.ofFn (fun i => Ty.extractVecElem 2 64 i (k1 ++ k0))) =
      pairVec k0 k1 := by
    simpa only [Ty.unflatten_vec] using pairVec_unflatten k0 k1
  rcases h with ⟨hp, hr470, hj471, h1, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77⟩
  let E4 := E[%488 := .value (BitVec.ofNat 64 (j+1)),
    %489 := .value (k.add (BitVec.ofNat 64 (8*(r+16)))),
    %490 := pairVec k0 k1, %491 := bulkVec k0 k1 k0 k1]
  let E6 := E4[%492 := bulkVec (q 1) (q 2) (u 1) (u 2),
    %493 := bulkVec (q 9) (q 10) (u 9) (u 10)]
  let E3 := E[%488 := .value (BitVec.ofNat 64 (j+1)),
    %489 := .value (k.add (BitVec.ofNat 64 (8*(r+16)))), %490 := pairVec k0 k1]
  have hload : List.foldlM Instr.run E (program.bb12.body.take 3) mem = .value (E3, mem) := by
    simp [program.bb12, List.foldlM_cons, List.foldlM_nil, Instr.run, E3,
      hp, hr470, hj471, h1, hinc, hidx, hgep, hfit, hread, hunflat,
      GepIndex.inboundsOffset, Operation.load,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]
  have hfirst : List.foldlM Instr.run E (program.bb12.body.take 4) mem = .value (E4, mem) := by
    have hcut : program.bb12.body.take 4 =
      program.bb12.body.take 3 ++ (program.bb12.body.drop 3).take 1 := by rfl
    rw [hcut, List.foldlM_append]
    simp only [EffectM.bind_eq, hload, PoisonOr.value_bind]
    simp [program.bb12, List.foldlM_cons, List.foldlM_nil, Instr.run, E3, E4,
      BinOp.compute, bulkVec, pairVec, Ty.wrap_vec,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]
  have hshuffle : List.foldlM Instr.run E4 ((program.bb12.body.drop 4).take 2) mem =
      .value (E6, mem) := by
    simp [program.bb12, List.foldlM_cons, List.foldlM_nil, Instr.run, E4, E6,
      hw.p0, hw.p1, hw.p4, hw.p5, BinOp.compute, bulkVec, pairVec, Ty.wrap_vec,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]
  have hcut : program.bb12.body.take 28 =
      program.bb12.body.take 4 ++ (program.bb12.body.drop 4).take 2 ++
        (program.bb12.body.drop 6).take 22 := by rfl
  rw [hcut, List.foldlM_append, List.foldlM_append]
  simp only [EffectM.bind_eq, hfirst, PoisonOr.value_bind, hshuffle]
  simp [program.bb12, List.foldlM_cons, List.foldlM_nil, Instr.run,
    bulkPairScheduleEnv, bulkPairVec, E4, E6,
    h68, h69, h70, h71, h72, h73, h74, h75, h76, h77,
    hw.p0, hw.p7, bulkVec_add, bulkVec_xor,
    bulkVec_shl _ _ _ _ _ (by decide : 56 < 64),
    bulkVec_shl _ _ _ _ _ (by decide : 63 < 64),
    bulkVec_shl _ _ _ _ _ (by decide : 3 < 64),
    bulkVec_shl _ _ _ _ _ (by decide : 45 < 64),
    bulkVec_lshr _ _ _ _ _ (by decide : 1 < 64),
    bulkVec_lshr _ _ _ _ _ (by decide : 7 < 64),
    bulkVec_lshr _ _ _ _ _ (by decide : 8 < 64),
    bulkVec_lshr _ _ _ _ _ (by decide : 6 < 64),
    bulkVec_lshr _ _ _ _ _ (by decide : 19 < 64),
    bulkVec_lshr _ _ _ _ _ (by decide : 61 < 64),
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

/-- Both independent schedules satisfy the same standard sixteen-word recurrence. -/
theorem bulkPairScheduleEnv_words (E : Env program.Γ) (k : Pointer) (r j : Nat)
    (q u : Window) (k0 k1 : Word) :
    (bulkPairScheduleEnv E k r j q u k0 k1).read (%514) =
      bulkPairVec (avxWindowPair q) (avxWindowPair u) ∧
    (bulkPairScheduleEnv E k r j q u k0 k1).read (%515) =
      bulkVec ((avxWindowPair q).1 + k0) ((avxWindowPair q).2 + k1)
        ((avxWindowPair u).1 + k0) ((avxWindowPair u).2 + k1) := by
  simp only [bulkPairScheduleEnv, bulkPairVec, mlir_env]
  change bulkVec (q 0 + q 9 + bulkPairSigma0 (q 1) + bulkPairSigma1 (q 14))
      (q 1 + q 10 + bulkPairSigma0 (q 2) + bulkPairSigma1 (q 15))
      (u 0 + u 9 + bulkPairSigma0 (u 1) + bulkPairSigma1 (u 14))
      (u 1 + u 10 + bulkPairSigma0 (u 2) + bulkPairSigma1 (u 15)) = _ ∧
    bulkVec (q 0 + q 9 + bulkPairSigma0 (q 1) + bulkPairSigma1 (q 14) + k0)
      (q 1 + q 10 + bulkPairSigma0 (q 2) + bulkPairSigma1 (q 15) + k1)
      (u 0 + u 9 + bulkPairSigma0 (u 1) + bulkPairSigma1 (u 14) + k0)
      (u 1 + u 10 + bulkPairSigma0 (u 2) + bulkPairSigma1 (u 15) + k1) = _
  simp only [bulkPairSigma0_eq, bulkPairSigma1_eq, avxWindowPair, and_self]

theorem bulkPairScheduleEnv_spec (E : Env program.Γ) (k : Pointer) (r j : Nat)
    (block₀ block₁ : Agave.Ed25519.Bridge.Challenge.Bytes) (hr : r+1<64) :
    let E' := bulkPairScheduleEnv E k r j (specWindow block₀ r) (specWindow block₁ r)
      (constants.toList.getD (r+16) 0) (constants.toList.getD (r+17) 0)
    E'.read (%514) = bulkVec ((schedule block₀).getD (r+16) 0)
      ((schedule block₀).getD (r+17) 0) ((schedule block₁).getD (r+16) 0)
      ((schedule block₁).getD (r+17) 0) ∧
    E'.read (%515) = bulkVec (scheduleKW (schedule block₀) (r+16))
      (scheduleKW (schedule block₀) (r+17)) (scheduleKW (schedule block₁) (r+16))
      (scheduleKW (schedule block₁) (r+17)) := by
  have hh := bulkPairScheduleEnv_words E k r j (specWindow block₀ r) (specWindow block₁ r)
    (constants.toList.getD (r+16) 0) (constants.toList.getD (r+17) 0)
  rw [avxWindowPair_spec block₀ r hr, avxWindowPair_spec block₁ r hr] at hh
  simpa only [bulkPairVec, scheduleKW, BitVec.add_comm] using hh

theorem bulkPairScheduleEnv_frame (E : Env program.Γ) (k : Pointer) (r j : Nat)
    (q u : Window) (k0 k1 : Word) :
    RegFrame 488 515 E (bulkPairScheduleEnv E k r j q u k0 k1) := by
  unfold bulkPairScheduleEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

end Agave.Ed25519.SHA512.Execution.Avx2
