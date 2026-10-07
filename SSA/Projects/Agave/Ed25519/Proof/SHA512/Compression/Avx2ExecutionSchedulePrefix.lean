import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionScheduleVectors

/-! Exact first 27 instructions of imported bb5. They compute two new
schedule words and load/add the corresponding constant pair. -/

namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

/-- The compiler's permutation of the eight live two-word window registers. -/
structure PairWindowReady (E : Env program.Γ) (q : Window) : Prop where
  p0 : E.read (%176) = pairVec (q 0) (q 1)
  p1 : E.read (%175) = pairVec (q 2) (q 3)
  p2 : E.read (%180) = pairVec (q 4) (q 5)
  p3 : E.read (%181) = pairVec (q 6) (q 7)
  p4 : E.read (%178) = pairVec (q 8) (q 9)
  p5 : E.read (%177) = pairVec (q 10) (q 11)
  p6 : E.read (%182) = pairVec (q 12) (q 13)
  p7 : E.read (%179) = pairVec (q 14) (q 15)

structure PairScheduleReady (E : Env program.Γ) (k : Pointer) (r j : Nat) : Prop where
  constantPtr : E.read (%24) = .value k
  nextIndex : E.read (%173) = .value (BitVec.ofNat 64 (r+16))
  slot : E.read (%174) = .value (BitVec.ofNat 64 j)
  one : E.read (%1) = .value 1#64
  c1 : E.read (%25) = pairVec 1 1
  c7 : E.read (%26) = pairVec 7 7
  c56 : E.read (%27) = pairVec 56 56
  c8 : E.read (%28) = pairVec 8 8
  c63 : E.read (%29) = pairVec 63 63
  c6 : E.read (%30) = pairVec 6 6
  c3 : E.read (%31) = pairVec 3 3
  c19 : E.read (%32) = pairVec 19 19
  c45 : E.read (%33) = pairVec 45 45
  c61 : E.read (%34) = pairVec 61 61

def pairScheduleEnv (E : Env program.Γ) (k : Pointer) (r j : Nat)
    (q : Window) (k0 k1 : Word) : Env program.Γ :=
  let v193 : Word × Word := (k0, k1)
  let v194 : Word × Word := (q 1, q 2)
  let v195 : Word × Word := (q 9, q 10)
  let v196 := (v194.1 >>> 1, v194.2 >>> 1)
  let v197 := (q 0 + v195.1, q 1 + v195.2)
  let v198 := (v194.1 >>> 7, v194.2 >>> 7)
  let v199 := (v194.1 <<< 56, v194.2 <<< 56)
  let v200 := (v194.1 >>> 8, v194.2 >>> 8)
  let v201 := (v196.1 ^^^ v199.1, v196.2 ^^^ v199.2)
  let v202 := (v194.1 <<< 63, v194.2 <<< 63)
  let v203 := (v201.1 ^^^ v200.1, v201.2 ^^^ v200.2)
  let v204 := (v203.1 ^^^ v202.1, v203.2 ^^^ v202.2)
  let v205 := (v204.1 ^^^ v198.1, v204.2 ^^^ v198.2)
  let v206 := (q 14 >>> 6, q 15 >>> 6)
  let v207 := (q 14 <<< 3, q 15 <<< 3)
  let v208 := (v197.1 + v205.1, v197.2 + v205.2)
  let v209 := (q 14 >>> 19, q 15 >>> 19)
  let v210 := (q 14 <<< 45, q 15 <<< 45)
  let v211 := (v207.1 ^^^ v209.1, v207.2 ^^^ v209.2)
  let v212 := (q 14 >>> 61, q 15 >>> 61)
  let v213 := (v211.1 ^^^ v210.1, v211.2 ^^^ v210.2)
  let v214 := (v213.1 ^^^ v212.1, v213.2 ^^^ v212.2)
  let v215 := (v214.1 ^^^ v206.1, v214.2 ^^^ v206.2)
  let v216 := (v208.1 + v215.1, v208.2 + v215.2)
  let v217 := (v216.1 + v193.1, v216.2 + v193.2)
  E[%191 := .value (BitVec.ofNat 64 (j+1)),
    %192 := .value (k.add (BitVec.ofNat 64 (8*(r+16)))),
    %193 := pairVec v193.1 v193.2,
    %194 := pairVec v194.1 v194.2,
    %195 := pairVec v195.1 v195.2,
    %196 := pairVec v196.1 v196.2,
    %197 := pairVec v197.1 v197.2,
    %198 := pairVec v198.1 v198.2,
    %199 := pairVec v199.1 v199.2,
    %200 := pairVec v200.1 v200.2,
    %201 := pairVec v201.1 v201.2,
    %202 := pairVec v202.1 v202.2,
    %203 := pairVec v203.1 v203.2,
    %204 := pairVec v204.1 v204.2,
    %205 := pairVec v205.1 v205.2,
    %206 := pairVec v206.1 v206.2,
    %207 := pairVec v207.1 v207.2,
    %208 := pairVec v208.1 v208.2,
    %209 := pairVec v209.1 v209.2,
    %210 := pairVec v210.1 v210.2,
    %211 := pairVec v211.1 v211.2,
    %212 := pairVec v212.1 v212.2,
    %213 := pairVec v213.1 v213.2,
    %214 := pairVec v214.1 v214.2,
    %215 := pairVec v215.1 v215.2,
    %216 := pairVec v216.1 v216.2,
    %217 := pairVec v217.1 v217.2]

private theorem pair_counter_add (j : Nat) (hj : j < 8) :
    Operation.add {nsw := true, nuw := true} (.value (BitVec.ofNat 64 j)) (.value 1#64) =
      .value (BitVec.ofNat 64 (j+1)) := by
  interval_cases j <;> decide

private theorem pair_constant_gep (r : Nat) (hr : r < 64) :
    Operation.gepInboundsIndex 8 (.value (BitVec.ofNat 64 (r+16))) =
      .value (Int.ofNat (8*(r+16))) := by
  interval_cases r <;> decide

/-- All source instructions and flags are retained. The constant pair is a
concrete 128-bit memory read, and no schedule-correctness premise is assumed. -/
theorem pair_schedule_prefix (E : Env program.Γ) (mem : GlobalState)
    (k : Pointer) (r j : Nat) (q : Window) (k0 k1 : Word)
    (hr : r + 1 < 64) (hj : j < 8)
    (h : PairScheduleReady E k r j) (hw : PairWindowReady E q)
    (hk : SmallRange mem.mem k 640)
    (hread : mem.mem.readAt (k.add (BitVec.ofNat 64 (8*(r+16)))) 128 = k1 ++ k0) :
    List.foldlM Instr.run E (program.bb5.body.take 27) mem =
      .value (pairScheduleEnv E k r j q k0 k1, mem) := by
  have hinc := pair_counter_add j hj
  change (BinOp.add {nsw := true, nuw := true}).compute
    (.value (BitVec.ofNat 64 j)) (.value 1#64) =
      .value (BitVec.ofNat 64 (j+1)) at hinc
  have hidx := pair_constant_gep r (by omega)
  have hgep := hk.gep (k := 8*(r+16)) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add] at hgep
  have hfit := hk.fits_add (k := 8*(r+16)) (count := 16) (by omega)
  have hunflat : Ty.wrap (Vector.ofFn (fun i => Ty.extractVecElem 2 64 i (k1 ++ k0))) =
      pairVec k0 k1 := by
    simpa only [Ty.unflatten_vec] using pairVec_unflatten k0 k1
  rcases h with ⟨hp, hr173, hj174, h1, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34⟩
  let E3 := E[%191 := .value (BitVec.ofNat 64 (j+1)),
    %192 := .value (k.add (BitVec.ofNat 64 (8*(r+16)))), %193 := pairVec k0 k1]
  let E5 := E3[%194 := pairVec (q 1) (q 2), %195 := pairVec (q 9) (q 10)]
  have hfirst : List.foldlM Instr.run E (program.bb5.body.take 3) mem = .value (E3, mem) := by
    simp [program.bb5, List.foldlM_cons, List.foldlM_nil, Instr.run, E3,
      hp, hr173, hj174, h1, hinc, hidx, hgep, hfit, hread, hunflat,
      GepIndex.inboundsOffset, Operation.load,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]
  have hshuffle : List.foldlM Instr.run E3 ((program.bb5.body.drop 3).take 2) mem =
      .value (E5, mem) := by
    simp [program.bb5, List.foldlM_cons, List.foldlM_nil, Instr.run, E3, E5,
      hw.p0, hw.p1, hw.p4, hw.p5, BinOp.compute, pairVec, Ty.wrap_vec,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]
  have hcut : program.bb5.body.take 27 =
      program.bb5.body.take 3 ++ (program.bb5.body.drop 3).take 2 ++
        (program.bb5.body.drop 5).take 22 := by rfl
  rw [hcut, List.foldlM_append, List.foldlM_append]
  simp only [EffectM.bind_eq, hfirst, PoisonOr.value_bind, hshuffle]
  simp [program.bb5, List.foldlM_cons, List.foldlM_nil, Instr.run, pairScheduleEnv, E3, E5,
    h25, h26, h27, h28, h29, h30, h31, h32, h33, h34,
    hw.p0, hw.p7, pairVec_add, pairVec_xor,
    pairVec_shl _ _ _ (by decide : 56 < 64), pairVec_shl _ _ _ (by decide : 63 < 64),
    pairVec_shl _ _ _ (by decide : 3 < 64), pairVec_shl _ _ _ (by decide : 45 < 64),
    pairVec_lshr _ _ _ (by decide : 1 < 64), pairVec_lshr _ _ _ (by decide : 7 < 64),
    pairVec_lshr _ _ _ (by decide : 8 < 64), pairVec_lshr _ _ _ (by decide : 6 < 64),
    pairVec_lshr _ _ _ (by decide : 19 < 64), pairVec_lshr _ _ _ (by decide : 61 < 64),
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

/-- The two emitted word results are exactly the standard rolling-window recurrence. -/
theorem pairScheduleEnv_words (E : Env program.Γ) (k : Pointer) (r j : Nat)
    (q : Window) (k0 k1 : Word) :
    (pairScheduleEnv E k r j q k0 k1).read (%216) =
      pairVec (avxWindowPair q).1 (avxWindowPair q).2 ∧
    (pairScheduleEnv E k r j q k0 k1).read (%217) =
      pairVec ((avxWindowPair q).1 + k0) ((avxWindowPair q).2 + k1) := by
  simp only [pairScheduleEnv, mlir_env]
  change pairVec (q 0 + q 9 + pairSigma0 (q 1) + pairSigma1 (q 14))
      (q 1 + q 10 + pairSigma0 (q 2) + pairSigma1 (q 15)) = _ ∧
    pairVec (q 0 + q 9 + pairSigma0 (q 1) + pairSigma1 (q 14) + k0)
      (q 1 + q 10 + pairSigma0 (q 2) + pairSigma1 (q 15) + k1) = _
  simp only [pairSigma0_eq, pairSigma1_eq, avxWindowPair, and_self]

/-- Concrete FIPS schedule words and constants determine the actual two
vector destinations of the imported prefix, without a backend-result premise. -/
theorem pairScheduleEnv_spec (E : Env program.Γ) (k : Pointer) (r j : Nat)
    (block : Agave.Ed25519.Bridge.Challenge.Bytes) (hr : r + 1 < 64) :
    let E' := pairScheduleEnv E k r j (specWindow block r)
      (constants.toList.getD (r+16) 0) (constants.toList.getD (r+17) 0)
    E'.read (%216) = pairVec ((schedule block).getD (r+16) 0)
        ((schedule block).getD (r+17) 0) ∧
      E'.read (%217) = pairVec (scheduleKW (schedule block) (r+16))
        (scheduleKW (schedule block) (r+17)) := by
  have hh := pairScheduleEnv_words E k r j (specWindow block r)
    (constants.toList.getD (r+16) 0) (constants.toList.getD (r+17) 0)
  rw [avxWindowPair_spec block r hr] at hh
  simpa only [scheduleKW, BitVec.add_comm] using hh

end Agave.Ed25519.SHA512.Execution.Avx2
