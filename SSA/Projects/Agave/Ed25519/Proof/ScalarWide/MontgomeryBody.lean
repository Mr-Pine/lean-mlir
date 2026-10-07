import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ProductPhase
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryCarry
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryWordCorrect
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Frame

/-! Actual product/carry/tail composition from the end of the allocation prefix.
No machine-phase correctness is assumed: entry facts are registers, liveness,
freshness, and the two mathematical limb bounds. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
open LeanMLIR.RIR
open Agave.Ed25519.Bridge
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

structure BodyReady (E : Env program.Γ) (out left right : Pointer)
    (scratch : Fin 9 → Pointer) : Prop where
  product : ProductReady E left right scratch
  out : E.read (%arg0) = .value out
  scratch0 : E.read (%24) = .value (scratch 0)
  c5 : E.read (%5) = .value 1439961107955227#64
  c6 : E.read (%6) = .value 4503599627370495#64
  c7 : E.read (%7) = .value 671914833335277#128
  c8 : E.read (%8) = .value 52#128
  c9 : E.read (%9) = .value 3916664325105025#128
  c10 : E.read (%10) = .value 1367801#128
  c11 : E.read (%11) = .value 44#128
  c12 : E.read (%12) = .value (-671914833335277 : BitVec 64)
  c13 : E.read (%13) = .value 63#64
  c14 : E.read (%14) = .value (-3916664325105025 : BitVec 64)
  c15 : E.read (%15) = .value (-1367801 : BitVec 64)
  c16 : E.read (%16) = .value (-17592186044416 : BitVec 64)
  c17 : E.read (%17) = .value 0#64
  c18 : E.read (%18) = .value 671914833335277#64
  c19 : E.read (%19) = .value 3916664325105025#64
  c20 : E.read (%20) = .value 52#64
  c21 : E.read (%21) = .value 1367801#64
  c22 : E.read (%22) = .value 17592186044416#64
  c23 : E.read (%23) = .value 0#128

def bodyEnv (E : Env program.Γ) (a b : Fin 5 → BitVec 64)
    (out left right : Pointer) : Env program.Γ :=
  tailEnv (carryWordEnv (productEnvs E a b left right 8) (columnWords a b left right))
    (quotient52 a b left right) out

def bodyState (state : GlobalState) (a b : Fin 5 → BitVec 64)
    (out left right : Pointer) (scratch : Fin 9 → Pointer) : GlobalState :=
  tailState (productStates state a b left right scratch 8)
    (quotient52 a b left right) out scratch

/-- Complete execution of imported body instructions 33–285. -/
theorem body_run (p : Primitives)
    (hblack : p.blackBoxByte = Agave.Ed25519.Encoding.Decompress.Execution.BlackBox.program.call)
    (E : Env program.Γ) (state : GlobalState)
    (a b : Fin 5 → BitVec 64) (out left right : Pointer) (scratch : Fin 9 → Pointer)
    (hr : BodyReady E out left right scratch) (hwf : state.WF)
    (hout : SmallRange state.mem out 40)
    (hlive : SmallRange state.mem left 40) (hrive : SmallRange state.mem right 40)
    (hscratch : ∀ i, Fits state.mem (scratch i) 128)
    (hdleft : ∀ i, (scratch i).id ≠ left.id) (hdright : ∀ i, (scratch i).id ≠ right.id)
    (ha : ∀ i : Fin 5, state.mem.readAt (left.add (BitVec.ofNat 64 (8 * i.val))) 64 = a i)
    (hb : ∀ i : Fin 5, state.mem.readAt (right.add (BitVec.ofNat 64 (8 * i.val))) 64 = b i)
    (habound : ∀ i, (a i).toNat < 2 ^ 52) (hbbound : ∀ i, (b i).toNat < 2 ^ 52)
    (hbcanonical : limbValue (fun i => (b i).toNat) < subgroupOrder) :
    (program.entry p).runBodyFrom E 33 state =
      .value (bodyEnv E a b out left right, bodyState state a b out left right scratch) := by
  let ep := productEnvs E a b left right 8
  let sp := productStates state a b left right scratch 8
  let z := columnWords a b left right
  let ec := carryWordEnv ep z
  let x := quotient52 a b left right
  have hp := product_run p E state a b left right scratch hr.product hlive hrive
    hscratch hdleft hdright ha hb
  have hc5 := hr.c5
  have hc6 := hr.c6
  have hc7 := hr.c7
  have hc8 := hr.c8
  have hc9 := hr.c9
  have hc10 := hr.c10
  have hc11 := hr.c11
  have hc12 := hr.c12
  have hc13 := hr.c13
  have hc14 := hr.c14
  have hc15 := hr.c15
  have hc16 := hr.c16
  have hc17 := hr.c17
  have hc18 := hr.c18
  have hc19 := hr.c19
  have hc20 := hr.c20
  have hc21 := hr.c21
  have hc22 := hr.c22
  have hc23 := hr.c23
  have hoffset1 := hr.product.offset1
  have hoffset2 := hr.product.offset2
  have hoffset3 := hr.product.offset3
  have hoffset4 := hr.product.offset4
  have hscratch1 := hr.product.scratch1
  have hscratch2 := hr.product.scratch2
  have hscratch3 := hr.product.scratch3
  have hscratch4 := hr.product.scratch4
  have hscratch5 := hr.product.scratch5
  have hscratch6 := hr.product.scratch6
  have hscratch7 := hr.product.scratch7
  have hscratch8 := hr.product.scratch8
  have hscratch0 := hr.scratch0
  have houtreg := hr.out
  have hcarry : List.foldlM Instr.run ep (((program.entry p).body.drop 122).take 86) sp =
      .value (ec, sp) := by
    apply carry_word_run p ep sp z <;>
      simp [ep, z, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, columnWords, column1Word, column2Word, column3Word, column4Word, column5Word, column6Word, column7Word, column8Word,
        hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env]
  have hq := carryWordEnv_quotient ep z
  have hx (i : Fin 5) := quotient52_widen a b left right habound hbbound hbcanonical i
  change ∀ i : Fin 5, (x i).setWidth 64 = wordQuotientLimbs z i at hx
  have htail : TailReady ec x out scratch := by
    constructor
    · exact hq.1.trans (congrArg LeanMLIR.RIR.PoisonOr.value (hx 0).symm)
    · exact hq.2.1.trans (congrArg LeanMLIR.RIR.PoisonOr.value (hx 1).symm)
    · exact hq.2.2.1.trans (congrArg LeanMLIR.RIR.PoisonOr.value (hx 2).symm)
    · exact hq.2.2.2.1.trans (congrArg LeanMLIR.RIR.PoisonOr.value (hx 3).symm)
    · exact hq.2.2.2.2.trans (congrArg LeanMLIR.RIR.PoisonOr.value (hx 4).symm)
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_arg]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using houtreg
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 24 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hscratch0
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 25 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hscratch1
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 26 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hscratch2
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 27 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hscratch3
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 28 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hscratch4
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 29 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hscratch5
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 30 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hscratch6
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 31 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hscratch7
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 32 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hscratch8
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 1 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hoffset1
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 2 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hoffset2
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 3 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hoffset3
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 4 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hoffset4
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 6 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hc6
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 12 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hc12
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 13 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hc13
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 14 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hc14
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 15 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hc15
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 16 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hc16
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 17 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hc17
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 18 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hc18
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 19 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hc19
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 20 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hc20
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 21 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hc21
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 22 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hc22
    · rw [show ec = carryWordEnv ep z from rfl, carryWordEnv_read_early ep z 23 rfl (by decide)]
      simpa [ep, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, column8Env, mlir_env] using hc23
  rw [hp, runBodyFrom_chunk hcarry]
  exact tail_run p hblack ec sp x out scratch htail
    (productStates_wf state a b left right scratch hwf 8)
    (productStates_smallRange state a b left right scratch out 40 hout 8)
    (fun i => productStates_fits state a b left right scratch (scratch i) 128 (hscratch i) 8)

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
