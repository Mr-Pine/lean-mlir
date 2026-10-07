import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Serialization

/-! All 32 actual ascending byte stores, separated from serialization arithmetic. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def byteStoresEnv (E : Env program.Γ) (out : Pointer) : Env program.Γ :=
  E[%425 := .value (out.add 1#64),
    %426 := .value (out.add 2#64),
    %427 := .value (out.add 3#64),
    %428 := .value (out.add 4#64),
    %429 := .value (out.add 5#64),
    %430 := .value (out.add 6#64),
    %431 := .value (out.add 7#64),
    %432 := .value (out.add 8#64),
    %433 := .value (out.add 9#64),
    %434 := .value (out.add 10#64),
    %435 := .value (out.add 11#64),
    %436 := .value (out.add 12#64),
    %437 := .value (out.add 13#64),
    %438 := .value (out.add 14#64),
    %439 := .value (out.add 15#64),
    %440 := .value (out.add 16#64),
    %441 := .value (out.add 17#64),
    %442 := .value (out.add 18#64),
    %443 := .value (out.add 19#64),
    %444 := .value (out.add 20#64),
    %445 := .value (out.add 21#64),
    %446 := .value (out.add 22#64),
    %447 := .value (out.add 23#64),
    %448 := .value (out.add 24#64),
    %449 := .value (out.add 25#64),
    %450 := .value (out.add 26#64),
    %451 := .value (out.add 27#64),
    %452 := .value (out.add 28#64),
    %453 := .value (out.add 29#64),
    %454 := .value (out.add 30#64),
    %455 := .value (out.add 31#64)]

theorem byteStores_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (out : Pointer) (bytes : Fin 32 → BitVec 8)
    (hout : E.read (%arg0) = .value out) (hlive : SmallRange state.mem out 32)
    (hb0 : E.read (%356) = .value (bytes 0))
    (hb1 : E.read (%358) = .value (bytes 1))
    (hb2 : E.read (%360) = .value (bytes 2))
    (hb3 : E.read (%362) = .value (bytes 3))
    (hb4 : E.read (%364) = .value (bytes 4))
    (hb5 : E.read (%366) = .value (bytes 5))
    (hb6 : E.read (%371) = .value (bytes 6))
    (hb7 : E.read (%373) = .value (bytes 7))
    (hb8 : E.read (%375) = .value (bytes 8))
    (hb9 : E.read (%377) = .value (bytes 9))
    (hb10 : E.read (%379) = .value (bytes 10))
    (hb11 : E.read (%381) = .value (bytes 11))
    (hb12 : E.read (%383) = .value (bytes 12))
    (hb13 : E.read (%385) = .value (bytes 13))
    (hb14 : E.read (%387) = .value (bytes 14))
    (hb15 : E.read (%389) = .value (bytes 15))
    (hb16 : E.read (%391) = .value (bytes 16))
    (hb17 : E.read (%393) = .value (bytes 17))
    (hb18 : E.read (%395) = .value (bytes 18))
    (hb19 : E.read (%400) = .value (bytes 19))
    (hb20 : E.read (%402) = .value (bytes 20))
    (hb21 : E.read (%404) = .value (bytes 21))
    (hb22 : E.read (%406) = .value (bytes 22))
    (hb23 : E.read (%408) = .value (bytes 23))
    (hb24 : E.read (%410) = .value (bytes 24))
    (hb25 : E.read (%412) = .value (bytes 25))
    (hb26 : E.read (%414) = .value (bytes 26))
    (hb27 : E.read (%416) = .value (bytes 27))
    (hb28 : E.read (%418) = .value (bytes 28))
    (hb29 : E.read (%420) = .value (bytes 29))
    (hb30 : E.read (%422) = .value (bytes 30))
    (hb31 : E.read (%424) = .value (bytes 31))
    (hc1 : E.read (%1) = .value 4#64)
    (hc3 : E.read (%3) = .value 5#64)
    (hc5 : E.read (%5) = .value 6#64)
    (hc7 : E.read (%7) = .value 7#64)
    (hc9 : E.read (%9) = .value 8#64)
    (hc10 : E.read (%10) = .value 12#64)
    (hc11 : E.read (%11) = .value 13#64)
    (hc12 : E.read (%12) = .value 14#64)
    (hc13 : E.read (%13) = .value 16#64)
    (hc14 : E.read (%14) = .value 18#64)
    (hc15 : E.read (%15) = .value 19#64)
    (hc16 : E.read (%16) = .value 24#64)
    (hc17 : E.read (%17) = .value 20#64)
    (hc18 : E.read (%18) = .value 22#64)
    (hc19 : E.read (%19) = .value 25#64)
    (hc20 : E.read (%20) = .value 26#64)
    (hc21 : E.read (%21) = .value 28#64)
    (hc22 : E.read (%22) = .value 30#64)
    (hc52 : E.read (%52) = .value 1#64)
    (hc53 : E.read (%53) = .value 2#64)
    (hc54 : E.read (%54) = .value 3#64)
    (hc55 : E.read (%55) = .value 9#64)
    (hc56 : E.read (%56) = .value 10#64)
    (hc57 : E.read (%57) = .value 11#64)
    (hc58 : E.read (%58) = .value 15#64)
    (hc59 : E.read (%59) = .value 17#64)
    (hc60 : E.read (%60) = .value 21#64)
    (hc61 : E.read (%61) = .value 23#64)
    (hc62 : E.read (%62) = .value 27#64)
    (hc63 : E.read (%63) = .value 29#64)
    (hc64 : E.read (%64) = .value 31#64)
    : List.foldlM Instr.run E (((program.entry p g).body.drop 513).take 63) state =
      .value (byteStoresEnv E out,
        {state with mem := Agave.Ed25519.ScalarReduce32.Execution.storeBytes state.mem out bytes}) := by
  change E.args 0 = .value out at hout
  have hf0 := hlive.fits_add (k := 0) (count := 1) (by decide)
  have hf1 := hlive.fits_add (k := 1) (count := 1) (by decide)
  have hf2 := hlive.fits_add (k := 2) (count := 1) (by decide)
  have hf3 := hlive.fits_add (k := 3) (count := 1) (by decide)
  have hf4 := hlive.fits_add (k := 4) (count := 1) (by decide)
  have hf5 := hlive.fits_add (k := 5) (count := 1) (by decide)
  have hf6 := hlive.fits_add (k := 6) (count := 1) (by decide)
  have hf7 := hlive.fits_add (k := 7) (count := 1) (by decide)
  have hf8 := hlive.fits_add (k := 8) (count := 1) (by decide)
  have hf9 := hlive.fits_add (k := 9) (count := 1) (by decide)
  have hf10 := hlive.fits_add (k := 10) (count := 1) (by decide)
  have hf11 := hlive.fits_add (k := 11) (count := 1) (by decide)
  have hf12 := hlive.fits_add (k := 12) (count := 1) (by decide)
  have hf13 := hlive.fits_add (k := 13) (count := 1) (by decide)
  have hf14 := hlive.fits_add (k := 14) (count := 1) (by decide)
  have hf15 := hlive.fits_add (k := 15) (count := 1) (by decide)
  have hf16 := hlive.fits_add (k := 16) (count := 1) (by decide)
  have hf17 := hlive.fits_add (k := 17) (count := 1) (by decide)
  have hf18 := hlive.fits_add (k := 18) (count := 1) (by decide)
  have hf19 := hlive.fits_add (k := 19) (count := 1) (by decide)
  have hf20 := hlive.fits_add (k := 20) (count := 1) (by decide)
  have hf21 := hlive.fits_add (k := 21) (count := 1) (by decide)
  have hf22 := hlive.fits_add (k := 22) (count := 1) (by decide)
  have hf23 := hlive.fits_add (k := 23) (count := 1) (by decide)
  have hf24 := hlive.fits_add (k := 24) (count := 1) (by decide)
  have hf25 := hlive.fits_add (k := 25) (count := 1) (by decide)
  have hf26 := hlive.fits_add (k := 26) (count := 1) (by decide)
  have hf27 := hlive.fits_add (k := 27) (count := 1) (by decide)
  have hf28 := hlive.fits_add (k := 28) (count := 1) (by decide)
  have hf29 := hlive.fits_add (k := 29) (count := 1) (by decide)
  have hf30 := hlive.fits_add (k := 30) (count := 1) (by decide)
  have hf31 := hlive.fits_add (k := 31) (count := 1) (by decide)
  simp only [Pointer.add_zero] at hf0
  have live0 := hlive
  have live1 := live0.storeAt out (bytes 0)
  have hg1 := live1.gep (k := 1) (by decide)
  have live2 := live1.storeAt (out.add 1#64) (bytes 1)
  have hg2 := live2.gep (k := 2) (by decide)
  have live3 := live2.storeAt (out.add 2#64) (bytes 2)
  have hg3 := live3.gep (k := 3) (by decide)
  have live4 := live3.storeAt (out.add 3#64) (bytes 3)
  have hg4 := live4.gep (k := 4) (by decide)
  have live5 := live4.storeAt (out.add 4#64) (bytes 4)
  have hg5 := live5.gep (k := 5) (by decide)
  have live6 := live5.storeAt (out.add 5#64) (bytes 5)
  have hg6 := live6.gep (k := 6) (by decide)
  have live7 := live6.storeAt (out.add 6#64) (bytes 6)
  have hg7 := live7.gep (k := 7) (by decide)
  have live8 := live7.storeAt (out.add 7#64) (bytes 7)
  have hg8 := live8.gep (k := 8) (by decide)
  have live9 := live8.storeAt (out.add 8#64) (bytes 8)
  have hg9 := live9.gep (k := 9) (by decide)
  have live10 := live9.storeAt (out.add 9#64) (bytes 9)
  have hg10 := live10.gep (k := 10) (by decide)
  have live11 := live10.storeAt (out.add 10#64) (bytes 10)
  have hg11 := live11.gep (k := 11) (by decide)
  have live12 := live11.storeAt (out.add 11#64) (bytes 11)
  have hg12 := live12.gep (k := 12) (by decide)
  have live13 := live12.storeAt (out.add 12#64) (bytes 12)
  have hg13 := live13.gep (k := 13) (by decide)
  have live14 := live13.storeAt (out.add 13#64) (bytes 13)
  have hg14 := live14.gep (k := 14) (by decide)
  have live15 := live14.storeAt (out.add 14#64) (bytes 14)
  have hg15 := live15.gep (k := 15) (by decide)
  have live16 := live15.storeAt (out.add 15#64) (bytes 15)
  have hg16 := live16.gep (k := 16) (by decide)
  have live17 := live16.storeAt (out.add 16#64) (bytes 16)
  have hg17 := live17.gep (k := 17) (by decide)
  have live18 := live17.storeAt (out.add 17#64) (bytes 17)
  have hg18 := live18.gep (k := 18) (by decide)
  have live19 := live18.storeAt (out.add 18#64) (bytes 18)
  have hg19 := live19.gep (k := 19) (by decide)
  have live20 := live19.storeAt (out.add 19#64) (bytes 19)
  have hg20 := live20.gep (k := 20) (by decide)
  have live21 := live20.storeAt (out.add 20#64) (bytes 20)
  have hg21 := live21.gep (k := 21) (by decide)
  have live22 := live21.storeAt (out.add 21#64) (bytes 21)
  have hg22 := live22.gep (k := 22) (by decide)
  have live23 := live22.storeAt (out.add 22#64) (bytes 22)
  have hg23 := live23.gep (k := 23) (by decide)
  have live24 := live23.storeAt (out.add 23#64) (bytes 23)
  have hg24 := live24.gep (k := 24) (by decide)
  have live25 := live24.storeAt (out.add 24#64) (bytes 24)
  have hg25 := live25.gep (k := 25) (by decide)
  have live26 := live25.storeAt (out.add 25#64) (bytes 25)
  have hg26 := live26.gep (k := 26) (by decide)
  have live27 := live26.storeAt (out.add 26#64) (bytes 26)
  have hg27 := live27.gep (k := 27) (by decide)
  have live28 := live27.storeAt (out.add 27#64) (bytes 27)
  have hg28 := live28.gep (k := 28) (by decide)
  have live29 := live28.storeAt (out.add 28#64) (bytes 28)
  have hg29 := live29.gep (k := 29) (by decide)
  have live30 := live29.storeAt (out.add 29#64) (bytes 29)
  have hg30 := live30.gep (k := 30) (by decide)
  have live31 := live30.storeAt (out.add 30#64) (bytes 30)
  have hg31 := live31.gep (k := 31) (by decide)
  norm_num at hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    byteStoresEnv, Agave.Ed25519.ScalarReduce32.Execution.storeBytes, Operation.store,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf, hout,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23, hb24, hb25, hb26, hb27, hb28, hb29, hb30, hb31, hc1, hc3, hc5, hc7, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc52, hc53, hc54, hc55, hc56, hc57, hc58, hc59, hc60, hc61, hc62, hc63, hc64, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf17, hf18, hf19, hf20, hf21, hf22, hf23, hf24, hf25, hf26, hf27, hf28, hf29, hf30, hf31, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg31]

end Agave.Ed25519.Verifier.Execution.ScalarWide
