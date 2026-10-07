import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputSplitWords
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryStores

/-! Exact ten split-limb stores, at instructions 284–319 of the pinned wrapper. -/
set_option maxRecDepth 100000
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def splitStores (m : MemoryState) (low high : Pointer) (bytes : BitVec 512) : MemoryState :=
  ScalarMontgomeryMul.outputStores
    (ScalarMontgomeryMul.outputStores m low (lowSplitWords bytes)) high (highSplitWords bytes)

def splitEnv (E : Env program.Γ) (low high : Pointer) (bytes : BitVec 512) : Env program.Γ :=
  let v262 : BitVec 64 := (inputFragment bytes 0 56 0) &&& (4503599627370495#64)
  let v263 : BitVec 64 := funnel64 (inputFragment bytes 64 40 0) (inputFragment bytes 0 64 0) 12
  let v264 : Pointer := low.add 8#64
  let v265 : BitVec 64 := funnel64 (inputFragment bytes 128 32 0) (inputFragment bytes 104 24 40) 24
  let v266 : Pointer := low.add 16#64
  let v267 : BitVec 64 := (v265) &&& (4503599627370495#64)
  let v268 : BitVec 64 := funnel64 (inputFragment bytes 192 16 0) (inputFragment bytes 128 64 0) 36
  let v269 : Pointer := low.add 24#64
  let v270 : BitVec 64 := funnel64 (inputFragment bytes 256 8 0) (inputFragment bytes 208 48 16) 48
  let v271 : Pointer := low.add 32#64
  let v272 : BitVec 64 := (v270) &&& (4503599627370495#64)
  let v273 : BitVec 64 := (inputFragment bytes 256 64 0) >>> 4
  let v274 : BitVec 64 := (v273) &&& (4503599627370495#64)
  let v275 : BitVec 64 := funnel64 (inputFragment bytes 320 48 0) (inputFragment bytes 304 16 48) 8
  let v276 : Pointer := high.add 8#64
  let v277 : BitVec 64 := (v275) &&& (4503599627370495#64)
  let v278 : BitVec 64 := funnel64 (inputFragment bytes 384 32 0) (inputFragment bytes 320 64 0) 20
  let v279 : Pointer := high.add 16#64
  let v280 : BitVec 64 := funnel64 (inputFragment bytes 448 24 0) (inputFragment bytes 416 32 32) 32
  let v281 : Pointer := high.add 24#64
  let v282 : BitVec 64 := (v280) &&& (4503599627370495#64)
  let v283 : Pointer := high.add 32#64
  let v284 : BitVec 64 := (inputFragment bytes 448 64 0) >>> 20
  E[%262 := .value v262,
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
    %276 := .value v276,
    %277 := .value v277,
    %278 := .value v278,
    %279 := .value v279,
    %280 := .value v280,
    %281 := .value v281,
    %282 := .value v282,
    %283 := .value v283,
    %284 := .value v284]

theorem split_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (low high : Pointer) (bytes : BitVec 512)
    (hlow : E.read (%75) = .value low) (hhigh : E.read (%74) = .value high)
    (hlive : SmallRange state.mem low 40) (hive : SmallRange state.mem high 40)
    (hv105 : E.read (%105) = .value (inputFragment bytes 0 56 0))
    (hv110 : E.read (%110) = .value (inputFragment bytes 0 64 0))
    (hv118 : E.read (%118) = .value (inputFragment bytes 64 40 0))
    (hv127 : E.read (%127) = .value (inputFragment bytes 104 24 40))
    (hv141 : E.read (%141) = .value (inputFragment bytes 128 32 0))
    (hv151 : E.read (%151) = .value (inputFragment bytes 128 64 0))
    (hv159 : E.read (%159) = .value (inputFragment bytes 192 16 0))
    (hv173 : E.read (%173) = .value (inputFragment bytes 208 48 16))
    (hv177 : E.read (%177) = .value (inputFragment bytes 256 8 0))
    (hv195 : E.read (%195) = .value (inputFragment bytes 304 16 48))
    (hv197 : E.read (%197) = .value (inputFragment bytes 256 64 0))
    (hv210 : E.read (%210) = .value (inputFragment bytes 320 48 0))
    (hv215 : E.read (%215) = .value (inputFragment bytes 320 64 0))
    (hv228 : E.read (%228) = .value (inputFragment bytes 384 32 0))
    (hv237 : E.read (%237) = .value (inputFragment bytes 416 32 32))
    (hv246 : E.read (%246) = .value (inputFragment bytes 448 24 0))
    (hv261 : E.read (%261) = .value (inputFragment bytes 448 64 0))
    (hc1 : E.read (%1) = .value 4#64)
    (hc2 : E.read (%2) = .value 32#64)
    (hc6 : E.read (%6) = .value 48#64)
    (hc9 : E.read (%9) = .value 8#64)
    (hc10 : E.read (%10) = .value 12#64)
    (hc13 : E.read (%13) = .value 16#64)
    (hc16 : E.read (%16) = .value 24#64)
    (hc17 : E.read (%17) = .value 20#64)
    (hc25 : E.read (%25) = .value 36#64)
    (hc38 : E.read (%38) = .value 4503599627370495#64)
    : List.foldlM Instr.run E (((program.entry p g).body.drop 284).take 36) state =
      .value (splitEnv E low high bytes, {state with mem := splitStores state.mem low high bytes}) := by
  have hlf0 := hlive.fits_add (k := 0) (count := 8) (by decide)
  have hlf1 := hlive.fits_add (k := 8) (count := 8) (by decide)
  have hlf2 := hlive.fits_add (k := 16) (count := 8) (by decide)
  have hlf3 := hlive.fits_add (k := 24) (count := 8) (by decide)
  have hlf4 := hlive.fits_add (k := 32) (count := 8) (by decide)
  simp only [Pointer.add_zero] at hlf0
  have hlg1 := ((hlive).storeAt low (lowSplitWords bytes 0)).gep (k := 8) (by decide)
  have hlg2 := (((hlive).storeAt low (lowSplitWords bytes 0)).storeAt (low.add 8#64) (lowSplitWords bytes 1)).gep (k := 16) (by decide)
  have hlg3 := ((((hlive).storeAt low (lowSplitWords bytes 0)).storeAt (low.add 8#64) (lowSplitWords bytes 1)).storeAt (low.add 16#64) (lowSplitWords bytes 2)).gep (k := 24) (by decide)
  have hlg4 := (((((hlive).storeAt low (lowSplitWords bytes 0)).storeAt (low.add 8#64) (lowSplitWords bytes 1)).storeAt (low.add 16#64) (lowSplitWords bytes 2)).storeAt (low.add 24#64) (lowSplitWords bytes 3)).gep (k := 32) (by decide)
  have hhf0 := hive.fits_add (k := 0) (count := 8) (by decide)
  have hhf1 := hive.fits_add (k := 8) (count := 8) (by decide)
  have hhf2 := hive.fits_add (k := 16) (count := 8) (by decide)
  have hhf3 := hive.fits_add (k := 24) (count := 8) (by decide)
  have hhf4 := hive.fits_add (k := 32) (count := 8) (by decide)
  simp only [Pointer.add_zero] at hhf0
  have hhg1 := (((((((hive).storeAt low (lowSplitWords bytes 0)).storeAt (low.add 8#64) (lowSplitWords bytes 1)).storeAt (low.add 16#64) (lowSplitWords bytes 2)).storeAt (low.add 24#64) (lowSplitWords bytes 3)).storeAt (low.add 32#64) (lowSplitWords bytes 4)).storeAt high (highSplitWords bytes 0)).gep (k := 8) (by decide)
  have hhg2 := ((((((((hive).storeAt low (lowSplitWords bytes 0)).storeAt (low.add 8#64) (lowSplitWords bytes 1)).storeAt (low.add 16#64) (lowSplitWords bytes 2)).storeAt (low.add 24#64) (lowSplitWords bytes 3)).storeAt (low.add 32#64) (lowSplitWords bytes 4)).storeAt high (highSplitWords bytes 0)).storeAt (high.add 8#64) (highSplitWords bytes 1)).gep (k := 16) (by decide)
  have hhg3 := (((((((((hive).storeAt low (lowSplitWords bytes 0)).storeAt (low.add 8#64) (lowSplitWords bytes 1)).storeAt (low.add 16#64) (lowSplitWords bytes 2)).storeAt (low.add 24#64) (lowSplitWords bytes 3)).storeAt (low.add 32#64) (lowSplitWords bytes 4)).storeAt high (highSplitWords bytes 0)).storeAt (high.add 8#64) (highSplitWords bytes 1)).storeAt (high.add 16#64) (highSplitWords bytes 2)).gep (k := 24) (by decide)
  have hhg4 := ((((((((((hive).storeAt low (lowSplitWords bytes 0)).storeAt (low.add 8#64) (lowSplitWords bytes 1)).storeAt (low.add 16#64) (lowSplitWords bytes 2)).storeAt (low.add 24#64) (lowSplitWords bytes 3)).storeAt (low.add 32#64) (lowSplitWords bytes 4)).storeAt high (highSplitWords bytes 0)).storeAt (high.add 8#64) (highSplitWords bytes 1)).storeAt (high.add 16#64) (highSplitWords bytes 2)).storeAt (high.add 24#64) (highSplitWords bytes 3)).gep (k := 32) (by decide)
  simp [lowSplitWords, highSplitWords, funnel64] at hlg1 hlg2 hlg3 hlg4 hhg1 hhg2 hhg3 hhg4
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    splitStores, splitEnv, ScalarMontgomeryMul.outputStores, lowSplitWords, highSplitWords,
    funnel64, Operation.store, Operation.fshl, Operation.and, Operation.lshr, GepIndex.inboundsOffset,
    Operation.gepInboundsIndex, Operation.GepSignedRange,
    BinOp.compute, TernOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf,
    hlow, hhigh, hv105, hv110, hv118, hv127, hv141, hv151, hv159, hv173, hv177, hv195, hv197, hv210, hv215, hv228, hv237, hv246, hv261, hc1, hc2, hc6, hc9, hc10, hc13, hc16, hc17, hc25, hc38, hlf0, hlf1, hlf2, hlf3, hlf4, hhf0, hhf1, hhf2, hhf3, hhf4, hlg1, hlg2, hlg3, hlg4, hhg1, hhg2, hhg3, hhg4]

end Agave.Ed25519.Verifier.Execution.ScalarWide
