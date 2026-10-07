import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.FiveWordMemory
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.AddbackWords

/-! The exact wrapping additions and carry masks before the final subtraction. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 100000

def sumEnv (E : Env program.Γ) (a b : Fin 5 → BitVec 64) : Env program.Γ :=
  let v285 : BitVec 64 := b 0
  let v286 : BitVec 64 := a 0
  let v287 : BitVec 64 := (v286) + (v285)
  let v288 : BitVec 64 := (v287) &&& (4503599627370495#64)
  let v289 : BitVec 64 := b 1
  let v290 : BitVec 64 := a 1
  let v291 : BitVec 64 := (v287) >>> 52
  let v292 : BitVec 64 := (v291) + (v289)
  let v293 : BitVec 64 := (v292) + (v290)
  let v294 : BitVec 64 := (v293) &&& (4503599627370495#64)
  let v295 : BitVec 64 := b 2
  let v296 : BitVec 64 := a 2
  let v297 : BitVec 64 := (v293) >>> 52
  let v298 : BitVec 64 := (v296) + (v295)
  let v299 : BitVec 64 := (v298) + (v297)
  let v300 : BitVec 64 := (v299) &&& (4503599627370495#64)
  let v301 : BitVec 64 := b 3
  let v302 : BitVec 64 := a 3
  let v303 : BitVec 64 := (v299) >>> 52
  let v304 : BitVec 64 := (v302) + (v301)
  let v305 : BitVec 64 := (v304) + (v303)
  let v306 : BitVec 64 := (v305) &&& (4503599627370495#64)
  let v307 : BitVec 64 := b 4
  let v308 : BitVec 64 := a 4
  let v309 : BitVec 64 := (v305) >>> 52
  let v310 : BitVec 64 := (v308) + (v307)
  let v311 : BitVec 64 := (v310) + (v309)
  let v312 : BitVec 64 := (v311) &&& (4503599627370495#64)
  E[%285 := .value v285,
    %286 := .value v286,
    %287 := .value v287,
    %288 := .value v288,
    %289 := .value v289,
    %290 := .value v290,
    %291 := .value v291,
    %292 := .value v292,
    %293 := .value v293,
    %294 := .value v294,
    %295 := .value v295,
    %296 := .value v296,
    %297 := .value v297,
    %298 := .value v298,
    %299 := .value v299,
    %300 := .value v300,
    %301 := .value v301,
    %302 := .value v302,
    %303 := .value v303,
    %304 := .value v304,
    %305 := .value v305,
    %306 := .value v306,
    %307 := .value v307,
    %308 := .value v308,
    %309 := .value v309,
    %310 := .value v310,
    %311 := .value v311,
    %312 := .value v312]

def sumWords (a b : Fin 5 → BitVec 64) : Fin 5 → BitVec 64 :=
  let v285 : BitVec 64 := b 0
  let v286 : BitVec 64 := a 0
  let v287 : BitVec 64 := (v286) + (v285)
  let v288 : BitVec 64 := (v287) &&& (4503599627370495#64)
  let v289 : BitVec 64 := b 1
  let v290 : BitVec 64 := a 1
  let v291 : BitVec 64 := (v287) >>> 52
  let v292 : BitVec 64 := (v291) + (v289)
  let v293 : BitVec 64 := (v292) + (v290)
  let v294 : BitVec 64 := (v293) &&& (4503599627370495#64)
  let v295 : BitVec 64 := b 2
  let v296 : BitVec 64 := a 2
  let v297 : BitVec 64 := (v293) >>> 52
  let v298 : BitVec 64 := (v296) + (v295)
  let v299 : BitVec 64 := (v298) + (v297)
  let v300 : BitVec 64 := (v299) &&& (4503599627370495#64)
  let v301 : BitVec 64 := b 3
  let v302 : BitVec 64 := a 3
  let v303 : BitVec 64 := (v299) >>> 52
  let v304 : BitVec 64 := (v302) + (v301)
  let v305 : BitVec 64 := (v304) + (v303)
  let v306 : BitVec 64 := (v305) &&& (4503599627370495#64)
  let v307 : BitVec 64 := b 4
  let v308 : BitVec 64 := a 4
  let v309 : BitVec 64 := (v305) >>> 52
  let v310 : BitVec 64 := (v308) + (v307)
  let v311 : BitVec 64 := (v310) + (v309)
  let v312 : BitVec 64 := (v311) &&& (4503599627370495#64)
  ![v288, v294, v300, v306, v312]

theorem sum_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (a b : Fin 5 → BitVec 64) (low high : Pointer)
    (hlive : SmallRange state.mem low 40) (hive : SmallRange state.mem high 40)
    (ha : ∀ i : Fin 5, state.mem.readAt (low.add (BitVec.ofNat 64 (8 * i.val))) 64 = a i)
    (hb : ∀ i : Fin 5, state.mem.readAt (high.add (BitVec.ofNat 64 (8 * i.val))) 64 = b i)
    (hp74 : E.read (%74) = .value (high))
    (hp75 : E.read (%75) = .value (low))
    (hp276 : E.read (%276) = .value (high.add 8#64))
    (hp264 : E.read (%264) = .value (low.add 8#64))
    (hp279 : E.read (%279) = .value (high.add 16#64))
    (hp266 : E.read (%266) = .value (low.add 16#64))
    (hp281 : E.read (%281) = .value (high.add 24#64))
    (hp269 : E.read (%269) = .value (low.add 24#64))
    (hp283 : E.read (%283) = .value (high.add 32#64))
    (hp271 : E.read (%271) = .value (low.add 32#64))
    (hc38 : E.read (%38) = .value 4503599627370495#64)
    (hc32 : E.read (%32) = .value 52#64)
    : List.foldlM Instr.run E (((program.entry p g).body.drop 330).take 28) state =
      .value (sumEnv E a b, state) := by
  have haf0 := hlive.fits_add (k := 0) (count := 8) (by decide)
  have har0 := ha 0
  have haf1 := hlive.fits_add (k := 8) (count := 8) (by decide)
  have har1 := ha 1
  have haf2 := hlive.fits_add (k := 16) (count := 8) (by decide)
  have har2 := ha 2
  have haf3 := hlive.fits_add (k := 24) (count := 8) (by decide)
  have har3 := ha 3
  have haf4 := hlive.fits_add (k := 32) (count := 8) (by decide)
  have har4 := ha 4
  simp only [Pointer.add_zero] at haf0 har0
  have hbf0 := hive.fits_add (k := 0) (count := 8) (by decide)
  have hbr0 := hb 0
  have hbf1 := hive.fits_add (k := 8) (count := 8) (by decide)
  have hbr1 := hb 1
  have hbf2 := hive.fits_add (k := 16) (count := 8) (by decide)
  have hbr2 := hb 2
  have hbf3 := hive.fits_add (k := 24) (count := 8) (by decide)
  have hbr3 := hb 3
  have hbf4 := hive.fits_add (k := 32) (count := 8) (by decide)
  have hbr4 := hb 4
  simp only [Pointer.add_zero] at hbf0 hbr0
  norm_num at har0 har1 har2 har3 har4 hbr0 hbr1 hbr2 hbr3 hbr4
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run, sumEnv,
    Operation.load, Operation.add, Operation.and, Operation.lshr, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf, hc38, hc32, hp74, hp75, hp276, hp264, hp279, hp266, hp281, hp269, hp283, hp271,
    haf0, haf1, haf2, haf3, haf4, har0, har1, har2, har3, har4, hbf0, hbf1, hbf2, hbf3, hbf4, hbr0, hbr1, hbr2, hbr3, hbr4]

theorem sumEnv_words (E : Env program.Γ) (a b : Fin 5 → BitVec 64) :
    (sumEnv E a b).read (%288) = .value (sumWords a b 0) ∧
    (sumEnv E a b).read (%294) = .value (sumWords a b 1) ∧
    (sumEnv E a b).read (%300) = .value (sumWords a b 2) ∧
    (sumEnv E a b).read (%306) = .value (sumWords a b 3) ∧
    (sumEnv E a b).read (%312) = .value (sumWords a b 4) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Agave.Ed25519.Verifier.Execution.ScalarWide
