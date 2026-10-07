import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairSecond

/-! Exact execution of the second scalar round in the imported bb12 pair body. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

structure BulkPairSecondReady (E : Env program.Γ) (pairptr : Pointer) (s : Spec.State) : Prop where
  pairPtr : E.read (%517) = .value pairptr
  a : E.read (%540) = .value s.a
  b : E.read (%484) = .value s.b
  c : E.read (%485) = .value s.c
  d : E.read (%486) = .value s.d
  e : E.read (%541) = .value s.e
  f : E.read (%481) = .value s.f
  g : E.read (%483) = .value s.g
  h : E.read (%482) = .value s.h
  eight : E.read (%3) = .value 8#64
  rot14 : E.read (%36) = .value 50#64
  rot18 : E.read (%37) = .value 46#64
  rot41 : E.read (%38) = .value 23#64
  rot28 : E.read (%39) = .value 36#64
  rot34 : E.read (%40) = .value 30#64
  rot39 : E.read (%41) = .value 25#64

def bulkPairSecondEnv (E : Env program.Γ) (pairptr : Pointer) (s : Spec.State)
    (kw : Word) : Env program.Γ :=
  let v246 := s.e.rotateRight 14
  let v247 := s.e.rotateRight 18
  let v248 := v246 ^^^ v247
  let v249 := s.e.rotateRight 41
  let v250 := v248 ^^^ v249
  let v251 := s.g ^^^ s.f
  let v252 := s.e &&& v251
  let v253 := v252 ^^^ s.g
  let v254 := v253 + s.h
  let v255 := v254 + v250
  let v256 := v255 + kw
  let v257 := s.a.rotateRight 28
  let v258 := s.a.rotateRight 34
  let v259 := v257 ^^^ v258
  let v260 := s.a.rotateRight 39
  let v261 := v259 ^^^ v260
  let v262 := s.c ^^^ s.b
  let v263 := s.a &&& v262
  let v264 := s.c &&& s.b
  let v265 := v263 ^^^ v264
  let v266 := v261 + v265
  let v267 := v266 + v256
  let v268 := v256 + s.d
  E[%542 := .value (pairptr.add 8#64), %543 := .value kw,
    %544 := .value v246, %545 := .value v247, %546 := .value v248,
    %547 := .value v249, %548 := .value v250, %549 := .value v251,
    %550 := .value v252, %551 := .value v253, %552 := .value v254,
    %553 := .value v255, %554 := .value v256, %555 := .value v257,
    %556 := .value v258, %557 := .value v259, %558 := .value v260,
    %559 := .value v261, %560 := .value v262, %561 := .value v263,
    %562 := .value v264, %563 := .value v265, %564 := .value v266,
    %565 := .value v267, %566 := .value v268]

/-- The register interpretation after the second round, before bb12's store. -/
structure BulkPairSecondFinalReady (E : Env program.Γ) (s : Spec.State) : Prop where
  a : E.read (%565) = .value s.a
  b : E.read (%540) = .value s.b
  c : E.read (%484) = .value s.c
  d : E.read (%485) = .value s.d
  e : E.read (%566) = .value s.e
  f : E.read (%541) = .value s.f
  g : E.read (%481) = .value s.g
  h : E.read (%483) = .value s.h

theorem bulkPairSecondEnv_final_ready (E : Env program.Γ) (pairptr : Pointer)
    (s : Spec.State) (kw : Word) (h : BulkPairSecondReady E pairptr s) :
    BulkPairSecondFinalReady (bulkPairSecondEnv E pairptr s kw) (pairSecondState s kw) := by
  rcases h with ⟨hp, ha, hb, hc, hd, he, hf, hg, hh, h8, h14, h18, h41, h28, h34, h39⟩
  constructor <;> simp [bulkPairSecondEnv, pairSecondState, bigSigma0, bigSigma1,
    ha, hb, hc, he, hf, hg, mlir_env]

/-- The imported bb12 instructions at offsets 54 through 78 inclusive. -/
theorem bulk_pair_second_body (E : Env program.Γ) (mem : GlobalState) (pairptr : Pointer)
    (s : Spec.State) (kw : Word) (h : BulkPairSecondReady E pairptr s)
    (hm : SmallRange mem.mem pairptr 16)
    (hread : mem.mem.readAt (pairptr.add 8#64) 64 = kw) :
    List.foldlM Instr.run E ((program.bb12.body.drop 54).take 25) mem =
      .value (bulkPairSecondEnv E pairptr s kw, mem) := by
  have hgep := hm.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  have hfits : Fits mem.mem (pairptr.add 8#64) 64 :=
    hm.fits_add (k := 8) (count := 8) (by decide)
  rcases h with ⟨hp, ha, hb, hc, hd, he, hf, hg, hh, h8, h14, h18, h41, h28, h34, h39⟩
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb12, List.foldlM_cons, List.foldlM_nil, Instr.run,
    bulkPairSecondEnv, hp, ha, hb, hc, hd, he, hf, hg, hh,
    h14, h18, h41, h28, h34, h39, hgep, hfits, hread,
    GepIndex.inboundsOffset, Operation.load, Operation.and, Operation.xor, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.SHA512.Execution.Avx2
