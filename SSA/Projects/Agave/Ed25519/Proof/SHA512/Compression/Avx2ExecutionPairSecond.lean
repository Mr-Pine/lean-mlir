import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2Execution

/-! Exact execution of the second scalar round in the imported bb5 pair body. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

structure PairSecondReady (E : Env program.Γ) (pairptr : Pointer) (s : Spec.State) : Prop where
  pairPtr : E.read (%219) = .value pairptr
  a : E.read (%242) = .value s.a
  b : E.read (%187) = .value s.b
  c : E.read (%188) = .value s.c
  d : E.read (%189) = .value s.d
  e : E.read (%243) = .value s.e
  f : E.read (%184) = .value s.f
  g : E.read (%186) = .value s.g
  h : E.read (%185) = .value s.h
  eight : E.read (%3) = .value 8#64
  rot14 : E.read (%36) = .value 50#64
  rot18 : E.read (%37) = .value 46#64
  rot41 : E.read (%38) = .value 23#64
  rot28 : E.read (%39) = .value 36#64
  rot34 : E.read (%40) = .value 30#64
  rot39 : E.read (%41) = .value 25#64

def pairSecondEnv (E : Env program.Γ) (pairptr : Pointer) (s : Spec.State)
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
  E[%244 := .value (pairptr.add 8#64), %245 := .value kw,
    %246 := .value v246, %247 := .value v247, %248 := .value v248,
    %249 := .value v249, %250 := .value v250, %251 := .value v251,
    %252 := .value v252, %253 := .value v253, %254 := .value v254,
    %255 := .value v255, %256 := .value v256, %257 := .value v257,
    %258 := .value v258, %259 := .value v259, %260 := .value v260,
    %261 := .value v261, %262 := .value v262, %263 := .value v263,
    %264 := .value v264, %265 := .value v265, %266 := .value v266,
    %267 := .value v267, %268 := .value v268]

def pairSecondState (s : Spec.State) (kw : Word) : Spec.State :=
  let t := (s.e &&& (s.g ^^^ s.f) ^^^ s.g) + s.h + bigSigma1 s.e + kw
  ⟨(bigSigma0 s.a + ((s.a &&& (s.c ^^^ s.b)) ^^^ (s.c &&& s.b))) + t,
    s.a, s.b, s.c, t + s.d, s.e, s.f, s.g⟩

theorem pairSecondState_eq_avxRound (s : Spec.State) (kw : Word) :
    pairSecondState s kw = Spec.avxRound s kw := by
  have hmaj : (s.a &&& (s.c ^^^ s.b)) ^^^ (s.c &&& s.b) = majority s.a s.b s.c := by
    simpa only [BitVec.and_comm] using majority_source s.a s.b s.c
  simp only [pairSecondState, Spec.avxRound, hmaj]
  congr 1 <;> ac_rfl

theorem pairSecondState_eq_round (s : Spec.State) (word constant : Word) :
    pairSecondState s (constant + word) = Spec.round s word constant := by
  rw [pairSecondState_eq_avxRound, avxRound_eq_round]

/-- The register interpretation after the second round, before bb5's store. -/
structure PairSecondFinalReady (E : Env program.Γ) (s : Spec.State) : Prop where
  a : E.read (%267) = .value s.a
  b : E.read (%242) = .value s.b
  c : E.read (%187) = .value s.c
  d : E.read (%188) = .value s.d
  e : E.read (%268) = .value s.e
  f : E.read (%243) = .value s.f
  g : E.read (%184) = .value s.g
  h : E.read (%186) = .value s.h

theorem pairSecondEnv_final_ready (E : Env program.Γ) (pairptr : Pointer)
    (s : Spec.State) (kw : Word) (h : PairSecondReady E pairptr s) :
    PairSecondFinalReady (pairSecondEnv E pairptr s kw) (pairSecondState s kw) := by
  rcases h with ⟨hp, ha, hb, hc, hd, he, hf, hg, hh, h8, h14, h18, h41, h28, h34, h39⟩
  constructor <;> simp [pairSecondEnv, pairSecondState, bigSigma0, bigSigma1,
    ha, hb, hc, he, hf, hg, mlir_env]

/-- The imported bb5 instructions at offsets 53 through 77 inclusive. -/
theorem pair_second_body (E : Env program.Γ) (mem : GlobalState) (pairptr : Pointer)
    (s : Spec.State) (kw : Word) (h : PairSecondReady E pairptr s)
    (hm : SmallRange mem.mem pairptr 16)
    (hread : mem.mem.readAt (pairptr.add 8#64) 64 = kw) :
    List.foldlM Instr.run E ((program.bb5.body.drop 53).take 25) mem =
      .value (pairSecondEnv E pairptr s kw, mem) := by
  have hgep := hm.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  have hfits : Fits mem.mem (pairptr.add 8#64) 64 :=
    hm.fits_add (k := 8) (count := 8) (by decide)
  rcases h with ⟨hp, ha, hb, hc, hd, he, hf, hg, hh, h8, h14, h18, h41, h28, h34, h39⟩
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb5, List.foldlM_cons, List.foldlM_nil, Instr.run,
    pairSecondEnv, hp, ha, hb, hc, hd, he, hf, hg, hh,
    h14, h18, h41, h28, h34, h39, hgep, hfits, hread,
    GepIndex.inboundsOffset, Operation.load, Operation.and, Operation.xor, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.SHA512.Execution.Avx2
