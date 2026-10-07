import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.DispatchProgram
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! The first round of the imported scalar backend, at the exact bb4 body
slice 50..76. Message decoding precedes this slice; its concrete register
value and the live constant load are the only data premises. This lemma
proves a standard SHA-512 round, not an assumed compression result. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

namespace Agave.Ed25519.SHA512.Execution.Dispatch
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

/-- The compiler adds the two disjoint choice terms in the first round. -/
theorem scalar_choose_add (e f g : Word) :
    (e &&& f) + (g &&& (e ^^^ (-1 : Word))) = choose e f g := by
  have hdis : (e &&& f) &&& (g &&& (e ^^^ (-1 : Word))) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_zero]
    have hm : (-1 : Word).getLsbD i = true := by
      change (BitVec.allOnes 64).getLsbD i = true
      simp only [BitVec.getLsbD_allOnes, hi, decide_true]
    rw [hm]
    cases e.getLsbD i <;> cases f.getLsbD i <;> cases g.getLsbD i <;> simp [BitVec.getLsbD]
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ hdis]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [choose, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_xor, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  have hm : (-1 : Word).getLsbD i = true := by
    change (BitVec.allOnes 64).getLsbD i = true
    simp only [BitVec.getLsbD_allOnes, hi, decide_true]
  rw [hm]
  cases e.getLsbD i <;> cases f.getLsbD i <;> cases g.getLsbD i <;> simp [BitVec.getLsbD]

/-- Source-shaped values in the first scalar round. -/
def scalarFirstRound (s : Spec.State) (word constant : Word) : Spec.State :=
  let t := (s.e &&& s.f) + s.h + (s.g &&& (s.e ^^^ (-1 : Word))) +
    bigSigma1 s.e + word + constant
  let maj := (s.a &&& (s.b ^^^ s.c)) ^^^ (s.b &&& s.c)
  ⟨(bigSigma0 s.a + maj) + t, s.a, s.b, s.c, t + s.d, s.e, s.f, s.g⟩

theorem scalarFirstRound_eq (s : Spec.State) (word constant : Word) :
    scalarFirstRound s word constant = Spec.round s word constant := by
  have hm : (s.a &&& (s.b ^^^ s.c)) ^^^ (s.b &&& s.c) = majority s.a s.b s.c := by
    simpa only [BitVec.and_comm, BitVec.xor_comm] using majority_source s.a s.b s.c
  have ht : (s.e &&& s.f) + s.h + (s.g &&& (s.e ^^^ (-1 : Word))) =
      choose s.e s.f s.g + s.h := by
    rw [← scalar_choose_add]
    ac_rfl
  simp only [scalarFirstRound, Spec.round, hm, ht]
  congr 1 <;> ac_rfl

structure ScalarFirstRoundReady (E : Env program.Γ) (s : Spec.State)
    (word : Word) (constants : Pointer) : Prop where
  a : E.read (%201) = .value s.a
  b : E.read (%199) = .value s.b
  c : E.read (%198) = .value s.c
  d : E.read (%197) = .value s.d
  e : E.read (%196) = .value s.e
  f : E.read (%195) = .value s.f
  g : E.read (%194) = .value s.g
  h : E.read (%193) = .value s.h
  word : E.read (%204) = .value word
  constants : E.read (%23) = .value constants
  rot14 : E.read (%19) = .value 50#64
  rot18 : E.read (%20) = .value 46#64
  rot41 : E.read (%21) = .value 23#64
  notMask : E.read (%22) = .value (-1 : Word)
  rot28 : E.read (%24) = .value 36#64
  rot34 : E.read (%25) = .value 30#64
  rot39 : E.read (%26) = .value 25#64

/-- Every destination in the original twenty-seven-instruction round. -/
def scalarFirstRoundEnv (E : Env program.Γ) (s : Spec.State)
    (word constant : Word) : Env program.Γ :=
  let v250 := s.e.rotateRight 14
  let v251 := s.e.rotateRight 18
  let v252 := v250 ^^^ v251
  let v253 := s.e.rotateRight 41
  let v254 := v252 ^^^ v253
  let v255 := s.e &&& s.f
  let v256 := s.e ^^^ (-1 : Word)
  let v257 := s.g &&& v256
  let v259 := v255 + s.h
  let v260 := v259 + v257
  let v261 := v260 + v254
  let v262 := v261 + word
  let v263 := v262 + constant
  let v264 := s.a.rotateRight 28
  let v265 := s.a.rotateRight 34
  let v266 := v264 ^^^ v265
  let v267 := s.a.rotateRight 39
  let v268 := v266 ^^^ v267
  let v269 := s.a &&& s.b
  let v270 := s.b ^^^ s.c
  let v271 := s.a &&& v270
  let v272 := s.b &&& s.c
  let v273 := v271 ^^^ v272
  let v274 := v268 + v273
  let v275 := v263 + s.d
  let v276 := v274 + v263
  E[%250 := .value v250, %251 := .value v251, %252 := .value v252,
    %253 := .value v253, %254 := .value v254, %255 := .value v255,
    %256 := .value v256, %257 := .value v257, %258 := .value constant,
    %259 := .value v259, %260 := .value v260, %261 := .value v261,
    %262 := .value v262, %263 := .value v263, %264 := .value v264,
    %265 := .value v265, %266 := .value v266, %267 := .value v267,
    %268 := .value v268, %269 := .value v269, %270 := .value v270,
    %271 := .value v271, %272 := .value v272, %273 := .value v273,
    %274 := .value v274, %275 := .value v275, %276 := .value v276]

/-- Exact imported round-slice execution, including its volatile K load.
The modeled memory and allocation state are unchanged. -/
theorem scalar_first_round_body (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (word constant : Word) (constants : Pointer)
    (h : ScalarFirstRoundReady E s word constants)
    (hf : Fits state.mem constants 64)
    (hr : state.mem.readAt constants 64 = constant) :
    List.foldlM Instr.run E (program.bb4.body.drop 50 |>.take 27) state =
      .value (scalarFirstRoundEnv E s word constant, state) := by
  rcases h with ⟨ha, hb, hc, hd, he, hf', hg, hh, hw, hk,
    h19, h20, h21, h22, h24, h25, h26⟩
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    scalarFirstRoundEnv, ha, hb, hc, hd, he, hf', hg, hh, hw, hk,
    h19, h20, h21, h22, h24, h25, h26, hf, hr,
    Operation.load, Operation.and, Operation.xor, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

/-- The two newly computed state registers are exactly the standard round;
the remaining six state components are the standard register rotation. -/
theorem scalar_first_round_result (E : Env program.Γ) (s : Spec.State)
    (word constant : Word) :
    (scalarFirstRoundEnv E s word constant).read (%276) =
      .value (Spec.round s word constant).a ∧
    (scalarFirstRoundEnv E s word constant).read (%275) =
      .value (Spec.round s word constant).e := by
  rw [← scalarFirstRound_eq]
  simp [scalarFirstRoundEnv, scalarFirstRound, bigSigma0, bigSigma1, mlir_env]

/-- Register locations read by the second unrolled scalar round. -/
structure ScalarSecondRoundReady (E : Env program.Γ) (s : Spec.State) : Prop where
  a : E.read (%276) = .value s.a
  b : E.read (%201) = .value s.b
  c : E.read (%199) = .value s.c
  d : E.read (%198) = .value s.d
  e : E.read (%275) = .value s.e
  f : E.read (%196) = .value s.f
  g : E.read (%195) = .value s.g
  h : E.read (%194) = .value s.h

/-- All eight state components at the real second-round cut point agree
with the independent standard round, alongside exact successful execution. -/
theorem scalar_first_round_transition (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (word constant : Word) (constants : Pointer)
    (h : ScalarFirstRoundReady E s word constants)
    (hf : Fits state.mem constants 64)
    (hr : state.mem.readAt constants 64 = constant) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 50 |>.take 27) state =
      .value (E', state) ∧ ScalarSecondRoundReady E' (Spec.round s word constant) := by
  refine ⟨scalarFirstRoundEnv E s word constant,
    scalar_first_round_body E state s word constant constants h hf hr, ?_⟩
  have ha := (scalar_first_round_result E s word constant).1
  have he := (scalar_first_round_result E s word constant).2
  refine ⟨ha, ?_, ?_, ?_, he, ?_, ?_, ?_⟩ <;>
    simp [scalarFirstRoundEnv, Spec.round, mlir_env,
      h.a, h.b, h.c, h.e, h.f, h.g]

end Agave.Ed25519.SHA512.Execution.Dispatch
