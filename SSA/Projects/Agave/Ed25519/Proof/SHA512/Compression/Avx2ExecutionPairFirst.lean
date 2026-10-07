import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairSecond

/-! Exact execution of the first scalar round in the imported bb5 pair body. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

structure PairFirstReady (E : Env program.Γ) (scratch : Pointer) (j : Nat)
    (s : Spec.State) : Prop where
  scratchPtr : E.read (%81) = .value scratch
  slot : E.read (%174) = .value (BitVec.ofNat 64 j)
  a : E.read (%187) = .value s.a
  b : E.read (%188) = .value s.b
  c : E.read (%189) = .value s.c
  d : E.read (%190) = .value s.d
  e : E.read (%184) = .value s.e
  f : E.read (%186) = .value s.f
  g : E.read (%185) = .value s.g
  h : E.read (%183) = .value s.h
  eight : E.read (%3) = .value 8#64
  shift : E.read (%35) = .value 4#64
  rot14 : E.read (%36) = .value 50#64
  rot18 : E.read (%37) = .value 46#64
  rot41 : E.read (%38) = .value 23#64
  rot28 : E.read (%39) = .value 36#64
  rot34 : E.read (%40) = .value 30#64
  rot39 : E.read (%41) = .value 25#64

def pairFirstEnv (E : Env program.Γ) (scratch : Pointer) (j : Nat) (s : Spec.State)
    (kw : Word) : Env program.Γ :=
  let v221 := s.h + kw
  let v222 := s.e.rotateRight 14
  let v223 := s.e.rotateRight 18
  let v224 := v222 ^^^ v223
  let v225 := s.e.rotateRight 41
  let v226 := v224 ^^^ v225
  let v227 := v221 + v226
  let v228 := s.f ^^^ s.g
  let v229 := v228 &&& s.e
  let v230 := v229 ^^^ s.g
  let v231 := v227 + v230
  let v232 := s.a.rotateRight 28
  let v233 := s.a.rotateRight 34
  let v234 := v232 ^^^ v233
  let v235 := s.a.rotateRight 39
  let v236 := v234 ^^^ v235
  let v237 := v231 + v236
  let v238 := s.c ^^^ s.b
  let v239 := v238 &&& s.a
  let v240 := s.c &&& s.b
  let v241 := v239 ^^^ v240
  let v242 := v237 + v241
  let v243 := s.d + v231
  E[%218 := .value (BitVec.ofNat 64 (16*j)),
    %219 := .value (scratch.add (BitVec.ofNat 64 (16*j))), %220 := .value kw,
    %221 := .value v221, %222 := .value v222, %223 := .value v223,
    %224 := .value v224, %225 := .value v225, %226 := .value v226,
    %227 := .value v227, %228 := .value v228, %229 := .value v229,
    %230 := .value v230, %231 := .value v231, %232 := .value v232,
    %233 := .value v233, %234 := .value v234, %235 := .value v235,
    %236 := .value v236, %237 := .value v237, %238 := .value v238,
    %239 := .value v239, %240 := .value v240, %241 := .value v241,
    %242 := .value v242, %243 := .value v243]

private theorem pair_slot_shift (j : Nat) (hj : j < 8) :
    Operation.shl {nsw := true, nuw := true}
      (.value (BitVec.ofNat 64 j)) (.value 4#64) =
      .value (BitVec.ofNat 64 (16*j)) := by
  interval_cases j <;> decide

private theorem pair_slot_gep (j : Nat) (hj : j < 8) :
    Operation.gepInboundsIndex 1 (.value (BitVec.ofNat 64 (16*j))) =
      .value (Int.ofNat (16*j)) := by
  interval_cases j <;> decide

/-- The first round establishes every input of the following scalar slice. -/
theorem pairFirstEnv_second_ready (E : Env program.Γ) (scratch : Pointer)
    (j : Nat) (s : Spec.State) (kw : Word) (h : PairFirstReady E scratch j s) :
    PairSecondReady (pairFirstEnv E scratch j s kw)
      (scratch.add (BitVec.ofNat 64 (16*j))) (tailRound s kw) := by
  rcases h with ⟨hp, hj, ha, hb, hc, hd, he, hf, hg, hh, h8, h4,
    h14, h18, h41, h28, h34, h39⟩
  constructor <;> simp [pairFirstEnv, tailRound, bigSigma0, bigSigma1,
    ha, hb, hc, he, hf, hg, h8, h14, h18, h41, h28, h34, h39, mlir_env]

/-- The imported bb5 instructions at offsets 27 through 52 inclusive.
The signed and unsigned shift and pointer flags are discharged from j < 8. -/
theorem pair_first_body (E : Env program.Γ) (mem : GlobalState) (scratch : Pointer)
    (j : Nat) (s : Spec.State) (kw : Word) (hj : j < 8)
    (h : PairFirstReady E scratch j s) (hm : SmallRange mem.mem scratch 128)
    (hread : mem.mem.readAt (scratch.add (BitVec.ofNat 64 (16*j))) 64 = kw) :
    List.foldlM Instr.run E ((program.bb5.body.drop 27).take 26) mem =
      .value (pairFirstEnv E scratch j s kw, mem) := by
  have hshift := pair_slot_shift j hj
  have hidx := pair_slot_gep j hj
  have hgep := hm.gep (k := 16*j) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  have hfits : Fits mem.mem (scratch.add (BitVec.ofNat 64 (16*j))) 64 :=
    hm.fits_add (k := 16*j) (count := 8) (by omega)
  rcases h with ⟨hp, hslot, ha, hb, hc, hd, he, hf, hg, hh, h8, h4,
    h14, h18, h41, h28, h34, h39⟩
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb5, List.foldlM_cons, List.foldlM_nil, Instr.run,
    pairFirstEnv, hp, hslot, ha, hb, hc, hd, he, hf, hg, hh,
    h4, h14, h18, h41, h28, h34, h39, hshift, hidx, hgep, hfits, hread,
    GepIndex.inboundsOffset, Operation.load, Operation.and, Operation.xor, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    BinOp.compute, TernOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.SHA512.Execution.Avx2
