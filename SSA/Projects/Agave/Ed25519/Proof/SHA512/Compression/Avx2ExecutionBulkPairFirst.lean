import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairSecond

/-! Exact execution of the first scalar round in the imported bb12 pair body. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

structure BulkPairFirstReady (E : Env program.Γ) (scratch : Pointer) (j : Nat)
    (s : Spec.State) : Prop where
  scratchPtr : E.read (%83) = .value scratch
  slot : E.read (%471) = .value (BitVec.ofNat 64 j)
  a : E.read (%484) = .value s.a
  b : E.read (%485) = .value s.b
  c : E.read (%486) = .value s.c
  d : E.read (%487) = .value s.d
  e : E.read (%481) = .value s.e
  f : E.read (%483) = .value s.f
  g : E.read (%482) = .value s.g
  h : E.read (%480) = .value s.h
  eight : E.read (%3) = .value 8#64
  shift : E.read (%35) = .value 4#64
  rot14 : E.read (%36) = .value 50#64
  rot18 : E.read (%37) = .value 46#64
  rot41 : E.read (%38) = .value 23#64
  rot28 : E.read (%39) = .value 36#64
  rot34 : E.read (%40) = .value 30#64
  rot39 : E.read (%41) = .value 25#64

def bulkPairFirstEnv (E : Env program.Γ) (scratch : Pointer) (j : Nat) (s : Spec.State)
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
  E[%516 := .value (BitVec.ofNat 64 (16*j)),
    %517 := .value (scratch.add (BitVec.ofNat 64 (16*j))), %518 := .value kw,
    %519 := .value v221, %520 := .value v222, %521 := .value v223,
    %522 := .value v224, %523 := .value v225, %524 := .value v226,
    %525 := .value v227, %526 := .value v228, %527 := .value v229,
    %528 := .value v230, %529 := .value v231, %530 := .value v232,
    %531 := .value v233, %532 := .value v234, %533 := .value v235,
    %534 := .value v236, %535 := .value v237, %536 := .value v238,
    %537 := .value v239, %538 := .value v240, %539 := .value v241,
    %540 := .value v242, %541 := .value v243]

private theorem bulk_pair_slot_shift (j : Nat) (hj : j < 8) :
    Operation.shl {nsw := true, nuw := true}
      (.value (BitVec.ofNat 64 j)) (.value 4#64) =
      .value (BitVec.ofNat 64 (16*j)) := by
  interval_cases j <;> decide

private theorem bulk_pair_slot_gep (j : Nat) (hj : j < 8) :
    Operation.gepInboundsIndex 1 (.value (BitVec.ofNat 64 (16*j))) =
      .value (Int.ofNat (16*j)) := by
  interval_cases j <;> decide

/-- The first round establishes every input of the following scalar slice. -/
theorem bulkPairFirstEnv_second_ready (E : Env program.Γ) (scratch : Pointer)
    (j : Nat) (s : Spec.State) (kw : Word) (h : BulkPairFirstReady E scratch j s) :
    BulkPairSecondReady (bulkPairFirstEnv E scratch j s kw)
      (scratch.add (BitVec.ofNat 64 (16*j))) (tailRound s kw) := by
  rcases h with ⟨hp, hj, ha, hb, hc, hd, he, hf, hg, hh, h8, h4,
    h14, h18, h41, h28, h34, h39⟩
  constructor <;> simp [bulkPairFirstEnv, tailRound, bigSigma0, bigSigma1,
    ha, hb, hc, he, hf, hg, h8, h14, h18, h41, h28, h34, h39, mlir_env]

/-- The imported bb12 instructions at offsets 28 through 53 inclusive.
The signed and unsigned shift and pointer flags are discharged from j < 8. -/
theorem bulk_pair_first_body (E : Env program.Γ) (mem : GlobalState) (scratch : Pointer)
    (j : Nat) (s : Spec.State) (kw : Word) (hj : j < 8)
    (h : BulkPairFirstReady E scratch j s) (hm : SmallRange mem.mem scratch 128)
    (hread : mem.mem.readAt (scratch.add (BitVec.ofNat 64 (16*j))) 64 = kw) :
    List.foldlM Instr.run E ((program.bb12.body.drop 28).take 26) mem =
      .value (bulkPairFirstEnv E scratch j s kw, mem) := by
  have hshift := bulk_pair_slot_shift j hj
  have hidx := bulk_pair_slot_gep j hj
  have hgep := hm.gep (k := 16*j) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  have hfits : Fits mem.mem (scratch.add (BitVec.ofNat 64 (16*j))) 64 :=
    hm.fits_add (k := 16*j) (count := 8) (by omega)
  rcases h with ⟨hp, hslot, ha, hb, hc, hd, he, hf, hg, hh, h8, h4,
    h14, h18, h41, h28, h34, h39⟩
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb12, List.foldlM_cons, List.foldlM_nil, Instr.run,
    bulkPairFirstEnv, hp, hslot, ha, hb, hc, hd, he, hf, hg, hh,
    h4, h14, h18, h41, h28, h34, h39, hshift, hidx, hgep, hfits, hread,
    GepIndex.inboundsOffset, Operation.load, Operation.and, Operation.xor, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    BinOp.compute, TernOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.SHA512.Execution.Avx2
