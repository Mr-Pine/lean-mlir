import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2Execution
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! Exact bb13 execution of the first block in the two-block AVX2 path.
The shared TailSchedule premise describes the sixteen K+W words in %83;
no execution or compression result is assumed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic

/-- Register interpretation at the actual bb13 header. -/
structure BulkTailReady (E : Env program.Γ) (scratch : Pointer) (r : Nat) (s : Spec.State) : Prop where
  scratch : E.read (%83) = .value scratch
  counter : E.read (%573) = .value (BitVec.ofNat 64 r)
  a : E.read (%578) = .value s.a
  b : E.read (%579) = .value s.b
  c : E.read (%580) = .value s.c
  d : E.read (%581) = .value s.d
  e : E.read (%575) = .value s.e
  f : E.read (%577) = .value s.f
  g : E.read (%576) = .value s.g
  h : E.read (%574) = .value s.h
  one : E.read (%1) = .value 1#64
  limit : E.read (%17) = .value 80#64
  rot14 : E.read (%36) = .value 50#64
  rot18 : E.read (%37) = .value 46#64
  rot41 : E.read (%38) = .value 23#64
  rot28 : E.read (%39) = .value 36#64
  rot34 : E.read (%40) = .value 30#64
  rot39 : E.read (%41) = .value 25#64
  mask : E.read (%44) = .value 15#64

/-- Every bb13 destination in its exact source order. -/
def bulkTailBodyEnv (E : Env program.Γ) (scratch : Pointer) (r : Nat)
    (s : Spec.State) (kw : Word) : Env program.Γ :=
  let v586 := s.h + kw
  let v587 := s.e.rotateRight 14
  let v588 := s.e.rotateRight 18
  let v589 := v587 ^^^ v588
  let v590 := s.e.rotateRight 41
  let v591 := v589 ^^^ v590
  let v592 := v586 + v591
  let v593 := s.f ^^^ s.g
  let v594 := v593 &&& s.e
  let v595 := v594 ^^^ s.g
  let v596 := v592 + v595
  let v597 := s.a.rotateRight 28
  let v598 := s.a.rotateRight 34
  let v599 := v597 ^^^ v598
  let v600 := s.a.rotateRight 39
  let v601 := v599 ^^^ v600
  let v602 := v596 + v601
  let v603 := s.c ^^^ s.b
  let v604 := v603 &&& s.a
  let v605 := s.c &&& s.b
  let v606 := v604 ^^^ v605
  let v607 := v602 + v606
  let v608 := s.d + v596
  E[%582 := .value (BitVec.ofNat 64 r &&& 15#64),
    %583 := .value (BitVec.ofNat 64 (r + 1)),
    %584 := .value (scratch.add (BitVec.ofNat 64 (8 * (r - 64)))),
    %585 := .value kw,
    %586 := .value v586, %587 := .value v587, %588 := .value v588,
    %589 := .value v589, %590 := .value v590, %591 := .value v591,
    %592 := .value v592, %593 := .value v593, %594 := .value v594,
    %595 := .value v595, %596 := .value v596, %597 := .value v597,
    %598 := .value v598, %599 := .value v599, %600 := .value v600,
    %601 := .value v601, %602 := .value v602, %603 := .value v603,
    %604 := .value v604, %605 := .value v605, %606 := .value v606,
    %607 := .value v607, %608 := .value v608,
    %609 := .value (BitVec.ofBool (decide (r + 1 = 80)))]

/-- The actual loop backedge assigns bb13's nine block parameters. -/
def bulkTailNextEnv (E : Env program.Γ) (r : Nat) (s : Spec.State) : Env program.Γ :=
  E[%573 := .value (BitVec.ofNat 64 r),
    %574 := .value s.h, %575 := .value s.e, %576 := .value s.g,
    %577 := .value s.f, %578 := .value s.a, %579 := .value s.b,
    %580 := .value s.c, %581 := .value s.d]

/-- Execute all 28 body instructions from the imported bb13. The source's
signed/unsigned counter flags and all three GEP flags are discharged. -/
theorem bulkTail_body (E : Env program.Γ) (mem : GlobalState) (scratch : Pointer)
    (r : Nat) (s : Spec.State) (words : List Word)
    (hlo : 64 ≤ r) (hhi : r < 80)
    (h : BulkTailReady E scratch r s) (hs : TailSchedule mem.mem scratch words) :
    List.foldlM Instr.run E program.bb13.body mem =
      .value (bulkTailBodyEnv E scratch r s
        (constants.toList.getD r 0 + words.getD r 0), mem) := by
  rcases h with ⟨h83, h573, ha, hb, hc, hd, he, hf, hg, hh,
    h1, h17, h36, h37, h38, h39, h40, h41, h44⟩
  have hinc := tail_index_add r hlo hhi
  have hidx := tail_index_gep r hlo hhi
  have hgep := hs.live.gep (k := 8 * (r - 64)) (by omega)
  have hfits := hs.live.fits_add (k := 8 * (r - 64)) (count := 8) (by omega)
  have hread := hs.words r hlo hhi
  have heq := tail_index_eq80 r hhi
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb13, List.foldlM_cons, List.foldlM_nil, Instr.run,
    bulkTailBodyEnv, h83, h573, ha, hb, hc, hd, he, hf, hg, hh,
    h1, h17, h36, h37, h38, h39, h40, h41, h44,
    hinc, hidx, hgep, hfits, hread, heq,
    GepIndex.inboundsOffset, Operation.load,
    Operation.and, Operation.xor, hadd, Operation.icmp,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.SHA512.Execution.Avx2
