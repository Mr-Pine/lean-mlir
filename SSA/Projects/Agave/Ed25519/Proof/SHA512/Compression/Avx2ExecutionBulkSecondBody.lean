import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2Execution
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkSecondArithmetic

/-! Concrete execution of one imported bb15 second-block round. The loop
consumes the full cached K+W schedule at %82, without changing global state. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

/-- Exact live-register interpretation at bb15. Its counter measures bytes. -/
structure BulkSecondReady (E : Env program.Γ) (cache : Pointer)
    (r : Nat) (s : Spec.State) : Prop where
  cache : E.read (%82) = .value cache
  counter : E.read (%618) = .value (BitVec.ofNat 64 (8 * r))
  a : E.read (%623) = .value s.a
  b : E.read (%624) = .value s.b
  c : E.read (%625) = .value s.c
  d : E.read (%626) = .value s.d
  e : E.read (%620) = .value s.e
  f : E.read (%622) = .value s.f
  g : E.read (%621) = .value s.g
  h : E.read (%619) = .value s.h
  eight : E.read (%3) = .value 8#64
  limit : E.read (%79) = .value 640#64
  rot14 : E.read (%36) = .value 50#64
  rot18 : E.read (%37) = .value 46#64
  rot41 : E.read (%38) = .value 23#64
  rot28 : E.read (%39) = .value 36#64
  rot34 : E.read (%40) = .value 30#64
  rot39 : E.read (%41) = .value 25#64

/-- Concrete cached schedule contents; no execution or compression conclusion
is assumed. All eighty words belong to the same live 640-byte cache. -/
structure BulkSecondSchedule (mem : MemoryState) (cache : Pointer)
    (words : List Word) : Prop where
  live : SmallRange mem cache 640
  words : ∀ r, r < 80 →
    mem.readAt (cache.add (BitVec.ofNat 64 (8 * r))) 64 =
      constants.toList.getD r 0 + words.getD r 0

/-- Final live working words consumed by the imported bb16 feed-forward. -/
structure BulkSecondFinalReady (E : Env program.Γ) (s : Spec.State) : Prop where
  a : E.read (%651) = .value s.a
  b : E.read (%623) = .value s.b
  c : E.read (%624) = .value s.c
  d : E.read (%625) = .value s.d
  e : E.read (%652) = .value s.e
  f : E.read (%620) = .value s.f
  g : E.read (%622) = .value s.g
  h : E.read (%621) = .value s.h

/-- Every bb15 destination, in its imported source order. -/
def bulkSecondBodyEnv (E : Env program.Γ) (cache : Pointer) (r : Nat)
    (s : Spec.State) (kw : Word) : Env program.Γ :=
  let v630 := s.h + kw
  let v631 := s.e.rotateRight 14
  let v632 := s.e.rotateRight 18
  let v633 := v631 ^^^ v632
  let v634 := s.e.rotateRight 41
  let v635 := v633 ^^^ v634
  let v636 := v630 + v635
  let v637 := s.f ^^^ s.g
  let v638 := v637 &&& s.e
  let v639 := v638 ^^^ s.g
  let v640 := v636 + v639
  let v641 := s.a.rotateRight 28
  let v642 := s.a.rotateRight 34
  let v643 := v641 ^^^ v642
  let v644 := s.a.rotateRight 39
  let v645 := v643 ^^^ v644
  let v646 := v640 + v645
  let v647 := s.c ^^^ s.b
  let v648 := v647 &&& s.a
  let v649 := s.c &&& s.b
  let v650 := v648 ^^^ v649
  let v651 := v646 + v650
  let v652 := s.d + v640
  E[%627 := .value (cache.add (BitVec.ofNat 64 (8 * r))),
    %628 := .value (BitVec.ofNat 64 (8 * (r + 1))),
    %629 := .value kw,
    %630 := .value v630, %631 := .value v631, %632 := .value v632,
    %633 := .value v633, %634 := .value v634, %635 := .value v635,
    %636 := .value v636, %637 := .value v637, %638 := .value v638,
    %639 := .value v639, %640 := .value v640, %641 := .value v641,
    %642 := .value v642, %643 := .value v643, %644 := .value v644,
    %645 := .value v645, %646 := .value v646, %647 := .value v647,
    %648 := .value v648, %649 := .value v649, %650 := .value v650,
    %651 := .value v651, %652 := .value v652,
    %653 := .value (BitVec.ofBool (decide (r + 1 = 80)))]

/-- The actual simultaneous nine-parameter bb15 backedge assignment. -/
def bulkSecondNextEnv (E : Env program.Γ) (r : Nat) (s : Spec.State) :
    Env program.Γ :=
  E[%618 := .value (BitVec.ofNat 64 (8 * r)),
    %619 := .value s.h, %620 := .value s.e, %621 := .value s.g,
    %622 := .value s.f, %623 := .value s.a, %624 := .value s.b,
    %625 := .value s.c, %626 := .value s.d]

/-- The body has the same already-proved round arithmetic as bb6. This proof
also discharges both add overflow flags, every inbounds GEP flag and the load. -/
theorem bulkSecond_body (E : Env program.Γ) (mem : GlobalState) (cache : Pointer)
    (r : Nat) (s : Spec.State) (words : List Word) (hhi : r < 80)
    (h : BulkSecondReady E cache r s)
    (hs : BulkSecondSchedule mem.mem cache words) :
    List.foldlM Instr.run E program.bb15.body mem =
      .value (bulkSecondBodyEnv E cache r s
        (constants.toList.getD r 0 + words.getD r 0), mem) := by
  rcases h with ⟨h82, h618, ha, hb, hc, hd, he, hf, hg, hh,
    h3, h79, h36, h37, h38, h39, h40, h41⟩
  have hinc := bulkSecond_index_add r hhi
  have hidx := bulkSecond_index_gep r hhi
  have hgep := hs.live.gep (k := 8 * r) (by omega)
  have hfits := hs.live.fits_add (k := 8 * r) (count := 8) (by omega)
  have hread := hs.words r hhi
  have heq := bulkSecond_index_eq640 r hhi
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb15, List.foldlM_cons, List.foldlM_nil, Instr.run,
    bulkSecondBodyEnv, h82, h618, ha, hb, hc, hd, he, hf, hg, hh,
    h3, h79, h36, h37, h38, h39, h40, h41,
    hinc, hidx, hgep, hfits, hread, heq,
    GepIndex.inboundsOffset, Operation.load,
    Operation.and, Operation.xor, hadd, Operation.icmp,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.SHA512.Execution.Avx2
