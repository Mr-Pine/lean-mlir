import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixNumeratorTail

/-! Exact bb0:106--120 increment/copy region. The multiplication's original
word representation is retained, including the unnormalized increment. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def denominatorEnv (E : Env program.Γ) (r a : Pointer) (x : Words) : Env program.Γ :=
  E[%85 := .value (a.add 16#64), %86 := .value (a.add 32#64),
    %87 := .value (x 4), %88 := Ty.wrap #v[x 0, x 1],
    %89 := Ty.wrap #v[x 0 + 1#64, x 1], %90 := .value (r.add 16#64),
    %91 := Ty.wrap #v[x 2, x 3], %92 := .value (r.add 32#64)]

def denominatorStore (m : MemoryState) (r : Pointer) (x : Words) : MemoryState :=
  ((m.storeAt r (x 1 ++ (x 0 + 1#64))).storeAt (r.add 16#64) (x 3 ++ x 2)).storeAt
    (r.add 32#64) (x 4)

structure DenominatorRegisters (E : Env program.Γ) (r a : Pointer) : Prop where
  r32 : E.read (%32) = .value r
  a31 : E.read (%31) = .value a
  c9 : E.read (%9) = .value 16#64
  c10 : E.read (%10) = .value 32#64
  c18 : E.read (%18) = Ty.wrap #v[1#64, 0#64]

theorem denominator_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (hr : SmallRange s.mem r 40)
    (ha : SmallRange s.mem a 40) (hd : r.id ≠ a.id)
    (he : DenominatorRegisters E r a) :
    Cutpoint.segment (program p g) 0 106 15 E s =
      .value (denominatorEnv E r a (readLimbs s a),
        {s with mem := denominatorStore s.mem r (readLimbs s a)}) := by
  obtain ⟨e32,e31,e9,e10,e18⟩ := he
  have ga16 := ha.gep (k := 16) (by decide)
  have ga32 := ha.gep (k := 32) (by decide)
  have gr16 := (hr.storeAt r ((readLimbs s a) 1 ++ ((readLimbs s a) 0 + 1#64))).gep
    (k := 16) (by decide)
  have gr32 := ((hr.storeAt r ((readLimbs s a) 1 ++ ((readLimbs s a) 0 + 1#64))).storeAt
    (r.add 16#64) ((readLimbs s a) 3 ++ (readLimbs s a) 2)).gep
    (k := 32) (by decide)
  simp [readLimbs] at gr16 gr32
  norm_num only [Nat.cast_ofNat] at ga16 ga32 gr16 gr32
  have fa0 := ha.fits_add (k := 0) (count := 16) (by decide)
  have fa16 := ha.fits_add (k := 16) (count := 16) (by decide)
  have fa32 := ha.fits_add (k := 32) (count := 8) (by decide)
  have fr0 := hr.fits_add (k := 0) (count := 16) (by decide)
  have fr16 := hr.fits_add (k := 16) (count := 16) (by decide)
  have fr32 := hr.fits_add (k := 32) (count := 8) (by decide)
  have va0 := smallRange_add ha (k := 0) (count := 16) (by decide)
  have va16 := smallRange_add ha (k := 16) (count := 16) (by decide)
  simp only [Pointer.add_zero] at fa0 fr0 va0
  have hread (w : Nat) (v : BitVec w) (qoff : BitVec 64) (bits : Nat) :
      (s.mem.storeAt r v).readAt (a.add qoff) bits =
        s.mem.readAt (a.add qoff) bits :=
    MemoryState.readAt_storeAt_disjoint (p := r) (q := a.add qoff)
      (m := s.mem) (v := w) (w := bits) (Or.inl hd) v
  change List.foldlM Instr.run E (((program.bb0 p g).body.drop 106).take 15) s = _
  dsimp only [program.bb0, List.drop, List.take]
  simp (maxSteps := 1000000) (disch := first | assumption | decide)
    [List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
      Operation.load, Operation.store, Operation.gepInboundsIndex, GepIndex.inboundsOffset,
      Operation.GepSignedRange, EffectM.bind_eq, EffectM.pure_eq,
      PoisonOr.value_bind, mlir_env, mlir_effect, mlir_operation,
      e32,e31,e9,e10,e18, ga16,ga32,gr16,gr32,fa0,fa16,fa32,fr0,fr16,fr32,
      load_two_words, va0,va16, Fits.storeAt_iff, hread,
      denominatorEnv, denominatorStore, vector_two, pack_pair, readLimbs, Pointer.add_add, throwUBIf]

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
