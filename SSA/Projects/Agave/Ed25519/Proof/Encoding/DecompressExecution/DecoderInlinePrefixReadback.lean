import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixCallsite

/-! The two actual sqrt input buffers contain the exact typed word model. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul SerialPoint
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
open SmallOrder.Execution (PrivateFrame)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
attribute [local irreducible] machine

theorem denominator_splices (old : BitVec 320) (x : Words) :
    Memory.spliceBits (Memory.spliceBits (Memory.spliceBits old 0 (x 1 ++ (x 0 + 1#64)))
      128 (x 3 ++ x 2)) 256 (x 4) = limbBytes (denominatorMachine x) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Memory.getLsbD_spliceBits, limbBytes, denominatorMachine,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, BitVec.getLsbD_append]
  grind

theorem denominator_read320 (m : MemoryState) (r : Pointer) (x : Words)
    (hr : SmallRange m r 40) :
    (denominatorStore m r x).readAt r 320 = limbBytes (denominatorMachine x) := by
  have h0 := MemoryState.readAt_add_storeAt (p := r) (off := 0#64)
    (v := 320) hr.fits (hr.no_wrap (k := 0) (by decide)) (by decide) (x 1 ++ (x 0 + 1#64))
  have h16 := MemoryState.readAt_add_storeAt (p := r) (off := 16#64)
    (v := 320) (m := m.storeAt r (x 1 ++ (x 0 + 1#64)))
    hr.fits.storeAt (hr.no_wrap (k := 16) (by decide)) (by decide) (x 3 ++ x 2)
  have h32 := MemoryState.readAt_add_storeAt (p := r) (off := 32#64)
    (v := 320) (m := (m.storeAt r (x 1 ++ (x 0 + 1#64))).storeAt (r.add 16#64) (x 3 ++ x 2))
    hr.fits.storeAt.storeAt (hr.no_wrap (k := 32) (by decide)) (by decide) (x 4)
  simp only [Pointer.add_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.zero_mul, Nat.reduceMul] at h0 h16 h32
  simp only [denominatorStore, h32, h16, h0, denominator_splices]

theorem denominator_readLimbs (s : GlobalState) (r : Pointer) (x : Words)
    (hr : SmallRange s.mem r 40) :
    readLimbs {s with mem := denominatorStore s.mem r x} r = denominatorMachine x :=
  readLimbs_of_limbBytes _ r _ (((hr.storeAt _ _).storeAt _ _).storeAt _ _)
    (denominator_read320 s.mem r x hr)

theorem denominator_read_ne (s : GlobalState) (r a : Pointer) (x : Words)
    (hd : r.id ≠ a.id) :
    readLimbs {s with mem := denominatorStore s.mem r x} a = readLimbs s a := by
  funext i
  let q := a.add (BitVec.ofNat 64 (8 * i.val))
  change (denominatorStore s.mem r x).readAt q 64 = s.mem.readAt q 64
  unfold denominatorStore
  rw [MemoryState.readAt_storeAt_disjoint
    (p := r.add 32#64) (q := q) (w := 64) (Or.inl hd)]
  rw [MemoryState.readAt_storeAt_disjoint
    (p := r.add 16#64) (q := q) (w := 64) (Or.inl hd)]
  exact MemoryState.readAt_storeAt_disjoint
    (p := r) (q := q) (m := s.mem) (w := 64) (Or.inl hd) _

theorem product_readback (g : Globals) (sg : SqrtRatio.Globals) (s : GlobalState)
    (input : Pointer) (bytes : BitVec 256) (hwf : s.WF)
    (hin : Verifier.Execution.Dalek.ReadBytes s input 32 bytes) (ready : Ready g sg s) :
    readLimbs (productState g s input) (slot1 s) =
      machine ((parsedWord bytes).square 1).limbs curveDWord.limbs := by
  unfold productState
  rw [readLimbs_storeLimbs _ _ _ (numerator_live s input _ _ (slot1_live s hwf)),
    numerator_square_readback s input bytes hwf hin,
    (private_ready (numerator_frame s input hwf) hwf ready).curveD_read]
  rfl

theorem sqrtInput_denominator (g : Globals) (sg : SqrtRatio.Globals) (s : GlobalState)
    (input : Pointer) (bytes : BitVec 256) (hwf : s.WF)
    (hin : Verifier.Execution.Dalek.ReadBytes s input 32 bytes) (ready : Ready g sg s) :
    readLimbs (sqrtInputState g s input) (slot2 s) = (denominatorWord bytes).limbs := by
  unfold sqrtInputState
  rw [denominator_readLimbs _ _ _ (product_live g s input _ _ (slot2_live s hwf)),
    product_readback g sg s input bytes hwf hin ready, denominatorMachine_eq]
  rfl

theorem sqrtInput_numerator (g : Globals) (s : GlobalState)
    (input : Pointer) (bytes : BitVec 256) (hwf : s.WF)
    (hin : Verifier.Execution.Dalek.ReadBytes s input 32 bytes) :
    readLimbs (sqrtInputState g s input) (slot3 s) = (numeratorWord bytes).limbs := by
  unfold sqrtInputState
  rw [denominator_read_ne _ _ _ _
    (by intro h; have := congrArg BlockId.id h; simp only [slot2_id, slot3_id] at this; omega)]
  unfold productState
  rw [readLimbs_storeLimbs_ne _ _ _ _
    (by intro h; have := congrArg BlockId.id h; simp only [slot1_id, slot3_id] at this; omega)]
  exact numerator_readback s input bytes hwf hin

/-- Concrete call-site observations, with neither register-readiness nor a
restated arithmetic contract among the invocation prerequisites. -/
theorem sqrt_callsite (g : Globals) (sg : SqrtRatio.Globals) (s : GlobalState)
    (out input : Pointer) (bytes : BitVec 256) (hwf : s.WF)
    (hin : Verifier.Execution.Dalek.ReadBytes s input 32 bytes) (ready : Ready g sg s) :
    Cutpoint.segment (program (decodePrimitives sg) g) 0 0 121 (initialEnv out input) s =
        .value (sqrtInputEnv g s out input, sqrtInputState g s input) ∧
      PrivateFrame s (sqrtInputState g s input) ∧
      Ready g sg (sqrtInputState g s input) ∧
      SmallRange (sqrtInputState g s input).mem (slot0 s) 48 ∧
      SmallRange (sqrtInputState g s input).mem (slot3 s) 40 ∧
      SmallRange (sqrtInputState g s input).mem (slot2 s) 40 ∧
      readLimbs (sqrtInputState g s input) (slot3 s) = (numeratorWord bytes).limbs ∧
      readLimbs (sqrtInputState g s input) (slot2 s) = (denominatorWord bytes).limbs ∧
      (sqrtInputEnv g s out input).read (%30) = .value (slot0 s) ∧
      (sqrtInputEnv g s out input).read (%33) = .value (slot3 s) ∧
      (sqrtInputEnv g s out input).read (%32) = .value (slot2 s) :=
  ⟨through_denominator_segment g sg s out input hwf hin.1 ready,
    sqrtInput_frame g s input hwf, sqrtInput_ready g sg s input hwf ready,
    sqrtInput_live g s input _ _ (slot0_live s hwf),
    sqrtInput_live g s input _ _ (slot3_live s hwf),
    sqrtInput_live g s input _ _ (slot2_live s hwf),
    sqrtInput_numerator g s input bytes hwf hin,
    sqrtInput_denominator g sg s input bytes hwf hin ready, rfl, rfl, rfl⟩

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
