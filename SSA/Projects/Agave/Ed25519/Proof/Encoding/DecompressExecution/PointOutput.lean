import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Output
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.LimbMemory

/-! The actual success CFG after X and T have been computed: copy Y, construct
Z=1, copy all four coordinates, and store the Option tag. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open Verifier.Execution.Dalek (ReadBytes OutputFrame smallRange_add)

def finishPointState (s : GlobalState) (point y : Pointer) : GlobalState :=
  {s with mem := ((s.mem.storeAt (point.add 40#64) (s.mem.readAt y 320)).storeAt
    (point.add 80#64) (1#64)).storeAt (point.add 88#64) (0#256)}

def finishPointBits (old : BitVec 1280) (y : BitVec 320) : BitVec 1280 :=
  Memory.spliceBits (Memory.spliceBits (Memory.spliceBits old 320 y)
    640 (1#64)) 704 (0#256)

/-- The retained X/T slices and initialized Y/Z form the exact Rust payload. -/
theorem finishPointBits_coordinates (old : BitVec 1280) (x y t : BitVec 320)
    (hx : old.extractLsb' 0 320 = x) (ht : old.extractLsb' 960 320 = t) :
    finishPointBits old y = t ++ (1#320) ++ y ++ x := by
  change finishPointBits old y = t ++ (0#256 ++ 1#64) ++ y ++ x
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hxbit := congrArg (fun b : BitVec 320 => b.getLsbD i) hx
  have htbit := congrArg (fun b : BitVec 320 => b.getLsbD (i - 960)) ht
  simp only [BitVec.getLsbD_extractLsb'] at hxbit htbit
  simp only [finishPointBits, Memory.getLsbD_spliceBits, BitVec.getLsbD_append,
    BitVec.getLsbD_zero]
  clear hx ht
  grind only

theorem finishPointState_live (h : SmallRange s.mem q bytes) (point y : Pointer) :
    SmallRange (finishPointState s point y).mem q bytes :=
  ((h.storeAt _ _).storeAt _ _).storeAt _ _

/-- Exact wide read after the one memcpy, one scalar store, and one memset. -/
theorem finishPointState_read (s : GlobalState) (point y : Pointer)
    (h : SmallRange s.mem point 160) :
    ReadBytes (finishPointState s point y) point 160
      (finishPointBits (s.mem.readAt point 1280) (s.mem.readAt y 320)) := by
  refine ⟨finishPointState_live h point y, ?_⟩
  have h40 := MemoryState.readAt_add_storeAt (p := point) (off := 40#64)
    (v := 1280) h.fits (h.no_wrap (k := 40) (by decide)) (by decide)
    (s.mem.readAt y 320)
  have h80 := MemoryState.readAt_add_storeAt (p := point) (off := 80#64)
    (v := 1280) (m := s.mem.storeAt (point.add 40#64) (s.mem.readAt y 320))
    h.fits.storeAt (h.no_wrap (k := 80) (by decide)) (by decide) (1#64)
  have h88 := MemoryState.readAt_add_storeAt (p := point) (off := 88#64)
    (v := 1280) (m := (s.mem.storeAt (point.add 40#64)
      (s.mem.readAt y 320)).storeAt (point.add 80#64) (1#64))
    h.fits.storeAt.storeAt (h.no_wrap (k := 88) (by decide)) (by decide) (0#256)
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul] at h40 h80 h88
  simp only [finishPointState, finishPointBits, h88, h80, h40]

/-- Link the output-byte observation to the previously computed X/T fields. -/
theorem finishPointState_coordinates (s : GlobalState) (point yptr : Pointer)
    (x y t : BitVec 320) (hp : SmallRange s.mem point 160)
    (hx : s.mem.readAt point 320 = x)
    (hy : s.mem.readAt yptr 320 = y)
    (ht : s.mem.readAt (point.add 120#64) 320 = t) :
    ReadBytes (finishPointState s point yptr) point 160
      (t ++ (1#320) ++ y ++ x) := by
  have hfirst := MemoryState.readAt_add_of_readAt (p := point) (off := 0#64)
    (v := 1280) (w := 320) hp.fits (hp.no_wrap (k := 0) (by decide))
    (by decide) (rfl : s.mem.readAt point 1280 = s.mem.readAt point 1280)
  have hlast := MemoryState.readAt_add_of_readAt (p := point) (off := 120#64)
    (v := 1280) (w := 320) hp.fits (hp.no_wrap (k := 120) (by decide))
    (by decide) (rfl : s.mem.readAt point 1280 = s.mem.readAt point 1280)
  simp only [Pointer.add_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.reduceMul] at hfirst hlast
  have hr := finishPointState_read s point yptr hp
  rw [hy, finishPointBits_coordinates _ x y t (hfirst.symm.trans hx) (hlast.symm.trans ht)] at hr
  exact hr

/-- Instruction slice 50--55 of bb1, with the original imported instructions. -/
theorem finishPoint_segment (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (point y : Pointer)
    (hpoint : E.read (%36) = .value point) (hy : E.read (%38) = .value y)
    (h40 : E.read (%19) = .value 40#64) (h80 : E.read (%27) = .value 80#64)
    (h88 : E.read (%28) = .value 88#64) (hone : E.read (%6) = .value 1#64)
    (hzero : E.read (%20) = .value 0#8) (h32 : E.read (%10) = .value 32#64)
    (hp : SmallRange s.mem point 160) (hyLive : SmallRange s.mem y 40)
    (hd : (Range.of (point.add 40#64) 320).Disjoint (Range.of y 320)) :
    Cutpoint.segment (program p g) 1 50 6 E s =
      .value (E[%137 := .value (point.add 40#64), %138 := .value (point.add 80#64),
        %139 := .value (point.add 88#64)], finishPointState s point y) := by
  change List.foldlM Instr.run E (((program.bb1 p).body.drop 50).take 6) s = _
  have hg40 := hp.gep (k := 40) (by decide)
  have hg80 := (hp.storeAt (point.add 40#64) (s.mem.readAt y 320)).gep (k := 80) (by decide)
  have hg88 := ((hp.storeAt (point.add 40#64) (s.mem.readAt y 320)).storeAt
    (point.add 80#64) (1#64)).gep (k := 88) (by decide)
  norm_num only [Nat.cast_ofNat] at hg40 hg80 hg88
  have hf40 := hp.fits_add (k := 40) (count := 40) (by decide)
  have hf80 := (hp.fits_add (k := 80) (count := 8) (by decide)).storeAt
    (q := point.add 40#64) (x := s.mem.readAt y 320)
  have hf88 := ((hp.fits_add (k := 88) (count := 32) (by decide)).storeAt
    (q := point.add 40#64) (x := s.mem.readAt y 320)).storeAt
    (q := point.add 80#64) (x := 1#64)
  simp (disch := decide) [program.bb1, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Operation.memcpy, Operation.memset, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, mlir_effect,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    hg40, hg80, hg88, hpoint, hy, h40, h80, h88, hone, hzero, h32,
    hf40, hf80, hf88, hyLive.fits, hd, throwUBIf, finishPointState]

/-- Composition retains the original bb1 suffix and common tag-store block. -/
theorem finishPoint_run (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (out point y : Pointer)
    (hout : E.read (%arg0) = .value out)
    (hpoint : E.read (%36) = .value point) (hy : E.read (%38) = .value y)
    (h40 : E.read (%19) = .value 40#64) (h80 : E.read (%27) = .value 80#64)
    (h88 : E.read (%28) = .value 88#64) (hone : E.read (%6) = .value 1#64)
    (hzero : E.read (%20) = .value 0#8) (h32 : E.read (%10) = .value 32#64)
    (h8 : E.read (%8) = .value 8#64) (h160 : E.read (%29) = .value 160#64)
    (hp : SmallRange s.mem point 160) (hyLive : SmallRange s.mem y 40)
    (ho : SmallRange s.mem out 168)
    (hdY : (Range.of (point.add 40#64) 320).Disjoint (Range.of y 320))
    (hdOut : (Range.of (out.add 8#64) 1280).Disjoint (Range.of point 1280)) :
    resume p g 1 50 E s = .value (.nil,
      successState (finishPointState s point y) out
        (finishPointBits (s.mem.readAt point 1280) (s.mem.readAt y 320))) := by
  have hsegment := finishPoint_segment p g E s point y hpoint hy h40 h80 h88
    hone hzero h32 hp hyLive hdY
  unfold resume
  rw [Cutpoint.after_segment (program p g) 1 50 6 E _ s _ hsegment]
  change resume p g 1 56 _ _ = _
  rw [success_copy_run p g _ _ out point
    (by simpa (disch := decide) only [mlir_env] using hout)
    (by simpa (disch := decide) only [mlir_env] using hpoint)
    (by simpa (disch := decide) only [mlir_env] using h8)
    (by simpa (disch := decide) only [mlir_env] using h160)
    (by simpa (disch := decide) only [mlir_env] using hone)
    (finishPointState_live ho point y) (finishPointState_live hp point y) hdOut]
  rw [(finishPointState_read s point y hp).2]

end Agave.Ed25519.Encoding.Decompress.Execution.Decode
