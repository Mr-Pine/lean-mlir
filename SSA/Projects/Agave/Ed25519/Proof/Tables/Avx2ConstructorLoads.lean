import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorStack
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorPacking

/-! Exact serial point loads from the caller's 160-byte range. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Loads
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open Avx2PointAdd.CFG (runSlice)
open DoubleBase.ExecutionAvx2 (RegisterFrame)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def point (m : MemoryState) (a : Pointer) : Packing.SerialPoint :=
  fun e k => m.readAt (a.add (BitVec.ofNat 64 (40*e.val + 8*k.val))) 64

def input (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  E[%1 := .value 8#64,
    %2 := .value 16#64,
    %3 := .value 24#64,
    %4 := .value 32#64,
    %5 := .value 40#64,
    %6 := .value 48#64,
    %7 := .value 56#64,
    %8 := .value 64#64,
    %9 := .value 72#64,
    %10 := .value 80#64,
    %11 := .value 88#64,
    %12 := .value 96#64,
    %13 := .value 104#64,
    %14 := .value 112#64,
    %15 := .value 120#64,
    %16 := .value 128#64,
    %17 := .value 136#64,
    %18 := .value 144#64,
    %19 := .value 152#64]

def result (E : ⟪kernel.Γ⟫) (m : MemoryState) (a : Pointer) : ⟪kernel.Γ⟫ :=
  E[%361 := .value (m.readAt a 64),
    %362 := .value (a.add 8#64),
    %363 := .value (m.readAt (a.add 8#64) 64),
    %364 := .value (a.add 16#64),
    %365 := .value (m.readAt (a.add 16#64) 64),
    %366 := .value (a.add 24#64),
    %367 := .value (m.readAt (a.add 24#64) 64),
    %368 := .value (a.add 32#64),
    %369 := .value (m.readAt (a.add 32#64) 64),
    %370 := .value (a.add 40#64),
    %371 := .value (m.readAt (a.add 40#64) 64),
    %372 := .value (a.add 48#64),
    %373 := .value (m.readAt (a.add 48#64) 64),
    %374 := .value (a.add 56#64),
    %375 := .value (m.readAt (a.add 56#64) 64),
    %376 := .value (a.add 64#64),
    %377 := .value (m.readAt (a.add 64#64) 64),
    %378 := .value (a.add 72#64),
    %379 := .value (m.readAt (a.add 72#64) 64),
    %380 := .value (a.add 80#64),
    %381 := .value (m.readAt (a.add 80#64) 64),
    %382 := .value (a.add 88#64),
    %383 := .value (m.readAt (a.add 88#64) 64),
    %384 := .value (a.add 96#64),
    %385 := .value (m.readAt (a.add 96#64) 64),
    %386 := .value (a.add 104#64),
    %387 := .value (m.readAt (a.add 104#64) 64),
    %388 := .value (a.add 112#64),
    %389 := .value (m.readAt (a.add 112#64) 64),
    %390 := .value (a.add 120#64),
    %391 := .value (m.readAt (a.add 120#64) 64),
    %392 := .value (a.add 128#64),
    %393 := .value (m.readAt (a.add 128#64) 64),
    %394 := .value (a.add 136#64),
    %395 := .value (m.readAt (a.add 136#64) 64),
    %396 := .value (a.add 144#64),
    %397 := .value (m.readAt (a.add 144#64) 64),
    %398 := .value (a.add 152#64),
    %399 := .value (m.readAt (a.add 152#64) 64)]

theorem register_frame (E : ⟪kernel.Γ⟫) (m : MemoryState) (a : Pointer) :
    RegisterFrame 361 400 E (result E m a) := by
  unfold result
  iterate 39 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem run (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) (a : Pointer)
    (ha : Buffer s.mem a 160) (harg : E.read (%arg1) = .value a) :
    runSlice (kernel.bb0 p) (input E) 361 39 s =
      .value (result (input E) s.mem a, s) := by
  have harg' : E.args 1 = .value a := harg
  have hf0 : Fits s.mem a 64 := ha.fits.mono (by decide)
  have hg1 := ha.gep (offset := 8) (by decide)
  have hf1 := ha.fits_at 8 8 (by decide)
  have hg2 := ha.gep (offset := 16) (by decide)
  have hf2 := ha.fits_at 16 8 (by decide)
  have hg3 := ha.gep (offset := 24) (by decide)
  have hf3 := ha.fits_at 24 8 (by decide)
  have hg4 := ha.gep (offset := 32) (by decide)
  have hf4 := ha.fits_at 32 8 (by decide)
  have hg5 := ha.gep (offset := 40) (by decide)
  have hf5 := ha.fits_at 40 8 (by decide)
  have hg6 := ha.gep (offset := 48) (by decide)
  have hf6 := ha.fits_at 48 8 (by decide)
  have hg7 := ha.gep (offset := 56) (by decide)
  have hf7 := ha.fits_at 56 8 (by decide)
  have hg8 := ha.gep (offset := 64) (by decide)
  have hf8 := ha.fits_at 64 8 (by decide)
  have hg9 := ha.gep (offset := 72) (by decide)
  have hf9 := ha.fits_at 72 8 (by decide)
  have hg10 := ha.gep (offset := 80) (by decide)
  have hf10 := ha.fits_at 80 8 (by decide)
  have hg11 := ha.gep (offset := 88) (by decide)
  have hf11 := ha.fits_at 88 8 (by decide)
  have hg12 := ha.gep (offset := 96) (by decide)
  have hf12 := ha.fits_at 96 8 (by decide)
  have hg13 := ha.gep (offset := 104) (by decide)
  have hf13 := ha.fits_at 104 8 (by decide)
  have hg14 := ha.gep (offset := 112) (by decide)
  have hf14 := ha.fits_at 112 8 (by decide)
  have hg15 := ha.gep (offset := 120) (by decide)
  have hf15 := ha.fits_at 120 8 (by decide)
  have hg16 := ha.gep (offset := 128) (by decide)
  have hf16 := ha.fits_at 128 8 (by decide)
  have hg17 := ha.gep (offset := 136) (by decide)
  have hf17 := ha.fits_at 136 8 (by decide)
  have hg18 := ha.gep (offset := 144) (by decide)
  have hf18 := ha.fits_at 144 8 (by decide)
  have hg19 := ha.gep (offset := 152) (by decide)
  have hf19 := ha.fits_at 152 8 (by decide)
  norm_num only [Nat.cast_ofNat] at hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19
  simp [runSlice, kernel.bb0, input, result, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Operation.load, Ty.wrap, EffectM.bind_eq, EffectM.pure_eq,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    mlir_effect, mlir_env, throwUBIf, harg', hf0,hg1, hf1, hg2, hf2, hg3, hf3, hg4, hf4, hg5, hf5, hg6, hf6, hg7, hf7, hg8, hf8, hg9, hf9, hg10, hf10, hg11, hf11, hg12, hf12, hg13, hf13, hg14, hf14, hg15, hf15, hg16, hf16, hg17, hf17, hg18, hf18, hg19, hf19]

def reads (E : ⟪kernel.Γ⟫) : Fin 4 → Fin 5 → PoisonOr (BitVec 64) :=
  ![![E.read (%361), E.read (%363), E.read (%365), E.read (%367), E.read (%369)],
    ![E.read (%371), E.read (%373), E.read (%375), E.read (%377), E.read (%379)],
    ![E.read (%381), E.read (%383), E.read (%385), E.read (%387), E.read (%389)],
    ![E.read (%391), E.read (%393), E.read (%395), E.read (%397), E.read (%399)]]

theorem reads_result (E : ⟪kernel.Γ⟫) (m : MemoryState) (a : Pointer)
    (e : Fin 4) (k : Fin 5) :
    reads (result E m a) e k = .value (point m a e k) := by
  fin_cases e <;> fin_cases k <;> simp [reads, result, point, mlir_env]

end Agave.Ed25519.Tables.Avx2Constructor.Loads
