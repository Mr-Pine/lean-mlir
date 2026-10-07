import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Pieces
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! Exact instructions 0–80: allocations, Z inversion calls, and affine X/Y
multiplication calls. Each call premise describes one lower primitive invocation;
no compressor or affine-conversion correctness is assumed. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def scratchBytes : Nat → Nat
  | 1 | 5 => 80
  | _ => 40

def scratchState (s : GlobalState) : Nat → GlobalState
  | 0 => s
  | n + 1 => (scratchState s n).alloca (scratchBytes n)

def scratch (s : GlobalState) (n : Nat) : Pointer := (scratchState s n).allocaPtr

def constantEnv (E : Env program.Γ) : Env program.Γ :=
  E[%0 := .value 1#32,
    %1 := .value 80#64,
    %2 := .value 40#64,
    %3 := .value 5#32,
    %4 := .value 48#64,
    %5 := .value 56#64,
    %6 := .value 64#64,
    %7 := .value 72#64,
    %8 := .value 51#64,
    %9 := .value 2251799813685247#64,
    %10 := .value 19#64,
    %11 := .value 8#64,
    %12 := .value 16#64,
    %13 := .value 24#64,
    %14 := .value 32#64,
    %15 := .value 7#64,
    %16 := .value 3#64,
    %17 := .value 5#64,
    %18 := .value 13#64,
    %19 := .value 21#64,
    %20 := .value 29#64,
    %21 := .value 37#64,
    %22 := .value 45#64,
    %23 := .value 6#64,
    %24 := .value 2#64,
    %25 := .value 10#64,
    %26 := .value 18#64,
    %27 := .value 26#64,
    %28 := .value 34#64,
    %29 := .value 42#64,
    %30 := .value 50#64,
    %31 := .value 1#64,
    %32 := .value 15#64,
    %33 := .value 23#64,
    %34 := .value 31#64,
    %35 := .value 39#64,
    %36 := .value 47#64,
    %37 := .value 4#64,
    %38 := .value 12#64,
    %39 := .value 20#64,
    %40 := .value 28#64,
    %41 := .value 36#64,
    %42 := .value 44#64,
    %43 := .value 1#8,
    %44 := .value 7#8,
    %45 := .value 9#64,
    %46 := .value 11#64,
    %47 := .value 14#64,
    %48 := .value 17#64,
    %49 := .value 22#64,
    %50 := .value 25#64,
    %51 := .value 27#64,
    %52 := .value 30#64]

def allocatedEnv (E : Env program.Γ) (s : GlobalState) : Env program.Γ :=
  (constantEnv E)[%53 := .value (scratch s 0), %54 := .value (scratch s 1),
    %55 := .value (scratch s 2), %56 := .value (scratch s 3),
    %57 := .value (scratch s 4), %58 := .value (scratch s 5)]

def affineEnv (E : Env program.Γ) (s : GlobalState) (input : Pointer) : Env program.Γ :=
  (allocatedEnv E s)[%59 := .value (input.add 80),
    %60 := .value ((scratch s 1).add 40), %61 := .value (input.add 40),
    %62 := .value ((scratch s 5).add 40)]

def copyFirst (initial powed : GlobalState) : GlobalState :=
  {powed with
    mem := powed.mem.storeAt (scratch initial 3)
      (powed.mem.readAt (scratch initial 1) 320)}

def copySecond (initial powed : GlobalState) : GlobalState :=
  let copied := copyFirst initial powed
  {copied with
    mem := copied.mem.storeAt (scratch initial 2)
      (copied.mem.readAt ((scratch initial 1).add 40) 320)}

private theorem modifyGet_run (f : GlobalState → α × GlobalState) (s : GlobalState) :
    (modifyGet f : EffectM α) s = .value (f s) := rfl

/-- The exact six allocations and five lower calls, including both memcpy
operations between pow22501 and pow2k. All live-range premises are local to the
instruction using them and will be supplied by lower primitive frames. -/
theorem affine_prefix_run (p : Primitives) (E : Env program.Γ) (input : Pointer)
    (initial powed squared inverted affineX affineXY : GlobalState)
    (hinput : E.read (%arg1) = .value input)
    (hinput0 : SmallRange (scratchState initial 6).mem input 160)
    (hpow : p.pow22501 (.cons (.value (scratch initial 1))
      (.cons (.value (input.add 80)) .nil)) (scratchState initial 6) = .value (.nil, powed))
    (hpair : SmallRange powed.mem (scratch initial 1) 80)
    (hfirst : SmallRange powed.mem (scratch initial 3) 40)
    (hsecond : SmallRange powed.mem (scratch initial 2) 40)
    (hdfirst : (Range.of (scratch initial 3) 320).Disjoint
      (Range.of (scratch initial 1) 320))
    (hdsecond : (Range.of (scratch initial 2) 320).Disjoint
      (Range.of ((scratch initial 1).add 40) 320))
    (hpow5 : p.pow2k (.cons (.value (scratch initial 0))
      (.cons (.value (scratch initial 3)) (.cons (.value 5#32) .nil)))
      (copySecond initial powed) = .value (.nil, squared))
    (hinvert : p.mul (.cons (.value (scratch initial 4))
      (.cons (.value (scratch initial 0)) (.cons (.value (scratch initial 2)) .nil)))
      squared = .value (.nil, inverted))
    (hx : p.mul (.cons (.value (scratch initial 5))
      (.cons (.value input) (.cons (.value (scratch initial 4)) .nil)))
      inverted = .value (.nil, affineX))
    (hinputX : SmallRange affineX.mem input 160)
    (htempX : SmallRange affineX.mem (scratch initial 5) 80)
    (hy : p.mul (.cons (.value ((scratch initial 5).add 40))
      (.cons (.value (input.add 40)) (.cons (.value (scratch initial 4)) .nil)))
      affineX = .value (.nil, affineXY)) :
    runSlice p 0 81 E initial = .value (affineEnv E initial input, affineXY) := by
  change E.args 1 = .value input at hinput
  have hgZ := hinput0.gep (k := 80) (by decide)
  have hgPair := (hpair.storeAt (scratch initial 3)
    (powed.mem.readAt (scratch initial 1) 320)).gep (k := 40) (by decide)
  have hgY := hinputX.gep (k := 40) (by decide)
  have hgOutY := htempX.gep (k := 40) (by decide)
  have hfPair0 := hpair.fits_add (k := 0) (count := 40) (by decide)
  have hfPair40 := (hpair.storeAt (scratch initial 3)
    (powed.mem.readAt (scratch initial 1) 320)).fits_add (k := 40) (count := 40) (by decide)
  have hfSecond := hsecond.fits.storeAt (q := scratch initial 3)
    (x := powed.mem.readAt (scratch initial 1) 320)
  have hfFirst := hfirst.fits
  simp only [Pointer.add_zero] at hfPair0
  norm_num only [Nat.cast_ofNat] at hgZ hgPair hgY hgOutY
  simp only [copySecond, copyFirst, scratch, scratchState, scratchBytes,
    BitVec.ofNat_eq_ofNat, Nat.reduceMul] at hpow hpow5 hinvert hx hy hgZ hgPair hgY hgOutY hfPair0 hfPair40 hfSecond hfFirst hdfirst hdsecond
  simp [runSlice, program.entry, affineEnv, allocatedEnv, constantEnv,
    List.foldlM_cons, List.foldlM_nil, Instr.run, run_alloca, modifyGet_run, Ty.wrap,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
    Operation.memcpy, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange, Env.writeMany_nil,
    hinput, hpow, hpow5, hinvert, hx, hy, hgZ, hgPair, hgY, hgOutY,
    hfPair0, hfPair40, hfFirst, hfSecond, hdfirst, hdsecond, throwUBIf,
    scratch, scratchState, scratchBytes]

end Agave.Ed25519.Encoding.Compress.Execution
