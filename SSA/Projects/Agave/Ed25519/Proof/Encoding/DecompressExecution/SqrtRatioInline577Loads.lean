import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlinePrefixSquare
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtWords

/-! The two exact load prefixes of the third sqrt inline region. The first
serializer reuses addresses from the first comparison; the second computes
its four GEPs locally. Neither prefix writes memory. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

structure FirstLoadRegisters (E : Env program.Γ) (a : Pointer) : Prop where
  a75 : E.read (%75) = .value a
  a85 : E.read (%85) = .value (a.add 8#64)
  a87 : E.read (%87) = .value (a.add 16#64)
  a89 : E.read (%89) = .value (a.add 24#64)
  a91 : E.read (%91) = .value (a.add 32#64)

def firstLoadEnv (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%431 := .value (x 0), %432 := .value (x 1), %433 := .value (x 2),
    %434 := .value (x 3), %435 := .value (x 4)]

theorem first_load_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (a : Pointer) (ha : SmallRange s.mem a 40)
    (he : FirstLoadRegisters E a) :
    Cutpoint.segment (program p g) 0 577 8 E s =
      .value (firstLoadEnv E (readLimbs s a), s) := by
  obtain ⟨e75,e85,e87,e89,e91⟩ := he
  have h0 := ha.fits_add (k := 0) (count := 8) (by decide)
  have h8 := ha.fits_add (k := 8) (count := 8) (by decide)
  have h16 := ha.fits_add (k := 16) (count := 8) (by decide)
  have h24 := ha.fits_add (k := 24) (count := 8) (by decide)
  have h32 := ha.fits_add (k := 32) (count := 8) (by decide)
  simp only [Pointer.add_zero] at h0
  change List.foldlM Instr.run E (((program.entry p g).body.drop 577).take 8) s = _
  dsimp only [program.entry,List.drop,List.take]
  simp (disch := first | assumption | decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,Operation.load,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_env,mlir_effect,
    e75,e85,e87,e89,e91,h0,h8,h16,h24,h32,throwUBIf,firstLoadEnv,readLimbs]

structure SecondLoadRegisters (E : Env program.Γ) (a : Pointer) : Prop where
  a73 : E.read (%73) = .value a
  c3 : E.read (%3) = .value 8#64
  c4 : E.read (%4) = .value 16#64
  c5 : E.read (%5) = .value 24#64
  c6 : E.read (%6) = .value 32#64

def secondLoadEnv (E : Env program.Γ) (a : Pointer) (x : Words) : Env program.Γ :=
  E[%579 := .value (x 0), %580 := .value (a.add 8#64),
    %581 := .value (x 1), %582 := .value (a.add 16#64),
    %583 := .value (x 2), %584 := .value (a.add 24#64),
    %585 := .value (x 3), %586 := .value (a.add 32#64), %587 := .value (x 4)]

theorem second_load_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (a : Pointer) (ha : SmallRange s.mem a 40)
    (he : SecondLoadRegisters E a) :
    Cutpoint.segment (program p g) 0 760 12 E s =
      .value (secondLoadEnv E a (readLimbs s a), s) := by
  obtain ⟨e73,e3,e4,e5,e6⟩ := he
  have h0 := ha.fits_add (k := 0) (count := 8) (by decide)
  have h8 := ha.fits_add (k := 8) (count := 8) (by decide)
  have h16 := ha.fits_add (k := 16) (count := 8) (by decide)
  have h24 := ha.fits_add (k := 24) (count := 8) (by decide)
  have h32 := ha.fits_add (k := 32) (count := 8) (by decide)
  simp only [Pointer.add_zero] at h0
  have g8 := ha.gep (k := 8) (by decide)
  have g16 := ha.gep (k := 16) (by decide)
  have g24 := ha.gep (k := 24) (by decide)
  have g32 := ha.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at g8 g16 g24 g32
  change List.foldlM Instr.run E (((program.entry p g).body.drop 760).take 12) s = _
  dsimp only [program.entry,List.drop,List.take]
  simp (disch := first | assumption | decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,Operation.load,
    Operation.gepInboundsIndex,GepIndex.inboundsOffset,Operation.GepSignedRange,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_env,mlir_effect,
    e73,e3,e4,e5,e6,h0,h8,h16,h24,h32,g8,g16,g24,g32,
    throwUBIf,secondLoadEnv,readLimbs]

theorem first_load_args (E : Env program.Γ) (x : Words) :
    (firstLoadEnv E x).args = E.args := rfl

theorem second_load_args (E : Env program.Γ) (a : Pointer) (x : Words) :
    (secondLoadEnv E a x).args = E.args := rfl

theorem first_load_frame (E : Env program.Γ) (x : Words)
    (i : Fin program.Γ.n) (hi : i.val < 431) :
    (firstLoadEnv E x).vals i = E.vals i := by
  simp [firstLoadEnv,Env.write,Env.set,show i ≠ 431 by intro h; have hh := congrArg Fin.val h; change i.val = 431 at hh; omega,
    show i ≠ 432 by intro h; have hh := congrArg Fin.val h; change i.val = 432 at hh; omega,
    show i ≠ 433 by intro h; have hh := congrArg Fin.val h; change i.val = 433 at hh; omega,
    show i ≠ 434 by intro h; have hh := congrArg Fin.val h; change i.val = 434 at hh; omega,
    show i ≠ 435 by intro h; have hh := congrArg Fin.val h; change i.val = 435 at hh; omega]

theorem second_load_frame (E : Env program.Γ) (a : Pointer) (x : Words)
    (i : Fin program.Γ.n) (hi : i.val < 579) :
    (secondLoadEnv E a x).vals i = E.vals i := by
  simp [secondLoadEnv,Env.write,Env.set,show i ≠ 579 by intro h; have hh := congrArg Fin.val h; change i.val = 579 at hh; omega,
    show i ≠ 580 by intro h; have hh := congrArg Fin.val h; change i.val = 580 at hh; omega,
    show i ≠ 581 by intro h; have hh := congrArg Fin.val h; change i.val = 581 at hh; omega,
    show i ≠ 582 by intro h; have hh := congrArg Fin.val h; change i.val = 582 at hh; omega,
    show i ≠ 583 by intro h; have hh := congrArg Fin.val h; change i.val = 583 at hh; omega,
    show i ≠ 584 by intro h; have hh := congrArg Fin.val h; change i.val = 584 at hh; omega,
    show i ≠ 585 by intro h; have hh := congrArg Fin.val h; change i.val = 585 at hh; omega,
    show i ≠ 586 by intro h; have hh := congrArg Fin.val h; change i.val = 586 at hh; omega,
    show i ≠ 587 by intro h; have hh := congrArg Fin.val h; change i.val = 587 at hh; omega]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577
