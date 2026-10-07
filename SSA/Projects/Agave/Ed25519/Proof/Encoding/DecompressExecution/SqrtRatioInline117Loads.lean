import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline117Maps
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline117Circuit
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline308Data

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117
open LeanMLIR.RIR SerialFieldMul SerializerRename
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

structure LoadRegisters (E : Env program.Γ) (a : Pointer) : Prop where
  a75 : E.read (%75) = .value a
  c3 : E.read (%3) = .value 8#64
  c4 : E.read (%4) = .value 16#64
  c5 : E.read (%5) = .value 24#64
  c6 : E.read (%6) = .value 32#64

def loadEnv (E : Env program.Γ) (a : Pointer) (x : Words) : Env program.Γ :=
  E[%84 := .value (x 0), %85 := .value (a.add 8#64),
    %86 := .value (x 1), %87 := .value (a.add 16#64),
    %88 := .value (x 2), %89 := .value (a.add 24#64),
    %90 := .value (x 3), %91 := .value (a.add 32#64), %92 := .value (x 4)]

theorem load_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (a : Pointer) (ha : SmallRange s.mem a 40)
    (he : LoadRegisters E a) :
    Cutpoint.segment (program p g) 0 117 13 E s =
      .value (loadEnv E a (readLimbs s a), s) := by
  obtain ⟨e75,e3,e4,e5,e6⟩ := he
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
  change List.foldlM Instr.run E (((program.entry p g).body.drop 117).take 13) s = _
  dsimp only [program.entry,List.drop,List.take]
  simp (disch := first | assumption | decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,Operation.load,
    Operation.gepInboundsIndex,GepIndex.inboundsOffset,Operation.GepSignedRange,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_env,mlir_effect,
    e75,e3,e4,e5,e6,h0,h8,h16,h24,h32,g8,g16,g24,g32,
    throwUBIf,loadEnv,readLimbs]

theorem load_constants (E : Env program.Γ) (a : Pointer) (x : Words)
    (hc : Inline308.Constants E) :
    prepared (rename.project (loadEnv E a x)) x = rename.project (loadEnv E a x) := by
  unfold prepared
  refine Env.write_eq_of ?_ (by rfl)
  refine Env.write_eq_of ?_ (by rfl)
  refine Env.write_eq_of ?_ (by rfl)
  refine Env.write_eq_of ?_ (by rfl)
  refine Env.write_eq_of ?_ (by rfl)
  refine Env.write_eq_of ?_ (by change E.read (%46) = _; exact hc.c46)
  refine Env.write_eq_of ?_ (by change E.read (%45) = _; exact hc.c45)
  refine Env.write_eq_of ?_ (by change E.read (%44) = _; exact hc.c44)
  refine Env.write_eq_of ?_ (by change E.read (%43) = _; exact hc.c43)
  refine Env.write_eq_of ?_ (by change E.read (%42) = _; exact hc.c42)
  refine Env.write_eq_of ?_ (by change E.read (%41) = _; exact hc.c41)
  refine Env.write_eq_of ?_ (by change E.read (%40) = _; exact hc.c40)
  refine Env.write_eq_of ?_ (by change E.read (%39) = _; exact hc.c39)
  refine Env.write_eq_of ?_ (by change E.read (%38) = _; exact hc.c38)
  refine Env.write_eq_of ?_ (by change E.read (%37) = _; exact hc.c37)
  refine Env.write_eq_of ?_ (by change E.read (%36) = _; exact hc.c36)
  refine Env.write_eq_of ?_ (by change E.read (%35) = _; exact hc.c35)
  refine Env.write_eq_of ?_ (by change E.read (%34) = _; exact hc.c34)
  refine Env.write_eq_of ?_ (by change E.read (%33) = _; exact hc.c33)
  refine Env.write_eq_of ?_ (by change E.read (%32) = _; exact hc.c32)
  refine Env.write_eq_of ?_ (by change E.read (%31) = _; exact hc.c31)
  refine Env.write_eq_of ?_ (by change E.read (%30) = _; exact hc.c30)
  refine Env.write_eq_of ?_ (by change E.read (%29) = _; exact hc.c29)
  refine Env.write_eq_of ?_ (by change E.read (%28) = _; exact hc.c28)
  refine Env.write_eq_of ?_ (by change E.read (%27) = _; exact hc.c27)
  refine Env.write_eq_of ?_ (by change E.read (%26) = _; exact hc.c26)
  refine Env.write_eq_of ?_ (by change E.read (%25) = _; exact hc.c25)
  refine Env.write_eq_of ?_ (by change E.read (%24) = _; exact hc.c24)
  refine Env.write_eq_of ?_ (by change E.read (%23) = _; exact hc.c23)
  refine Env.write_eq_of ?_ (by change E.read (%22) = _; exact hc.c22)
  refine Env.write_eq_of ?_ (by change E.read (%21) = _; exact hc.c21)
  refine Env.write_eq_of ?_ (by change E.read (%20) = _; exact hc.c20)
  refine Env.write_eq_of ?_ (by change E.read (%19) = _; exact hc.c19)
  refine Env.write_eq_of ?_ (by change E.read (%18) = _; exact hc.c18)
  refine Env.write_eq_of ?_ (by change E.read (%17) = _; exact hc.c17)
  refine Env.write_eq_of ?_ (by change E.read (%16) = _; exact hc.c16)
  refine Env.write_eq_of ?_ (by change E.read (%15) = _; exact hc.c15)
  refine Env.write_eq_of ?_ (by change E.read (%14) = _; exact hc.c14)
  refine Env.write_eq_of ?_ (by change E.read (%1) = _; exact hc.c1)
  refine Env.write_eq_of ?_ (by change E.read (%13) = _; exact hc.c13)
  refine Env.write_eq_of ?_ (by change E.read (%12) = _; exact hc.c12)
  refine Env.write_eq_of ?_ (by change E.read (%11) = _; exact hc.c11)
  refine Env.write_eq_of ?_ (by change E.read (%10) = _; exact hc.c10)
  refine Env.write_eq_of ?_ (by change E.read (%9) = _; exact hc.c9)
  refine Env.write_eq_of ?_ (by change E.read (%8) = _; exact hc.c8)
  refine Env.write_eq_of ?_ (by change E.read (%7) = _; exact hc.c7)
  refine Env.write_eq_of ?_ (by change E.read (%6) = _; exact hc.c6)
  refine Env.write_eq_of ?_ (by change E.read (%5) = _; exact hc.c5)
  refine Env.write_eq_of ?_ (by change E.read (%4) = _; exact hc.c4)
  refine Env.write_eq_of ?_ (by change E.read (%3) = _; exact hc.c3)
  rfl

theorem load_project_args (E : Env program.Γ) (a r : Pointer) (x : Words)
    (ha : E.read (%75) = .value a) (hr : E.read (%67) = .value r) :
    (rename.project (loadEnv E a x)).args = (ToBytes.program.args (.value r) (.value a)).get := by
  funext i
  fin_cases i
  · change E.read (%67) = .value r
    exact hr
  · change E.read (%75) = .value a
    exact ha

theorem exact_tail (p : Primitives) (g : Globals) :
    (((program.entry p g).body.drop 130).take 175) =
      (ToBytes.program.entry.body.drop 54).map rename.instr := by
  rfl

theorem source_supported : ∀ i ∈ (ToBytes.program.entry.body.drop 54), Renaming.supported i := by
  simp (maxSteps := 1000000) [ToBytes.program.entry, List.drop, Renaming.supported,
    Agave.Ed25519.SmallOrder.Execution.Transport.Supported]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline117
