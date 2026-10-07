import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixSignCompose

/-! The actual point-X copy and linked XY multiplication, bb1:47--49. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] machine

structure PointRegisters (E : Env program.Γ) (point x y : Pointer) : Prop where
  p36 : E.read (%36) = .value point
  x39 : E.read (%39) = .value x
  y38 : E.read (%38) = .value y
  c19 : E.read (%19) = .value 40#64
  c26 : E.read (%26) = .value 120#64

def pointXState (s : GlobalState) (point x : Pointer) : GlobalState :=
  {s with mem := s.mem.storeAt point (s.mem.readAt x 320)}

def pointTState (s : GlobalState) (point x y : Pointer) : GlobalState :=
  let t := pointXState s point x
  {t with mem := storeLimbs t.mem (point.add 120#64) (machine (readLimbs t x) (readLimbs t y))}

def pointEnv (E : Env program.Γ) (point : Pointer) : Env program.Γ :=
  E[%136 := .value (point.add 120#64)]

theorem point_copy_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (point x y : Pointer) (hp : SmallRange s.mem point 160)
    (hx : SmallRange s.mem x 40) (hd : point.id ≠ x.id) (he : PointRegisters E point x y) :
    Cutpoint.segment (program p g) 1 47 2 E s =
      .value (pointEnv E point, pointXState s point x) := by
  obtain ⟨e36,e39,e38,e19,e26⟩ := he
  have hfp : Fits s.mem point 320 := Fits.mono (by decide) hp.fits
  have hfx := hx.fits
  have hdis : (Range.of point 320).Disjoint (Range.of x 320) := Or.inl hd
  have hg := (hp.storeAt point (s.mem.readAt x 320)).gep (k := 120) (by decide)
  norm_num only [Nat.cast_ofNat] at hg
  change List.foldlM Instr.run E (((program.bb1 p).body.drop 47).take 2) s = _
  dsimp only [program.bb1,List.drop,List.take]
  simp (disch := first | assumption | decide)
    [List.foldlM_cons,List.foldlM_nil,Instr.run,Operation.memcpy,
    Operation.gepInboundsIndex,GepIndex.inboundsOffset,Operation.GepSignedRange,
    EffectM.bind_eq,EffectM.pure_eq,PoisonOr.value_bind,mlir_env,mlir_effect,
    e36,e39,e19,e26,hfp,hfx,hdis,hg,throwUBIf,pointEnv,pointXState]

theorem point_mul_segment (g : Globals) (sg : SqrtRatio.Globals) (E : Env program.Γ)
    (s : GlobalState) (point x y : Pointer) (hwf : s.WF)
    (hp : SmallRange s.mem point 160) (hx : SmallRange s.mem x 40)
    (hy : SmallRange s.mem y 40) (he : PointRegisters E point x y) :
    Cutpoint.segment (program (decodePrimitives sg) g) 1 49 1 (pointEnv E point)
      (pointXState s point x) = .value (pointEnv E point, pointTState s point x y) := by
  have hc := kernel_call (point.add 120#64) x y (pointXState s point x)
    hwf.storeAt (smallRange_add (hp.storeAt _ _) (k := 120) (count := 40) (by decide))
    (hx.storeAt _ _) (hy.storeAt _ _)
  simp only [kernel.args] at hc
  have e136 : (pointEnv E point).read (%136) = .value (point.add 120#64) := rfl
  have e39 : (pointEnv E point).read (%39) = .value x := by
    simpa (disch := decide) only [pointEnv,mlir_env] using he.x39
  have e38 : (pointEnv E point).read (%38) = .value y := by
    simpa (disch := decide) only [pointEnv,mlir_env] using he.y38
  change List.foldlM Instr.run (pointEnv E point)
    [.call (decodePrimitives sg).mul (.cons (%136) (.cons (%39) (.cons (%38) .nil))) .nil]
      (pointXState s point x) = _
  simp only [List.foldlM_cons,List.foldlM_nil,Instr.run,Regs.read_cons,Regs.read_nil,
    e136,e39,e38,decodePrimitives,EffectM.bind_eq,EffectM.pure_eq,hc,PoisonOr.value_bind,
    Env.writeMany_nil,pointTState]

theorem point_segment (g : Globals) (sg : SqrtRatio.Globals) (E : Env program.Γ)
    (s : GlobalState) (point x y : Pointer) (hwf : s.WF)
    (hp : SmallRange s.mem point 160) (hx : SmallRange s.mem x 40)
    (hy : SmallRange s.mem y 40) (hd : point.id ≠ x.id) (he : PointRegisters E point x y) :
    Cutpoint.segment (program (decodePrimitives sg) g) 1 47 3 E s =
      .value (pointEnv E point, pointTState s point x y) := by
  rw [show 3 = 2 + 1 from rfl,segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,
    point_copy_segment (decodePrimitives sg) g E s point x y hp hx hd he,PoisonOr.value_bind]
  exact point_mul_segment g sg E s point x y hwf hp hx hy he

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
