import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityPhases
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.Linked
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.PrivateFrame
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.FieldCall

/-! Execute the exact X-product phase, including live GEP checks and both
imported field-kernel calls. Arithmetic bounds are not required for raw word
execution; their field interpretation is supplied by `FieldProduct`. -/
namespace Agave.Ed25519.SmallOrder.Execution.EqualityPhases
open LeanMLIR.RIR Verifier.Execution.PointConstantTimeEq
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 16000

def productXState (s : GlobalState) (xl xr left right : Pointer) : GlobalState :=
  mulPost (mulPost s xl left (right.add 80#64)) xr right (left.add 80#64)

theorem productsX_exact (p : Primitives) : productsX p =
    [.lifetimeStart (%54) 40,
     .gepInbounds (%55) (%arg1) [.constant 80],
     .call p.fieldMul (.cons (%54) (.cons (%arg0) (.cons (%55) .nil))) .nil,
     .lifetimeStart (%53) 40,
     .gepInbounds (%56) (%arg0) [.constant 80],
     .call p.fieldMul (.cons (%53) (.cons (%arg1) (.cons (%56) .nil))) .nil] := rfl

/-- Both actual field calls execute from ordinary caller and scratch bounds;
no whole-point multiplication or field-operation contract is a premise. -/
theorem productsX_run (E : Env program.Γ) (s : GlobalState)
    (xl xr left right : Pointer) (hwf : s.WF)
    (hl : SmallRange s.mem left 160) (hr : SmallRange s.mem right 160)
    (hxl : SmallRange s.mem xl 40) (hxr : SmallRange s.mem xr 40)
    (el : E.read (%arg0) = .value left) (er : E.read (%arg1) = .value right)
    (exl : E.read (%54) = .value xl) (exr : E.read (%53) = .value xr)
    (e80 : E.read (%1) = .value 80#64) :
    List.foldlM Instr.run E (productsX equalityPrimitives) s =
      .value (E[%55 := .value (right.add 80#64), %56 := .value (left.add 80#64)],
        productXState s xl xr left right) := by
  change E.args 0 = .value left at el
  change E.args 1 = .value right at er
  let t := mulPost s xl left (right.add 80#64)
  have hl0 : SmallRange s.mem left 40 := by
    simpa only [Pointer.add_zero] using smallRange_add hl (k := 0) (count := 40) (by decide)
  have hr0 : SmallRange s.mem right 40 := by
    simpa only [Pointer.add_zero] using smallRange_add hr (k := 0) (count := 40) (by decide)
  have hr80 : SmallRange s.mem (right.add 80#64) 40 :=
    smallRange_add hr (k := 80) (count := 40) (by decide)
  have hl80 : SmallRange s.mem (left.add 80#64) 40 :=
    smallRange_add hl (k := 80) (count := 40) (by decide)
  have c1 := mulPost_call s xl left (right.add 80#64) hwf hxl hl0 hr80
  have c2 := mulPost_call t xr right (left.add 80#64) (mulPost_wf _ _ _ _ hwf)
    (mulPost_smallRange _ _ _ _ _ hxr) (mulPost_smallRange _ _ _ _ _ hr0)
    (mulPost_smallRange _ _ _ _ _ hl80)
  simp only [SerialFieldMul.kernel.args] at c1 c2
  have g1 := hr.gep (k := 80) (by decide)
  have g2 := (mulPost_smallRange s xl left (right.add 80#64) left hl).gep (k := 80) (by decide)
  norm_num only at g1 g2
  simp [productsX_exact, List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq, PoisonOr.value_bind,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    List.map_cons, List.map_nil, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    mlir_env, el, er, exl, exr, e80, g1, g2, equalityPrimitives,
    SerialFieldMul.kernel.args, c1, c2, t, productXState]

/-- The two field-kernel stores disappear under point equality's own cleanup. -/
theorem productsX_private (h : PrivateFrame before s) (xl xr left right : Pointer)
    (hxl : before.alloc.nextFreeBlock ≤ xl.id.id)
    (hxr : before.alloc.nextFreeBlock ≤ xr.id.id) :
    PrivateFrame before (productXState s xl xr left right) :=
  (h.storeLimbs xl _ hxl).storeLimbs xr _ hxr


def productYState (s : GlobalState) (yl yr left right : Pointer) : GlobalState :=
  mulPost (mulPost s yl (left.add 40#64) (right.add 80#64)) yr (right.add 40#64) (left.add 80#64)

theorem productsY_exact (p : Primitives) : productsY p =
    [.lifetimeStart (%52) 40,
     .gepInbounds (%362) (%arg0) [.constant 40],
     .call p.fieldMul (.cons (%52) (.cons (%362) (.cons (%55) .nil))) .nil,
     .lifetimeStart (%51) 40,
     .gepInbounds (%363) (%arg1) [.constant 40],
     .call p.fieldMul (.cons (%51) (.cons (%363) (.cons (%56) .nil))) .nil] := rfl

theorem productsY_run (E : Env program.Γ) (s : GlobalState)
    (yl yr left right : Pointer) (hwf : s.WF)
    (hl : SmallRange s.mem left 160) (hr : SmallRange s.mem right 160)
    (hyl : SmallRange s.mem yl 40) (hyr : SmallRange s.mem yr 40)
    (el : E.read (%arg0) = .value left) (er : E.read (%arg1) = .value right)
    (eyl : E.read (%52) = .value yl) (eyr : E.read (%51) = .value yr)
    (ezl : E.read (%56) = .value (left.add 80#64))
    (ezr : E.read (%55) = .value (right.add 80#64))
    (e40 : E.read (%13) = .value 40#64) :
    List.foldlM Instr.run E (productsY equalityPrimitives) s =
      .value (E[%362 := .value (left.add 40#64), %363 := .value (right.add 40#64)],
        productYState s yl yr left right) := by
  change E.args 0 = .value left at el
  change E.args 1 = .value right at er
  let t := mulPost s yl (left.add 40#64) (right.add 80#64)
  have hl40 : SmallRange s.mem (left.add 40#64) 40 :=
    smallRange_add hl (k := 40) (count := 40) (by decide)
  have hr40 : SmallRange s.mem (right.add 40#64) 40 :=
    smallRange_add hr (k := 40) (count := 40) (by decide)
  have hr80 : SmallRange s.mem (right.add 80#64) 40 :=
    smallRange_add hr (k := 80) (count := 40) (by decide)
  have hl80 : SmallRange s.mem (left.add 80#64) 40 :=
    smallRange_add hl (k := 80) (count := 40) (by decide)
  have c1 := mulPost_call s yl (left.add 40#64) (right.add 80#64) hwf hyl hl40 hr80
  have c2 := mulPost_call t yr (right.add 40#64) (left.add 80#64) (mulPost_wf _ _ _ _ hwf)
    (mulPost_smallRange _ _ _ _ _ hyr) (mulPost_smallRange _ _ _ _ _ hr40)
    (mulPost_smallRange _ _ _ _ _ hl80)
  simp only [SerialFieldMul.kernel.args] at c1 c2
  have g1 := hl.gep (k := 40) (by decide)
  have g2 := (mulPost_smallRange s yl (left.add 40#64) (right.add 80#64) right hr).gep
    (k := 40) (by decide)
  norm_num only at g1 g2
  simp [productsY_exact, List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, EffectM.get_eq, PoisonOr.value_bind,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    List.map_cons, List.map_nil, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    mlir_env, el, er, eyl, eyr, ezl, ezr, e40, g1, g2, equalityPrimitives,
    SerialFieldMul.kernel.args, c1, c2, t, productYState]

theorem productsY_private (h : PrivateFrame before s) (yl yr left right : Pointer)
    (hyl : before.alloc.nextFreeBlock ≤ yl.id.id)
    (hyr : before.alloc.nextFreeBlock ≤ yr.id.id) :
    PrivateFrame before (productYState s yl yr left right) :=
  (h.storeLimbs yl _ hyl).storeLimbs yr _ hyr

end Agave.Ed25519.SmallOrder.Execution.EqualityPhases
