import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioHelperSegments

/-! The actual helper calls plus their intervening lifetime/store/OR instructions.
The intervals are half-open: [306,308), [569,577), and [947,956). -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
open SerialPoint.Execution (smallRange_storeLimbs wf_storeLimbs)
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
attribute [local irreducible] SerialFieldMul.machine ToBytes.machine
attribute [local implicit_reducible] Ty.width

def negativeState (s : GlobalState) (p : Pointer) (x : Words) : GlobalState :=
  {s with mem := (s.mem.storeAt p (x 0)).storeAt (p.add 8) (BitVec.packLanes #v[x 1, x 2, x 3, x 4])}

theorem negativeState_live (h : SmallRange s.mem q n) (p : Pointer) (x : Words) :
    SmallRange (negativeState s p x).mem q n := (h.storeAt _ _).storeAt _ _

theorem negativeState_wf (hwf : s.WF) (p : Pointer) (x : Words) :
    (negativeState s p x).WF := by
  simpa only [negativeState, GlobalState.WF_storeAt] using hwf

theorem stores_570_576 (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (p : Pointer) (x : Words) (hp : SmallRange s.mem p 40)
    (h72 : E.read (%72) = .value p) (h300 : E.read (%300) = .value (p.add 8))
    (h312 : E.read (%312) = .value (x 0))
    (h313 : E.read (%313) = Ty.wrap #v[x 1, x 2, x 3, x 4]) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 570 6 E s =
      .value (E, negativeState s p x) := by
  have hf0 : Fits s.mem p 64 := Fits.mono (by decide) hp.fits
  have hf8 : Fits s.mem (p.add 8) 256 :=
    hp.fits_add (k := 8) (count := 32) (by decide)
  have hf8lit : Fits s.mem (p.add 8#64) 256 := hf8
  change List.foldlM Instr.run E (((program.entry sqrtRatioPrimitives g).body.drop 570).take 6) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    h72, h300, h312, h313, Ty.flatten_wrap_vec, Ty.flatten_bv,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_effect,
    hf0, throwUBIf, negativeState]
  rw [ite_eq_left hf8lit]
  rfl

theorem lifetimes_948_953 (g : Globals) (E : ⟪program.Γ⟫) (s : GlobalState) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 948 5 E s = .value (E, s) := by
  change List.foldlM Instr.run E (((program.entry sqrtRatioPrimitives g).body.drop 948).take 5) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, EffectM.bind_eq,
    EffectM.pure_eq, PoisonOr.value_bind]

theorem or_954 (g : Globals) (E : ⟪program.Γ⟫) (s : GlobalState) (a b : BitVec 8)
    (ha : E.read (%731) = .value a) (hb : E.read (%430) = .value b) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 954 1 E s =
      .value (E[%732 := .value (a ||| b)], s) := by
  change List.foldlM Instr.run E (((program.entry sqrtRatioPrimitives g).body.drop 954).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, Operation.or,
    ha, hb, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  rfl

theorem segment_306_308 (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (out input check : Pointer) (hwf : s.WF)
    (ho : SmallRange s.mem out 32) (hi : SmallRange s.mem input 40)
    (hc : SmallRange s.mem check 32)
    (h66 : E.read (%66) = .value out) (harg1 : E.read (%arg1) = .value input)
    (h67 : E.read (%67) = .value check) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 306 2 E s =
      .value (E[%236 := .value (comparison (serialize s out input) check out)],
        advance (serialize s out input) 33) := by
  rw [segment_append (n := 1) (m := 1)]
  simp only [Nat.reduceAdd, EffectM.bind_eq, toBytes_306 g E s out input hwf ho hi h66 harg1,
    PoisonOr.value_bind]
  exact bytesEq_307 g E (serialize s out input) check out
    (ToBytes.wf_storeBytes hwf _ _) (ToBytes.smallRange_storeBytes hc _ _)
    (ToBytes.smallRange_storeBytes ho _ _) h67 h66

theorem segment_569_577 (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (left right neg product sqrtM1 : Pointer) (x : Words)
    (hwf : s.WF) (hl : SmallRange s.mem left 32) (hr : SmallRange s.mem right 32)
    (hn : SmallRange s.mem neg 40) (hp : SmallRange s.mem product 40)
    (hs : SmallRange s.mem sqrtM1 40)
    (h65 : E.read (%65) = .value left) (h64 : E.read (%64) = .value right)
    (h72 : E.read (%72) = .value neg) (h300 : E.read (%300) = .value (neg.add 8))
    (h312 : E.read (%312) = .value (x 0))
    (h313 : E.read (%313) = Ty.wrap #v[x 1, x 2, x 3, x 4])
    (h73 : E.read (%73) = .value product) (h52 : E.read (%52) = .value sqrtM1) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 569 8 E s =
      .value (E[%430 := .value (comparison s left right)],
        multiply (negativeState (advance s 33) neg x) product neg sqrtM1) := by
  rw [segment_append (n := 1) (m := 7)]
  simp only [Nat.reduceAdd, EffectM.bind_eq, bytesEq_569 g E s left right hwf hl hr h65 h64,
    PoisonOr.value_bind]
  rw [segment_append (n := 6) (m := 1)]
  have hs0 := stores_570_576 g (E[%430 := .value (comparison s left right)])
    (advance s 33) neg x hn
    (by simpa (disch := decide) only [mlir_env] using h72)
    (by simpa (disch := decide) only [mlir_env] using h300)
    (by simpa (disch := decide) only [mlir_env] using h312)
    (by simpa (disch := decide) only [mlir_env] using h313)
  simp only [Nat.reduceAdd, EffectM.bind_eq, hs0, PoisonOr.value_bind]
  exact mul_576 g _ _ product neg sqrtM1
    (negativeState_wf (advance_wf s 33 hwf) neg x)
    (negativeState_live hp neg x) (negativeState_live hn neg x) (negativeState_live hs neg x)
    (by simpa (disch := decide) only [mlir_env] using h73)
    (by simpa (disch := decide) only [mlir_env] using h72)
    (by simpa (disch := decide) only [mlir_env] using h52)

def correctionEnv (E : ⟪program.Γ⟫) (eq previous : BitVec 8) : ⟪program.Γ⟫ :=
  E[%731 := .value eq, %732 := .value (eq ||| previous), %733 := .value (eq ||| previous)]

theorem segment_947_956 (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (left right replacement sqrtM1 root : Pointer) (previous : BitVec 8)
    (hwf : s.WF) (hl : SmallRange s.mem left 32) (hr : SmallRange s.mem right 32)
    (hp : SmallRange s.mem replacement 40) (hs : SmallRange s.mem sqrtM1 40)
    (hx : SmallRange s.mem root 40)
    (h63 : E.read (%63) = .value left) (h62 : E.read (%62) = .value right)
    (h71 : E.read (%71) = .value replacement) (h52 : E.read (%52) = .value sqrtM1)
    (h79 : E.read (%79) = .value root) (h430 : E.read (%430) = .value previous) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 947 9 E s =
      .value (correctionEnv E (comparison s left right) previous,
        advance (multiply (advance s 33) replacement sqrtM1 root) 1) := by
  rw [segment_append (n := 1) (m := 8)]
  simp only [Nat.reduceAdd, EffectM.bind_eq, bytesEq_947 g E s left right hwf hl hr h63 h62,
    PoisonOr.value_bind]
  rw [segment_append (n := 5) (m := 3)]
  simp only [Nat.reduceAdd, EffectM.bind_eq, lifetimes_948_953, PoisonOr.value_bind]
  rw [segment_append (n := 1) (m := 2)]
  have hm := mul_953 g (E[%731 := .value (comparison s left right)]) (advance s 33)
    replacement sqrtM1 root (advance_wf s 33 hwf) hp hs hx
    (by simpa (disch := decide) only [mlir_env] using h71)
    (by simpa (disch := decide) only [mlir_env] using h52)
    (by simpa (disch := decide) only [mlir_env] using h79)
  simp only [Nat.reduceAdd, EffectM.bind_eq, hm, PoisonOr.value_bind]
  rw [segment_append (n := 1) (m := 1)]
  have ho := or_954 g (E[%731 := .value (comparison s left right)])
    (multiply (advance s 33) replacement sqrtM1 root) (comparison s left right) previous
    (by simp only [mlir_env]) (by simpa (disch := decide) only [mlir_env] using h430)
  simp only [Nat.reduceAdd, EffectM.bind_eq, ho, PoisonOr.value_bind]
  exact blackBox_955 g _ _ (comparison s left right ||| previous)
    (wf_storeLimbs (advance_wf s 33 hwf) _ _) (by simp only [mlir_env])

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Helpers
