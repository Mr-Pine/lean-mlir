import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorAddDefs

/-! Exact positive-add intervals of the unchanged AVX2 table constructor. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Add
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases
open Avx2PointAdd.CFG (runSlice runBodyFrom_slice prepareConstants differenceConstants abdcVec)
open DoubleBase.ExecutionAvx2 (RegisterFrame)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
attribute [local implicit_reducible] Ty.width

def prepareEnv (E : ⟪kernel.Γ⟫) (a : PointBlocks) : ⟪kernel.Γ⟫ :=
  let v806 : ⟦Ty.vec 8 32⟧ := Ty.wrap (a 0)
  let v807 : ⟦Ty.vec 8 32⟧ := Ty.wrap (a 1)
  let v808 : ⟦Ty.vec 8 32⟧ := Ty.wrap (a 2)
  let v809 : ⟦Ty.vec 8 32⟧ := Ty.wrap (a 3)
  let v810 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] v806 (E.read (%31))
  let v811 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] v807 (E.read (%31))
  let v812 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] v808 (E.read (%31))
  let v813 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] v809 (E.read (%31))
  let v814 : ⟦Ty.vec 8 32⟧ := Ty.wrap (a 4)
  let v815 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] v814 (E.read (%31))
  let v816 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%52)) v806
  let v817 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%70)) v807
  let v818 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%70)) v808
  let v819 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%70)) v809
  let v820 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%70)) v814
  let v821 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v816 v806
  let v822 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v817 v807
  let v823 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v818 v808
  let v824 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v819 v809
  let v825 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v820 v814
  let v826 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v821 v810
  let v827 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v822 v811
  let v828 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v823 v812
  let v829 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v824 v813
  let v830 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v825 v815
  let v831 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v826 v806
  let v832 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v827 v807
  let v833 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v828 v808
  let v834 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v829 v809
  let v835 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v830 v814
  E[%806 := v806,
    %807 := v807,
    %808 := v808,
    %809 := v809,
    %810 := v810,
    %811 := v811,
    %812 := v812,
    %813 := v813,
    %814 := v814,
    %815 := v815,
    %816 := v816,
    %817 := v817,
    %818 := v818,
    %819 := v819,
    %820 := v820,
    %821 := v821,
    %822 := v822,
    %823 := v823,
    %824 := v824,
    %825 := v825,
    %826 := v826,
    %827 := v827,
    %828 := v828,
    %829 := v829,
    %830 := v830,
    %831 := v831,
    %832 := v832,
    %833 := v833,
    %834 := v834,
    %835 := v835]

theorem prepare_frame (E : ⟪kernel.Γ⟫) (a : PointBlocks) :
    RegisterFrame 806 836 E (prepareEnv E a) := by
  unfold prepareEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

def prepareOutputs (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%831), E.read (%832), E.read (%833), E.read (%834), E.read (%835)]

theorem prepare_slice (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (a : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = a)
    (hp0 : E.read (%355) = .value r)
    (hp1 : E.read (%787) = .value (r.add 32#64))
    (hp2 : E.read (%788) = .value (r.add 64#64))
    (hp3 : E.read (%789) = .value (r.add 96#64))
    (hp4 : E.read (%790) = .value (r.add 128#64)) :
    runSlice (kernel.bb2 p) E 5 30 s = .value (prepareEnv E a, s) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hv0 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 0#64) 256) =
      Ty.wrap (a 0) := packed_unflatten s.mem r a hv 0
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv0
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hv1 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 32#64) 256) =
      Ty.wrap (a 1) := packed_unflatten s.mem r a hv 1
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv1
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hv2 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 64#64) 256) =
      Ty.wrap (a 2) := packed_unflatten s.mem r a hv 2
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv2
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hv3 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 96#64) 256) =
      Ty.wrap (a 3) := packed_unflatten s.mem r a hv 3
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv3
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  have hv4 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 128#64) 256) =
      Ty.wrap (a 4) := packed_unflatten s.mem r a hv 4
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv4
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, kernel.bb2, prepareEnv, List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, Operation.load, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, -reduceShufflevector,
    hp0, hf0, hv0, hp1, hf1, hv1, hp2, hf2, hv2, hp3, hf3, hv3, hp4, hf4, hv4]

theorem prepare_network (E : ⟪kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (k : Fin 5) :
    prepareOutputs (prepareEnv E a) k =
      prepareInstructions (Ty.wrap (a k)) (evenConstant k) (oddConstant k) := by
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [prepareOutputs, prepareEnv, prepareInstructions, prepareConstants, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, mlir_env, -reduceShufflevector]

/-- The slice's output registers have the concrete packed field representation. -/
theorem prepare_field (E : ⟪kernel.Γ⟫) (P : Point) (hP : pointReduced P)
    (hc : Constants E) (k : Fin 5) :
    prepareOutputs (prepareEnv E (packPoint P)) k = Ty.wrap (packPoint (prepare P) k) := by
  exact (prepare_network E (packPoint P) hc k).trans (prepare_pair hP k)


end Agave.Ed25519.Tables.Avx2Constructor.Add
