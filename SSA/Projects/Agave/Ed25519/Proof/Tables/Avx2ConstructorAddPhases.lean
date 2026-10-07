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

def abdcEnv (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  let v840 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%836)) (E.read (%31))
  let v841 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%837)) (E.read (%31))
  let v842 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%838)) (E.read (%31))
  let v843 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%839)) (E.read (%31))
  E[%840 := v840,
    %841 := v841,
    %842 := v842,
    %843 := v843]

/-- Exact execution of body instructions [48, 52) in bb2.
All incoming registers and the entire state remain symbolic. -/
theorem abdc_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb2 p) E 48 4 s = .value (abdcEnv E, s) := by
  simp [runSlice, kernel.bb2, abdcEnv,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, -reduceShufflevector]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem abdc_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    (kernel.bb2 p).runBodyFrom E 48 s =
      (kernel.bb2 p).runBodyFrom (abdcEnv E) 52 s := by
  exact runBodyFrom_slice _ E (abdcEnv E) 48 4 s s (abdc_slice p E s)

theorem abdc_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 840 844 E (abdcEnv E) := by
  unfold abdcEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem abdc_reads (E : ⟪kernel.Γ⟫) (a : PointBlocks)
    (hp : E.read (%31) = Ty.poisoned (.vec 8 32))
    (h0 : E.read (%836) = Ty.wrap (a 0))
    (h1 : E.read (%837) = Ty.wrap (a 1))
    (h2 : E.read (%838) = Ty.wrap (a 2))
    (h3 : E.read (%839) = Ty.wrap (a 3)) :
    (abdcEnv E).read (%840) = Ty.wrap (abdcVec (a 0)) ∧
    (abdcEnv E).read (%841) = Ty.wrap (abdcVec (a 1)) ∧
    (abdcEnv E).read (%842) = Ty.wrap (abdcVec (a 2)) ∧
    (abdcEnv E).read (%843) = Ty.wrap (abdcVec (a 3)) := by
  simp [abdcEnv, hp, h0, h1, h2, h3, abdcVec, mlir_env]

def differenceEnv (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  let v845 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%844)) (E.read (%31))
  let v846 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%836)) (E.read (%31))
  let v847 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%837)) (E.read (%31))
  let v848 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%838)) (E.read (%31))
  let v849 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%839)) (E.read (%31))
  let v850 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%844)) (E.read (%31))
  let v851 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%332)) (E.read (%840))
  let v852 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%349)) (E.read (%841))
  let v853 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%349)) (E.read (%842))
  let v854 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%349)) (E.read (%843))
  let v855 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%349)) v845
  let v856 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v851 (E.read (%840))
  let v857 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v852 (E.read (%841))
  let v858 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v853 (E.read (%842))
  let v859 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v854 (E.read (%843))
  let v860 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v855 v845
  let v861 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v856 v846
  let v862 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v857 v847
  let v863 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v858 v848
  let v864 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v859 v849
  let v865 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v860 v850
  E[%845 := v845,
    %846 := v846,
    %847 := v847,
    %848 := v848,
    %849 := v849,
    %850 := v850,
    %851 := v851,
    %852 := v852,
    %853 := v853,
    %854 := v854,
    %855 := v855,
    %856 := v856,
    %857 := v857,
    %858 := v858,
    %859 := v859,
    %860 := v860,
    %861 := v861,
    %862 := v862,
    %863 := v863,
    %864 := v864,
    %865 := v865]

def differenceInputs (E : ⟪kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%836) = Ty.wrap (a 0) ∧
  E.read (%837) = Ty.wrap (a 1) ∧
  E.read (%838) = Ty.wrap (a 2) ∧
  E.read (%839) = Ty.wrap (a 3) ∧
  E.read (%844) = Ty.wrap (a 4) ∧
  E.read (%840) = Ty.wrap (abdcVec (a 0)) ∧
  E.read (%841) = Ty.wrap (abdcVec (a 1)) ∧
  E.read (%842) = Ty.wrap (abdcVec (a 2)) ∧
  E.read (%843) = Ty.wrap (abdcVec (a 3))

def differenceOutputs (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%861), E.read (%862), E.read (%863), E.read (%864), E.read (%865)]

/-- Exact execution of body instructions [53, 74) in bb2.
All incoming registers and the entire state remain symbolic. -/
theorem difference_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb2 p) E 53 21 s = .value (differenceEnv E, s) := by
  simp [runSlice, kernel.bb2, differenceEnv,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, -reduceShufflevector]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem difference_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    (kernel.bb2 p).runBodyFrom E 53 s =
      (kernel.bb2 p).runBodyFrom (differenceEnv E) 74 s := by
  exact runBodyFrom_slice _ E (differenceEnv E) 53 21 s s (difference_slice p E s)

theorem difference_constants (E : ⟪kernel.Γ⟫) (h : Constants E) :
    Constants (differenceEnv E) := by
  constructor <;> simp [differenceEnv, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN]

theorem difference_network (E : ⟪kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : differenceInputs E a) (k : Fin 5) :
    differenceOutputs (differenceEnv E) k =
      diffSumInstructions (Ty.wrap (a k)) false (evenConstant k) (oddConstant k) := by
  rcases ha with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [differenceOutputs, differenceEnv, diffSumInstructions, differenceConstants, abdcVec, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, h0, h1, h2, h3, h4, h5, h6, h7, h8, mlir_env, -reduceShufflevector]

/-- The slice's output registers have the concrete packed field representation. -/
theorem difference_field (E : ⟪kernel.Γ⟫) (P : Point) (hP : pointReduced P)
    (hc : Constants E) (ha : differenceInputs E (packPoint P)) (k : Fin 5) :
    differenceOutputs (differenceEnv E) k = Ty.wrap (packPoint (diffSum (shuffleABDC P)) k) := by
  exact (difference_network E (packPoint P) hc ha k).trans (difference_pair hP false k)

theorem difference_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 845 866 E (differenceEnv E) := by
  unfold differenceEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

def addaEnv (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  let v866 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%861)) (E.read (%31))
  let v867 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%862)) (E.read (%31))
  let v868 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%863)) (E.read (%31))
  let v869 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%864)) (E.read (%31))
  let v870 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%865)) (E.read (%31))
  E[%866 := v866,
    %867 := v867,
    %868 := v868,
    %869 := v869,
    %870 := v870]

def addaInputs (E : ⟪kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%861) = Ty.wrap (a 0) ∧
  E.read (%862) = Ty.wrap (a 1) ∧
  E.read (%863) = Ty.wrap (a 2) ∧
  E.read (%864) = Ty.wrap (a 3) ∧
  E.read (%865) = Ty.wrap (a 4)

def addaOutputs (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%866), E.read (%867), E.read (%868), E.read (%869), E.read (%870)]

/-- Exact execution of body instructions [75, 80) in bb2.
All incoming registers and the entire state remain symbolic. -/
theorem adda_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb2 p) E 75 5 s = .value (addaEnv E, s) := by
  simp [runSlice, kernel.bb2, addaEnv,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, -reduceShufflevector]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem adda_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    (kernel.bb2 p).runBodyFrom E 75 s =
      (kernel.bb2 p).runBodyFrom (addaEnv E) 80 s := by
  exact runBodyFrom_slice _ E (addaEnv E) 75 5 s s (adda_slice p E s)

theorem adda_constants (E : ⟪kernel.Γ⟫) (h : Constants E) :
    Constants (addaEnv E) := by
  constructor <;> simp [addaEnv, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN]

theorem adda_network (E : ⟪kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : addaInputs E a) (k : Fin 5) :
    addaOutputs (addaEnv E) k =
      Operation.shufflevector addaMask (Ty.wrap (a k)) (Ty.poisoned (.vec 8 32)) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [addaOutputs, addaEnv, addaMask, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, h0, h1, h2, h3, h4, mlir_env, -reduceShufflevector]

/-- The slice's output registers have the concrete packed field representation. -/
theorem adda_field (E : ⟪kernel.Γ⟫) (P : Point)
    (hc : Constants E) (ha : addaInputs E (packPoint P)) (k : Fin 5) :
    addaOutputs (addaEnv E) k = Ty.wrap (packPoint (shuffleADDA P) k) := by
  exact (adda_network E (packPoint P) hc ha k).trans (adda_pair P k)

theorem adda_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 866 871 E (addaEnv E) := by
  unfold addaEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

def cbcbEnv (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  let v871 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%861)) (E.read (%31))
  let v872 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%862)) (E.read (%31))
  let v873 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%863)) (E.read (%31))
  let v874 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%864)) (E.read (%31))
  let v875 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%865)) (E.read (%31))
  E[%871 := v871,
    %872 := v872,
    %873 := v873,
    %874 := v874,
    %875 := v875]

def cbcbInputs (E : ⟪kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%861) = Ty.wrap (a 0) ∧
  E.read (%862) = Ty.wrap (a 1) ∧
  E.read (%863) = Ty.wrap (a 2) ∧
  E.read (%864) = Ty.wrap (a 3) ∧
  E.read (%865) = Ty.wrap (a 4)

def cbcbOutputs (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%871), E.read (%872), E.read (%873), E.read (%874), E.read (%875)]

/-- Exact execution of body instructions [86, 91) in bb2.
All incoming registers and the entire state remain symbolic. -/
theorem cbcb_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb2 p) E 86 5 s = .value (cbcbEnv E, s) := by
  simp [runSlice, kernel.bb2, cbcbEnv,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, -reduceShufflevector]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem cbcb_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    (kernel.bb2 p).runBodyFrom E 86 s =
      (kernel.bb2 p).runBodyFrom (cbcbEnv E) 91 s := by
  exact runBodyFrom_slice _ E (cbcbEnv E) 86 5 s s (cbcb_slice p E s)

theorem cbcb_constants (E : ⟪kernel.Γ⟫) (h : Constants E) :
    Constants (cbcbEnv E) := by
  constructor <;> simp [cbcbEnv, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN]

theorem cbcb_network (E : ⟪kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : cbcbInputs E a) (k : Fin 5) :
    cbcbOutputs (cbcbEnv E) k =
      Operation.shufflevector cbcbMask (Ty.wrap (a k)) (Ty.poisoned (.vec 8 32)) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [cbcbOutputs, cbcbEnv, cbcbMask, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, h0, h1, h2, h3, h4, mlir_env, -reduceShufflevector]

/-- The slice's output registers have the concrete packed field representation. -/
theorem cbcb_field (E : ⟪kernel.Γ⟫) (P : Point)
    (hc : Constants E) (ha : cbcbInputs E (packPoint P)) (k : Fin 5) :
    cbcbOutputs (cbcbEnv E) k = Ty.wrap (packPoint (shuffleCBCB P) k) := by
  exact (cbcb_network E (packPoint P) hc ha k).trans (cbcb_pair P k)

theorem cbcb_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 871 876 E (cbcbEnv E) := by
  unfold cbcbEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _


end Agave.Ed25519.Tables.Avx2Constructor.Add
