import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGSlice

/-! Generated source candidates: small exact instruction intervals from the
unchanged double-base CFG. Kernel checking, not this generator, establishes
each execution equality. Field contracts use explicit packed register reads. -/
namespace Agave.Ed25519.Avx2PointAdd.CFG
open LeanMLIR.RIR DoubleBase DoubleBase.RIR Phases

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
attribute [local implicit_reducible] Ty.width

def prepare22Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v554 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%517)) (E.read (%26))
  let v555 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%518)) (E.read (%26))
  let v556 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%519)) (E.read (%26))
  let v557 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%520)) (E.read (%26))
  let v558 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%521)) (E.read (%26))
  let v559 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%135)) (E.read (%517))
  let v560 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%152)) (E.read (%518))
  let v561 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%152)) (E.read (%519))
  let v562 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%152)) (E.read (%520))
  let v563 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%152)) (E.read (%521))
  let v564 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v559 (E.read (%517))
  let v565 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v560 (E.read (%518))
  let v566 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v561 (E.read (%519))
  let v567 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v562 (E.read (%520))
  let v568 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v563 (E.read (%521))
  let v569 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v564 v554
  let v570 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v565 v555
  let v571 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v566 v556
  let v572 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v567 v557
  let v573 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v568 v558
  let v574 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v569 (E.read (%517))
  let v575 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v570 (E.read (%518))
  let v576 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v571 (E.read (%519))
  let v577 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v572 (E.read (%520))
  let v578 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v573 (E.read (%521))
  E[%554 := v554,
    %555 := v555,
    %556 := v556,
    %557 := v557,
    %558 := v558,
    %559 := v559,
    %560 := v560,
    %561 := v561,
    %562 := v562,
    %563 := v563,
    %564 := v564,
    %565 := v565,
    %566 := v566,
    %567 := v567,
    %568 := v568,
    %569 := v569,
    %570 := v570,
    %571 := v571,
    %572 := v572,
    %573 := v573,
    %574 := v574,
    %575 := v575,
    %576 := v576,
    %577 := v577,
    %578 := v578]

def prepare22Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%517) = Ty.wrap (a 0) ∧
  E.read (%518) = Ty.wrap (a 1) ∧
  E.read (%519) = Ty.wrap (a 2) ∧
  E.read (%520) = Ty.wrap (a 3) ∧
  E.read (%521) = Ty.wrap (a 4)

def prepare22Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%574), E.read (%575), E.read (%576), E.read (%577), E.read (%578)]

/-- Exact execution of body instructions [32, 57) in bb22.
All incoming registers and the entire state remain symbolic. -/
theorem prepare22_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb22 p) E 32 25 s = .value (prepare22Env E, s) := by
  simp [runSlice, avx2Kernel.bb22, prepare22Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem prepare22_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb22 p).runBodyFrom E 32 s =
      (avx2Kernel.bb22 p).runBodyFrom (prepare22Env E) 57 s := by
  exact runBodyFrom_slice _ E (prepare22Env E) 32 25 s s (prepare22_slice p E s)

theorem prepare22_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (prepare22Env E) := by
  constructor <;> simp [prepare22Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem prepare22_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : prepare22Inputs E a) (k : Fin 5) :
    prepare22Outputs (prepare22Env E) k =
      prepareInstructions (Ty.wrap (a k)) (evenConstant k) (oddConstant k) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [prepare22Outputs, prepare22Env, prepareInstructions, prepareConstants, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem prepare22_field (E : ⟪avx2Kernel.Γ⟫) (P : Point) (hP : pointReduced P)
    (hc : Constants E) (ha : prepare22Inputs E (packPoint P)) (k : Fin 5) :
    prepare22Outputs (prepare22Env E) k = Ty.wrap (packPoint (prepare P) k) := by
  exact (prepare22_network E (packPoint P) hc ha k).trans (prepare_pair hP k)

def prepare25Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v628 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%517)) (E.read (%26))
  let v629 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%518)) (E.read (%26))
  let v630 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%519)) (E.read (%26))
  let v631 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%520)) (E.read (%26))
  let v632 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%521)) (E.read (%26))
  let v633 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%135)) (E.read (%517))
  let v634 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%152)) (E.read (%518))
  let v635 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%152)) (E.read (%519))
  let v636 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%152)) (E.read (%520))
  let v637 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%152)) (E.read (%521))
  let v638 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v633 (E.read (%517))
  let v639 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v634 (E.read (%518))
  let v640 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v635 (E.read (%519))
  let v641 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v636 (E.read (%520))
  let v642 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v637 (E.read (%521))
  let v643 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v638 v628
  let v644 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v639 v629
  let v645 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v640 v630
  let v646 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v641 v631
  let v647 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v642 v632
  let v648 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v643 (E.read (%517))
  let v649 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v644 (E.read (%518))
  let v650 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v645 (E.read (%519))
  let v651 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v646 (E.read (%520))
  let v652 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v647 (E.read (%521))
  E[%628 := v628,
    %629 := v629,
    %630 := v630,
    %631 := v631,
    %632 := v632,
    %633 := v633,
    %634 := v634,
    %635 := v635,
    %636 := v636,
    %637 := v637,
    %638 := v638,
    %639 := v639,
    %640 := v640,
    %641 := v641,
    %642 := v642,
    %643 := v643,
    %644 := v644,
    %645 := v645,
    %646 := v646,
    %647 := v647,
    %648 := v648,
    %649 := v649,
    %650 := v650,
    %651 := v651,
    %652 := v652]

def prepare25Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%517) = Ty.wrap (a 0) ∧
  E.read (%518) = Ty.wrap (a 1) ∧
  E.read (%519) = Ty.wrap (a 2) ∧
  E.read (%520) = Ty.wrap (a 3) ∧
  E.read (%521) = Ty.wrap (a 4)

def prepare25Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%648), E.read (%649), E.read (%650), E.read (%651), E.read (%652)]

/-- Exact execution of body instructions [2, 27) in bb25.
All incoming registers and the entire state remain symbolic. -/
theorem prepare25_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb25 p) E 2 25 s = .value (prepare25Env E, s) := by
  simp [runSlice, avx2Kernel.bb25, prepare25Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem prepare25_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb25 p).runBodyFrom E 2 s =
      (avx2Kernel.bb25 p).runBodyFrom (prepare25Env E) 27 s := by
  exact runBodyFrom_slice _ E (prepare25Env E) 2 25 s s (prepare25_slice p E s)

theorem prepare25_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (prepare25Env E) := by
  constructor <;> simp [prepare25Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem prepare25_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : prepare25Inputs E a) (k : Fin 5) :
    prepare25Outputs (prepare25Env E) k =
      prepareInstructions (Ty.wrap (a k)) (evenConstant k) (oddConstant k) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [prepare25Outputs, prepare25Env, prepareInstructions, prepareConstants, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem prepare25_field (E : ⟪avx2Kernel.Γ⟫) (P : Point) (hP : pointReduced P)
    (hc : Constants E) (ha : prepare25Inputs E (packPoint P)) (k : Fin 5) :
    prepare25Outputs (prepare25Env E) k = Ty.wrap (packPoint (prepare P) k) := by
  exact (prepare25_network E (packPoint P) hc ha k).trans (prepare_pair hP k)

def prepare29Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v735 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%701)) (E.read (%26))
  let v736 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%700)) (E.read (%26))
  let v737 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%699)) (E.read (%26))
  let v738 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%698)) (E.read (%26))
  let v739 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%702)) (E.read (%26))
  let v740 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%135)) (E.read (%701))
  let v741 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%152)) (E.read (%700))
  let v742 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%152)) (E.read (%699))
  let v743 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%152)) (E.read (%698))
  let v744 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%152)) (E.read (%702))
  let v745 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v740 (E.read (%701))
  let v746 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v741 (E.read (%700))
  let v747 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v742 (E.read (%699))
  let v748 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v743 (E.read (%698))
  let v749 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v744 (E.read (%702))
  let v750 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v745 v735
  let v751 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v746 v736
  let v752 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v747 v737
  let v753 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v748 v738
  let v754 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v749 v739
  let v755 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v750 (E.read (%701))
  let v756 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v751 (E.read (%700))
  let v757 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v752 (E.read (%699))
  let v758 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v753 (E.read (%698))
  let v759 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v754 (E.read (%702))
  E[%735 := v735,
    %736 := v736,
    %737 := v737,
    %738 := v738,
    %739 := v739,
    %740 := v740,
    %741 := v741,
    %742 := v742,
    %743 := v743,
    %744 := v744,
    %745 := v745,
    %746 := v746,
    %747 := v747,
    %748 := v748,
    %749 := v749,
    %750 := v750,
    %751 := v751,
    %752 := v752,
    %753 := v753,
    %754 := v754,
    %755 := v755,
    %756 := v756,
    %757 := v757,
    %758 := v758,
    %759 := v759]

def prepare29Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%701) = Ty.wrap (a 0) ∧
  E.read (%700) = Ty.wrap (a 1) ∧
  E.read (%699) = Ty.wrap (a 2) ∧
  E.read (%698) = Ty.wrap (a 3) ∧
  E.read (%702) = Ty.wrap (a 4)

def prepare29Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%755), E.read (%756), E.read (%757), E.read (%758), E.read (%759)]

/-- Exact execution of body instructions [32, 57) in bb29.
All incoming registers and the entire state remain symbolic. -/
theorem prepare29_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb29 p) E 32 25 s = .value (prepare29Env E, s) := by
  simp [runSlice, avx2Kernel.bb29, prepare29Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem prepare29_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb29 p).runBodyFrom E 32 s =
      (avx2Kernel.bb29 p).runBodyFrom (prepare29Env E) 57 s := by
  exact runBodyFrom_slice _ E (prepare29Env E) 32 25 s s (prepare29_slice p E s)

theorem prepare29_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (prepare29Env E) := by
  constructor <;> simp [prepare29Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem prepare29_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : prepare29Inputs E a) (k : Fin 5) :
    prepare29Outputs (prepare29Env E) k =
      prepareInstructions (Ty.wrap (a k)) (evenConstant k) (oddConstant k) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [prepare29Outputs, prepare29Env, prepareInstructions, prepareConstants, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem prepare29_field (E : ⟪avx2Kernel.Γ⟫) (P : Point) (hP : pointReduced P)
    (hc : Constants E) (ha : prepare29Inputs E (packPoint P)) (k : Fin 5) :
    prepare29Outputs (prepare29Env E) k = Ty.wrap (packPoint (prepare P) k) := by
  exact (prepare29_network E (packPoint P) hc ha k).trans (prepare_pair hP k)

def prepare33Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v816 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%701)) (E.read (%26))
  let v817 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%700)) (E.read (%26))
  let v818 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%699)) (E.read (%26))
  let v819 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%698)) (E.read (%26))
  let v820 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, none, none, none, none] (E.read (%702)) (E.read (%26))
  let v821 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%135)) (E.read (%701))
  let v822 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%152)) (E.read (%700))
  let v823 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%152)) (E.read (%699))
  let v824 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%152)) (E.read (%698))
  let v825 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%152)) (E.read (%702))
  let v826 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v821 (E.read (%701))
  let v827 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v822 (E.read (%700))
  let v828 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v823 (E.read (%699))
  let v829 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v824 (E.read (%698))
  let v830 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, none, none, none, none] v825 (E.read (%702))
  let v831 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v826 v816
  let v832 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v827 v817
  let v833 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v828 v818
  let v834 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v829 v819
  let v835 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v830 v820
  let v836 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v831 (E.read (%701))
  let v837 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v832 (E.read (%700))
  let v838 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v833 (E.read (%699))
  let v839 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v834 (E.read (%698))
  let v840 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] v835 (E.read (%702))
  E[%816 := v816,
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
    %835 := v835,
    %836 := v836,
    %837 := v837,
    %838 := v838,
    %839 := v839,
    %840 := v840]

def prepare33Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%701) = Ty.wrap (a 0) ∧
  E.read (%700) = Ty.wrap (a 1) ∧
  E.read (%699) = Ty.wrap (a 2) ∧
  E.read (%698) = Ty.wrap (a 3) ∧
  E.read (%702) = Ty.wrap (a 4)

def prepare33Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%836), E.read (%837), E.read (%838), E.read (%839), E.read (%840)]

/-- Exact execution of body instructions [2, 27) in bb33.
All incoming registers and the entire state remain symbolic. -/
theorem prepare33_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb33 p) E 2 25 s = .value (prepare33Env E, s) := by
  simp [runSlice, avx2Kernel.bb33, prepare33Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem prepare33_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb33 p).runBodyFrom E 2 s =
      (avx2Kernel.bb33 p).runBodyFrom (prepare33Env E) 27 s := by
  exact runBodyFrom_slice _ E (prepare33Env E) 2 25 s s (prepare33_slice p E s)

theorem prepare33_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (prepare33Env E) := by
  constructor <;> simp [prepare33Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem prepare33_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : prepare33Inputs E a) (k : Fin 5) :
    prepare33Outputs (prepare33Env E) k =
      prepareInstructions (Ty.wrap (a k)) (evenConstant k) (oddConstant k) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [prepare33Outputs, prepare33Env, prepareInstructions, prepareConstants, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem prepare33_field (E : ⟪avx2Kernel.Γ⟫) (P : Point) (hP : pointReduced P)
    (hc : Constants E) (ha : prepare33Inputs E (packPoint P)) (k : Fin 5) :
    prepare33Outputs (prepare33Env E) k = Ty.wrap (packPoint (prepare P) k) := by
  exact (prepare33_network E (packPoint P) hc ha k).trans (prepare_pair hP k)


end Agave.Ed25519.Avx2PointAdd.CFG
