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

def abdc22Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v583 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%579)) (E.read (%26))
  let v584 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%580)) (E.read (%26))
  let v585 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%581)) (E.read (%26))
  let v586 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%582)) (E.read (%26))
  E[%583 := v583,
    %584 := v584,
    %585 := v585,
    %586 := v586]

/-- Exact execution of body instructions [70, 74) in bb22.
All incoming registers and the entire state remain symbolic. -/
theorem abdc22_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb22 p) E 70 4 s = .value (abdc22Env E, s) := by
  simp [runSlice, avx2Kernel.bb22, abdc22Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem abdc22_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb22 p).runBodyFrom E 70 s =
      (avx2Kernel.bb22 p).runBodyFrom (abdc22Env E) 74 s := by
  exact runBodyFrom_slice _ E (abdc22Env E) 70 4 s s (abdc22_slice p E s)

theorem abdc22_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (abdc22Env E) := by
  constructor <;> simp [abdc22Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem abdc22_reads (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hp : E.read (%26) = Ty.poisoned (.vec 8 32))
    (h0 : E.read (%579) = Ty.wrap (a 0))
    (h1 : E.read (%580) = Ty.wrap (a 1))
    (h2 : E.read (%581) = Ty.wrap (a 2))
    (h3 : E.read (%582) = Ty.wrap (a 3)) :
    (abdc22Env E).read (%583) = Ty.wrap (abdcVec (a 0)) ∧
    (abdc22Env E).read (%584) = Ty.wrap (abdcVec (a 1)) ∧
    (abdc22Env E).read (%585) = Ty.wrap (abdcVec (a 2)) ∧
    (abdc22Env E).read (%586) = Ty.wrap (abdcVec (a 3)) := by
  simp [abdc22Env, hp, h0, h1, h2, h3, abdcVec, mlir_env]

def abdc25Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v657 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%653)) (E.read (%26))
  let v658 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%654)) (E.read (%26))
  let v659 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%655)) (E.read (%26))
  let v660 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%656)) (E.read (%26))
  E[%657 := v657,
    %658 := v658,
    %659 := v659,
    %660 := v660]

/-- Exact execution of body instructions [40, 44) in bb25.
All incoming registers and the entire state remain symbolic. -/
theorem abdc25_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb25 p) E 40 4 s = .value (abdc25Env E, s) := by
  simp [runSlice, avx2Kernel.bb25, abdc25Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem abdc25_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb25 p).runBodyFrom E 40 s =
      (avx2Kernel.bb25 p).runBodyFrom (abdc25Env E) 44 s := by
  exact runBodyFrom_slice _ E (abdc25Env E) 40 4 s s (abdc25_slice p E s)

theorem abdc25_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (abdc25Env E) := by
  constructor <;> simp [abdc25Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem abdc25_reads (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hp : E.read (%26) = Ty.poisoned (.vec 8 32))
    (h0 : E.read (%653) = Ty.wrap (a 0))
    (h1 : E.read (%654) = Ty.wrap (a 1))
    (h2 : E.read (%655) = Ty.wrap (a 2))
    (h3 : E.read (%656) = Ty.wrap (a 3)) :
    (abdc25Env E).read (%657) = Ty.wrap (abdcVec (a 0)) ∧
    (abdc25Env E).read (%658) = Ty.wrap (abdcVec (a 1)) ∧
    (abdc25Env E).read (%659) = Ty.wrap (abdcVec (a 2)) ∧
    (abdc25Env E).read (%660) = Ty.wrap (abdcVec (a 3)) := by
  simp [abdc25Env, hp, h0, h1, h2, h3, abdcVec, mlir_env]

def abdc29Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v764 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%760)) (E.read (%26))
  let v765 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%761)) (E.read (%26))
  let v766 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%762)) (E.read (%26))
  let v767 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%763)) (E.read (%26))
  E[%764 := v764,
    %765 := v765,
    %766 := v766,
    %767 := v767]

/-- Exact execution of body instructions [70, 74) in bb29.
All incoming registers and the entire state remain symbolic. -/
theorem abdc29_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb29 p) E 70 4 s = .value (abdc29Env E, s) := by
  simp [runSlice, avx2Kernel.bb29, abdc29Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem abdc29_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb29 p).runBodyFrom E 70 s =
      (avx2Kernel.bb29 p).runBodyFrom (abdc29Env E) 74 s := by
  exact runBodyFrom_slice _ E (abdc29Env E) 70 4 s s (abdc29_slice p E s)

theorem abdc29_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (abdc29Env E) := by
  constructor <;> simp [abdc29Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem abdc29_reads (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hp : E.read (%26) = Ty.poisoned (.vec 8 32))
    (h0 : E.read (%760) = Ty.wrap (a 0))
    (h1 : E.read (%761) = Ty.wrap (a 1))
    (h2 : E.read (%762) = Ty.wrap (a 2))
    (h3 : E.read (%763) = Ty.wrap (a 3)) :
    (abdc29Env E).read (%764) = Ty.wrap (abdcVec (a 0)) ∧
    (abdc29Env E).read (%765) = Ty.wrap (abdcVec (a 1)) ∧
    (abdc29Env E).read (%766) = Ty.wrap (abdcVec (a 2)) ∧
    (abdc29Env E).read (%767) = Ty.wrap (abdcVec (a 3)) := by
  simp [abdc29Env, hp, h0, h1, h2, h3, abdcVec, mlir_env]

def abdc33Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v845 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%841)) (E.read (%26))
  let v846 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%842)) (E.read (%26))
  let v847 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%843)) (E.read (%26))
  let v848 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%844)) (E.read (%26))
  E[%845 := v845,
    %846 := v846,
    %847 := v847,
    %848 := v848]

/-- Exact execution of body instructions [40, 44) in bb33.
All incoming registers and the entire state remain symbolic. -/
theorem abdc33_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb33 p) E 40 4 s = .value (abdc33Env E, s) := by
  simp [runSlice, avx2Kernel.bb33, abdc33Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem abdc33_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb33 p).runBodyFrom E 40 s =
      (avx2Kernel.bb33 p).runBodyFrom (abdc33Env E) 44 s := by
  exact runBodyFrom_slice _ E (abdc33Env E) 40 4 s s (abdc33_slice p E s)

theorem abdc33_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (abdc33Env E) := by
  constructor <;> simp [abdc33Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem abdc33_reads (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hp : E.read (%26) = Ty.poisoned (.vec 8 32))
    (h0 : E.read (%841) = Ty.wrap (a 0))
    (h1 : E.read (%842) = Ty.wrap (a 1))
    (h2 : E.read (%843) = Ty.wrap (a 2))
    (h3 : E.read (%844) = Ty.wrap (a 3)) :
    (abdc33Env E).read (%845) = Ty.wrap (abdcVec (a 0)) ∧
    (abdc33Env E).read (%846) = Ty.wrap (abdcVec (a 1)) ∧
    (abdc33Env E).read (%847) = Ty.wrap (abdcVec (a 2)) ∧
    (abdc33Env E).read (%848) = Ty.wrap (abdcVec (a 3)) := by
  simp [abdc33Env, hp, h0, h1, h2, h3, abdcVec, mlir_env]

def difference22Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v588 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%587)) (E.read (%26))
  let v589 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%579)) (E.read (%26))
  let v590 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%580)) (E.read (%26))
  let v591 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%581)) (E.read (%26))
  let v592 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%582)) (E.read (%26))
  let v593 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%587)) (E.read (%26))
  let v594 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%170)) (E.read (%583))
  let v595 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%187)) (E.read (%584))
  let v596 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%187)) (E.read (%585))
  let v597 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%187)) (E.read (%586))
  let v598 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%187)) v588
  let v599 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v594 (E.read (%583))
  let v600 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v595 (E.read (%584))
  let v601 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v596 (E.read (%585))
  let v602 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v597 (E.read (%586))
  let v603 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v598 v588
  let v604 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v599 v589
  let v605 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v600 v590
  let v606 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v601 v591
  let v607 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v602 v592
  let v608 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v603 v593
  E[%588 := v588,
    %589 := v589,
    %590 := v590,
    %591 := v591,
    %592 := v592,
    %593 := v593,
    %594 := v594,
    %595 := v595,
    %596 := v596,
    %597 := v597,
    %598 := v598,
    %599 := v599,
    %600 := v600,
    %601 := v601,
    %602 := v602,
    %603 := v603,
    %604 := v604,
    %605 := v605,
    %606 := v606,
    %607 := v607,
    %608 := v608]

def difference22Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%579) = Ty.wrap (a 0) ∧
  E.read (%580) = Ty.wrap (a 1) ∧
  E.read (%581) = Ty.wrap (a 2) ∧
  E.read (%582) = Ty.wrap (a 3) ∧
  E.read (%587) = Ty.wrap (a 4) ∧
  E.read (%583) = Ty.wrap (abdcVec (a 0)) ∧
  E.read (%584) = Ty.wrap (abdcVec (a 1)) ∧
  E.read (%585) = Ty.wrap (abdcVec (a 2)) ∧
  E.read (%586) = Ty.wrap (abdcVec (a 3))

def difference22Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%604), E.read (%605), E.read (%606), E.read (%607), E.read (%608)]

/-- Exact execution of body instructions [75, 96) in bb22.
All incoming registers and the entire state remain symbolic. -/
theorem difference22_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb22 p) E 75 21 s = .value (difference22Env E, s) := by
  simp [runSlice, avx2Kernel.bb22, difference22Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem difference22_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb22 p).runBodyFrom E 75 s =
      (avx2Kernel.bb22 p).runBodyFrom (difference22Env E) 96 s := by
  exact runBodyFrom_slice _ E (difference22Env E) 75 21 s s (difference22_slice p E s)

theorem difference22_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (difference22Env E) := by
  constructor <;> simp [difference22Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem difference22_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : difference22Inputs E a) (k : Fin 5) :
    difference22Outputs (difference22Env E) k =
      diffSumInstructions (Ty.wrap (a k)) false (evenConstant k) (oddConstant k) := by
  rcases ha with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [difference22Outputs, difference22Env, diffSumInstructions, differenceConstants, abdcVec, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, h5, h6, h7, h8, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem difference22_field (E : ⟪avx2Kernel.Γ⟫) (P : Point) (hP : pointReduced P)
    (hc : Constants E) (ha : difference22Inputs E (packPoint P)) (k : Fin 5) :
    difference22Outputs (difference22Env E) k = Ty.wrap (packPoint (diffSum (shuffleABDC P)) k) := by
  exact (difference22_network E (packPoint P) hc ha k).trans (difference_pair hP false k)

def difference25Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v662 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%661)) (E.read (%26))
  let v663 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%653)) (E.read (%26))
  let v664 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%654)) (E.read (%26))
  let v665 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%655)) (E.read (%26))
  let v666 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%656)) (E.read (%26))
  let v667 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%661)) (E.read (%26))
  let v668 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%170)) (E.read (%657))
  let v669 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%187)) (E.read (%658))
  let v670 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%187)) (E.read (%659))
  let v671 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%187)) (E.read (%660))
  let v672 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%187)) v662
  let v673 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v668 (E.read (%657))
  let v674 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v669 (E.read (%658))
  let v675 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v670 (E.read (%659))
  let v676 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v671 (E.read (%660))
  let v677 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v672 v662
  let v678 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v673 v663
  let v679 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v674 v664
  let v680 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v675 v665
  let v681 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v676 v666
  let v682 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v677 v667
  E[%662 := v662,
    %663 := v663,
    %664 := v664,
    %665 := v665,
    %666 := v666,
    %667 := v667,
    %668 := v668,
    %669 := v669,
    %670 := v670,
    %671 := v671,
    %672 := v672,
    %673 := v673,
    %674 := v674,
    %675 := v675,
    %676 := v676,
    %677 := v677,
    %678 := v678,
    %679 := v679,
    %680 := v680,
    %681 := v681,
    %682 := v682]

def difference25Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%653) = Ty.wrap (a 0) ∧
  E.read (%654) = Ty.wrap (a 1) ∧
  E.read (%655) = Ty.wrap (a 2) ∧
  E.read (%656) = Ty.wrap (a 3) ∧
  E.read (%661) = Ty.wrap (a 4) ∧
  E.read (%657) = Ty.wrap (abdcVec (a 0)) ∧
  E.read (%658) = Ty.wrap (abdcVec (a 1)) ∧
  E.read (%659) = Ty.wrap (abdcVec (a 2)) ∧
  E.read (%660) = Ty.wrap (abdcVec (a 3))

def difference25Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%678), E.read (%679), E.read (%680), E.read (%681), E.read (%682)]

/-- Exact execution of body instructions [45, 66) in bb25.
All incoming registers and the entire state remain symbolic. -/
theorem difference25_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb25 p) E 45 21 s = .value (difference25Env E, s) := by
  simp [runSlice, avx2Kernel.bb25, difference25Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem difference25_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb25 p).runBodyFrom E 45 s =
      (avx2Kernel.bb25 p).runBodyFrom (difference25Env E) 66 s := by
  exact runBodyFrom_slice _ E (difference25Env E) 45 21 s s (difference25_slice p E s)

theorem difference25_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (difference25Env E) := by
  constructor <;> simp [difference25Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem difference25_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : difference25Inputs E a) (k : Fin 5) :
    difference25Outputs (difference25Env E) k =
      diffSumInstructions (Ty.wrap (a k)) false (evenConstant k) (oddConstant k) := by
  rcases ha with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [difference25Outputs, difference25Env, diffSumInstructions, differenceConstants, abdcVec, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, h5, h6, h7, h8, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem difference25_field (E : ⟪avx2Kernel.Γ⟫) (P : Point) (hP : pointReduced P)
    (hc : Constants E) (ha : difference25Inputs E (packPoint P)) (k : Fin 5) :
    difference25Outputs (difference25Env E) k = Ty.wrap (packPoint (diffSum (shuffleABDC P)) k) := by
  exact (difference25_network E (packPoint P) hc ha k).trans (difference_pair hP false k)

def difference29Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v769 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%768)) (E.read (%26))
  let v770 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%760)) (E.read (%26))
  let v771 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%761)) (E.read (%26))
  let v772 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%762)) (E.read (%26))
  let v773 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%763)) (E.read (%26))
  let v774 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%768)) (E.read (%26))
  let v775 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%170)) (E.read (%764))
  let v776 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%187)) (E.read (%765))
  let v777 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%187)) (E.read (%766))
  let v778 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%187)) (E.read (%767))
  let v779 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%187)) v769
  let v780 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v775 (E.read (%764))
  let v781 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v776 (E.read (%765))
  let v782 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v777 (E.read (%766))
  let v783 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v778 (E.read (%767))
  let v784 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v779 v769
  let v785 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v780 v770
  let v786 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v781 v771
  let v787 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v782 v772
  let v788 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v783 v773
  let v789 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v784 v774
  E[%769 := v769,
    %770 := v770,
    %771 := v771,
    %772 := v772,
    %773 := v773,
    %774 := v774,
    %775 := v775,
    %776 := v776,
    %777 := v777,
    %778 := v778,
    %779 := v779,
    %780 := v780,
    %781 := v781,
    %782 := v782,
    %783 := v783,
    %784 := v784,
    %785 := v785,
    %786 := v786,
    %787 := v787,
    %788 := v788,
    %789 := v789]

def difference29Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%760) = Ty.wrap (a 0) ∧
  E.read (%761) = Ty.wrap (a 1) ∧
  E.read (%762) = Ty.wrap (a 2) ∧
  E.read (%763) = Ty.wrap (a 3) ∧
  E.read (%768) = Ty.wrap (a 4) ∧
  E.read (%764) = Ty.wrap (abdcVec (a 0)) ∧
  E.read (%765) = Ty.wrap (abdcVec (a 1)) ∧
  E.read (%766) = Ty.wrap (abdcVec (a 2)) ∧
  E.read (%767) = Ty.wrap (abdcVec (a 3))

def difference29Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%785), E.read (%786), E.read (%787), E.read (%788), E.read (%789)]

/-- Exact execution of body instructions [75, 96) in bb29.
All incoming registers and the entire state remain symbolic. -/
theorem difference29_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb29 p) E 75 21 s = .value (difference29Env E, s) := by
  simp [runSlice, avx2Kernel.bb29, difference29Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem difference29_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb29 p).runBodyFrom E 75 s =
      (avx2Kernel.bb29 p).runBodyFrom (difference29Env E) 96 s := by
  exact runBodyFrom_slice _ E (difference29Env E) 75 21 s s (difference29_slice p E s)

theorem difference29_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (difference29Env E) := by
  constructor <;> simp [difference29Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem difference29_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : difference29Inputs E a) (k : Fin 5) :
    difference29Outputs (difference29Env E) k =
      diffSumInstructions (Ty.wrap (a k)) false (evenConstant k) (oddConstant k) := by
  rcases ha with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [difference29Outputs, difference29Env, diffSumInstructions, differenceConstants, abdcVec, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, h5, h6, h7, h8, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem difference29_field (E : ⟪avx2Kernel.Γ⟫) (P : Point) (hP : pointReduced P)
    (hc : Constants E) (ha : difference29Inputs E (packPoint P)) (k : Fin 5) :
    difference29Outputs (difference29Env E) k = Ty.wrap (packPoint (diffSum (shuffleABDC P)) k) := by
  exact (difference29_network E (packPoint P) hc ha k).trans (difference_pair hP false k)

def difference33Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v850 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6] (E.read (%849)) (E.read (%26))
  let v851 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%841)) (E.read (%26))
  let v852 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%842)) (E.read (%26))
  let v853 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%843)) (E.read (%26))
  let v854 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%844)) (E.read (%26))
  let v855 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%849)) (E.read (%26))
  let v856 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%170)) (E.read (%845))
  let v857 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%187)) (E.read (%846))
  let v858 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%187)) (E.read (%847))
  let v859 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%187)) (E.read (%848))
  let v860 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%187)) v850
  let v861 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v856 (E.read (%845))
  let v862 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v857 (E.read (%846))
  let v863 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v858 (E.read (%847))
  let v864 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v859 (E.read (%848))
  let v865 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] v860 v850
  let v866 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v861 v851
  let v867 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v862 v852
  let v868 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v863 v853
  let v869 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v864 v854
  let v870 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v865 v855
  E[%850 := v850,
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
    %865 := v865,
    %866 := v866,
    %867 := v867,
    %868 := v868,
    %869 := v869,
    %870 := v870]

def difference33Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%841) = Ty.wrap (a 0) ∧
  E.read (%842) = Ty.wrap (a 1) ∧
  E.read (%843) = Ty.wrap (a 2) ∧
  E.read (%844) = Ty.wrap (a 3) ∧
  E.read (%849) = Ty.wrap (a 4) ∧
  E.read (%845) = Ty.wrap (abdcVec (a 0)) ∧
  E.read (%846) = Ty.wrap (abdcVec (a 1)) ∧
  E.read (%847) = Ty.wrap (abdcVec (a 2)) ∧
  E.read (%848) = Ty.wrap (abdcVec (a 3))

def difference33Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%866), E.read (%867), E.read (%868), E.read (%869), E.read (%870)]

/-- Exact execution of body instructions [45, 66) in bb33.
All incoming registers and the entire state remain symbolic. -/
theorem difference33_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb33 p) E 45 21 s = .value (difference33Env E, s) := by
  simp [runSlice, avx2Kernel.bb33, difference33Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem difference33_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb33 p).runBodyFrom E 45 s =
      (avx2Kernel.bb33 p).runBodyFrom (difference33Env E) 66 s := by
  exact runBodyFrom_slice _ E (difference33Env E) 45 21 s s (difference33_slice p E s)

theorem difference33_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (difference33Env E) := by
  constructor <;> simp [difference33Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem difference33_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : difference33Inputs E a) (k : Fin 5) :
    difference33Outputs (difference33Env E) k =
      diffSumInstructions (Ty.wrap (a k)) false (evenConstant k) (oddConstant k) := by
  rcases ha with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [difference33Outputs, difference33Env, diffSumInstructions, differenceConstants, abdcVec, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, h5, h6, h7, h8, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem difference33_field (E : ⟪avx2Kernel.Γ⟫) (P : Point) (hP : pointReduced P)
    (hc : Constants E) (ha : difference33Inputs E (packPoint P)) (k : Fin 5) :
    difference33Outputs (difference33Env E) k = Ty.wrap (packPoint (diffSum (shuffleABDC P)) k) := by
  exact (difference33_network E (packPoint P) hc ha k).trans (difference_pair hP false k)


end Agave.Ed25519.Avx2PointAdd.CFG
