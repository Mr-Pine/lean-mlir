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

def adda22Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v609 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%604)) (E.read (%26))
  let v610 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%605)) (E.read (%26))
  let v611 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%606)) (E.read (%26))
  let v612 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%607)) (E.read (%26))
  let v613 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%608)) (E.read (%26))
  E[%609 := v609,
    %610 := v610,
    %611 := v611,
    %612 := v612,
    %613 := v613]

def adda22Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%604) = Ty.wrap (a 0) ∧
  E.read (%605) = Ty.wrap (a 1) ∧
  E.read (%606) = Ty.wrap (a 2) ∧
  E.read (%607) = Ty.wrap (a 3) ∧
  E.read (%608) = Ty.wrap (a 4)

def adda22Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%609), E.read (%610), E.read (%611), E.read (%612), E.read (%613)]

/-- Exact execution of body instructions [97, 102) in bb22.
All incoming registers and the entire state remain symbolic. -/
theorem adda22_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb22 p) E 97 5 s = .value (adda22Env E, s) := by
  simp [runSlice, avx2Kernel.bb22, adda22Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem adda22_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb22 p).runBodyFrom E 97 s =
      (avx2Kernel.bb22 p).runBodyFrom (adda22Env E) 102 s := by
  exact runBodyFrom_slice _ E (adda22Env E) 97 5 s s (adda22_slice p E s)

theorem adda22_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (adda22Env E) := by
  constructor <;> simp [adda22Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem adda22_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : adda22Inputs E a) (k : Fin 5) :
    adda22Outputs (adda22Env E) k =
      Operation.shufflevector addaMask (Ty.wrap (a k)) (Ty.poisoned (.vec 8 32)) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [adda22Outputs, adda22Env, addaMask, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem adda22_field (E : ⟪avx2Kernel.Γ⟫) (P : Point)
    (hc : Constants E) (ha : adda22Inputs E (packPoint P)) (k : Fin 5) :
    adda22Outputs (adda22Env E) k = Ty.wrap (packPoint (shuffleADDA P) k) := by
  exact (adda22_network E (packPoint P) hc ha k).trans (adda_pair P k)

def cbcb22Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v614 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%604)) (E.read (%26))
  let v615 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%605)) (E.read (%26))
  let v616 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%606)) (E.read (%26))
  let v617 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%607)) (E.read (%26))
  let v618 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%608)) (E.read (%26))
  E[%614 := v614,
    %615 := v615,
    %616 := v616,
    %617 := v617,
    %618 := v618]

def cbcb22Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%604) = Ty.wrap (a 0) ∧
  E.read (%605) = Ty.wrap (a 1) ∧
  E.read (%606) = Ty.wrap (a 2) ∧
  E.read (%607) = Ty.wrap (a 3) ∧
  E.read (%608) = Ty.wrap (a 4)

def cbcb22Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%614), E.read (%615), E.read (%616), E.read (%617), E.read (%618)]

/-- Exact execution of body instructions [108, 113) in bb22.
All incoming registers and the entire state remain symbolic. -/
theorem cbcb22_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb22 p) E 108 5 s = .value (cbcb22Env E, s) := by
  simp [runSlice, avx2Kernel.bb22, cbcb22Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem cbcb22_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb22 p).runBodyFrom E 108 s =
      (avx2Kernel.bb22 p).runBodyFrom (cbcb22Env E) 113 s := by
  exact runBodyFrom_slice _ E (cbcb22Env E) 108 5 s s (cbcb22_slice p E s)

theorem cbcb22_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (cbcb22Env E) := by
  constructor <;> simp [cbcb22Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem cbcb22_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : cbcb22Inputs E a) (k : Fin 5) :
    cbcb22Outputs (cbcb22Env E) k =
      Operation.shufflevector cbcbMask (Ty.wrap (a k)) (Ty.poisoned (.vec 8 32)) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [cbcb22Outputs, cbcb22Env, cbcbMask, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem cbcb22_field (E : ⟪avx2Kernel.Γ⟫) (P : Point)
    (hc : Constants E) (ha : cbcb22Inputs E (packPoint P)) (k : Fin 5) :
    cbcb22Outputs (cbcb22Env E) k = Ty.wrap (packPoint (shuffleCBCB P) k) := by
  exact (cbcb22_network E (packPoint P) hc ha k).trans (cbcb_pair P k)

def adda25Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v683 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%678)) (E.read (%26))
  let v684 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%679)) (E.read (%26))
  let v685 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%680)) (E.read (%26))
  let v686 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%681)) (E.read (%26))
  let v687 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%682)) (E.read (%26))
  E[%683 := v683,
    %684 := v684,
    %685 := v685,
    %686 := v686,
    %687 := v687]

def adda25Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%678) = Ty.wrap (a 0) ∧
  E.read (%679) = Ty.wrap (a 1) ∧
  E.read (%680) = Ty.wrap (a 2) ∧
  E.read (%681) = Ty.wrap (a 3) ∧
  E.read (%682) = Ty.wrap (a 4)

def adda25Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%683), E.read (%684), E.read (%685), E.read (%686), E.read (%687)]

/-- Exact execution of body instructions [67, 72) in bb25.
All incoming registers and the entire state remain symbolic. -/
theorem adda25_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb25 p) E 67 5 s = .value (adda25Env E, s) := by
  simp [runSlice, avx2Kernel.bb25, adda25Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem adda25_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb25 p).runBodyFrom E 67 s =
      (avx2Kernel.bb25 p).runBodyFrom (adda25Env E) 72 s := by
  exact runBodyFrom_slice _ E (adda25Env E) 67 5 s s (adda25_slice p E s)

theorem adda25_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (adda25Env E) := by
  constructor <;> simp [adda25Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem adda25_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : adda25Inputs E a) (k : Fin 5) :
    adda25Outputs (adda25Env E) k =
      Operation.shufflevector addaMask (Ty.wrap (a k)) (Ty.poisoned (.vec 8 32)) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [adda25Outputs, adda25Env, addaMask, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem adda25_field (E : ⟪avx2Kernel.Γ⟫) (P : Point)
    (hc : Constants E) (ha : adda25Inputs E (packPoint P)) (k : Fin 5) :
    adda25Outputs (adda25Env E) k = Ty.wrap (packPoint (shuffleADDA P) k) := by
  exact (adda25_network E (packPoint P) hc ha k).trans (adda_pair P k)

def cbcb25Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v688 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%678)) (E.read (%26))
  let v689 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%679)) (E.read (%26))
  let v690 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%680)) (E.read (%26))
  let v691 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%681)) (E.read (%26))
  let v692 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%682)) (E.read (%26))
  E[%688 := v688,
    %689 := v689,
    %690 := v690,
    %691 := v691,
    %692 := v692]

def cbcb25Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%678) = Ty.wrap (a 0) ∧
  E.read (%679) = Ty.wrap (a 1) ∧
  E.read (%680) = Ty.wrap (a 2) ∧
  E.read (%681) = Ty.wrap (a 3) ∧
  E.read (%682) = Ty.wrap (a 4)

def cbcb25Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%688), E.read (%689), E.read (%690), E.read (%691), E.read (%692)]

/-- Exact execution of body instructions [78, 83) in bb25.
All incoming registers and the entire state remain symbolic. -/
theorem cbcb25_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb25 p) E 78 5 s = .value (cbcb25Env E, s) := by
  simp [runSlice, avx2Kernel.bb25, cbcb25Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem cbcb25_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb25 p).runBodyFrom E 78 s =
      (avx2Kernel.bb25 p).runBodyFrom (cbcb25Env E) 83 s := by
  exact runBodyFrom_slice _ E (cbcb25Env E) 78 5 s s (cbcb25_slice p E s)

theorem cbcb25_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (cbcb25Env E) := by
  constructor <;> simp [cbcb25Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem cbcb25_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : cbcb25Inputs E a) (k : Fin 5) :
    cbcb25Outputs (cbcb25Env E) k =
      Operation.shufflevector cbcbMask (Ty.wrap (a k)) (Ty.poisoned (.vec 8 32)) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [cbcb25Outputs, cbcb25Env, cbcbMask, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem cbcb25_field (E : ⟪avx2Kernel.Γ⟫) (P : Point)
    (hc : Constants E) (ha : cbcb25Inputs E (packPoint P)) (k : Fin 5) :
    cbcb25Outputs (cbcb25Env E) k = Ty.wrap (packPoint (shuffleCBCB P) k) := by
  exact (cbcb25_network E (packPoint P) hc ha k).trans (cbcb_pair P k)

def adda29Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v790 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%785)) (E.read (%26))
  let v791 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%786)) (E.read (%26))
  let v792 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%787)) (E.read (%26))
  let v793 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%788)) (E.read (%26))
  let v794 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%789)) (E.read (%26))
  E[%790 := v790,
    %791 := v791,
    %792 := v792,
    %793 := v793,
    %794 := v794]

def adda29Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%785) = Ty.wrap (a 0) ∧
  E.read (%786) = Ty.wrap (a 1) ∧
  E.read (%787) = Ty.wrap (a 2) ∧
  E.read (%788) = Ty.wrap (a 3) ∧
  E.read (%789) = Ty.wrap (a 4)

def adda29Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%790), E.read (%791), E.read (%792), E.read (%793), E.read (%794)]

/-- Exact execution of body instructions [97, 102) in bb29.
All incoming registers and the entire state remain symbolic. -/
theorem adda29_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb29 p) E 97 5 s = .value (adda29Env E, s) := by
  simp [runSlice, avx2Kernel.bb29, adda29Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem adda29_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb29 p).runBodyFrom E 97 s =
      (avx2Kernel.bb29 p).runBodyFrom (adda29Env E) 102 s := by
  exact runBodyFrom_slice _ E (adda29Env E) 97 5 s s (adda29_slice p E s)

theorem adda29_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (adda29Env E) := by
  constructor <;> simp [adda29Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem adda29_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : adda29Inputs E a) (k : Fin 5) :
    adda29Outputs (adda29Env E) k =
      Operation.shufflevector addaMask (Ty.wrap (a k)) (Ty.poisoned (.vec 8 32)) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [adda29Outputs, adda29Env, addaMask, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem adda29_field (E : ⟪avx2Kernel.Γ⟫) (P : Point)
    (hc : Constants E) (ha : adda29Inputs E (packPoint P)) (k : Fin 5) :
    adda29Outputs (adda29Env E) k = Ty.wrap (packPoint (shuffleADDA P) k) := by
  exact (adda29_network E (packPoint P) hc ha k).trans (adda_pair P k)

def cbcb29Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v795 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%785)) (E.read (%26))
  let v796 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%786)) (E.read (%26))
  let v797 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%787)) (E.read (%26))
  let v798 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%788)) (E.read (%26))
  let v799 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%789)) (E.read (%26))
  E[%795 := v795,
    %796 := v796,
    %797 := v797,
    %798 := v798,
    %799 := v799]

def cbcb29Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%785) = Ty.wrap (a 0) ∧
  E.read (%786) = Ty.wrap (a 1) ∧
  E.read (%787) = Ty.wrap (a 2) ∧
  E.read (%788) = Ty.wrap (a 3) ∧
  E.read (%789) = Ty.wrap (a 4)

def cbcb29Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%795), E.read (%796), E.read (%797), E.read (%798), E.read (%799)]

/-- Exact execution of body instructions [108, 113) in bb29.
All incoming registers and the entire state remain symbolic. -/
theorem cbcb29_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb29 p) E 108 5 s = .value (cbcb29Env E, s) := by
  simp [runSlice, avx2Kernel.bb29, cbcb29Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem cbcb29_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb29 p).runBodyFrom E 108 s =
      (avx2Kernel.bb29 p).runBodyFrom (cbcb29Env E) 113 s := by
  exact runBodyFrom_slice _ E (cbcb29Env E) 108 5 s s (cbcb29_slice p E s)

theorem cbcb29_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (cbcb29Env E) := by
  constructor <;> simp [cbcb29Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem cbcb29_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : cbcb29Inputs E a) (k : Fin 5) :
    cbcb29Outputs (cbcb29Env E) k =
      Operation.shufflevector cbcbMask (Ty.wrap (a k)) (Ty.poisoned (.vec 8 32)) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [cbcb29Outputs, cbcb29Env, cbcbMask, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem cbcb29_field (E : ⟪avx2Kernel.Γ⟫) (P : Point)
    (hc : Constants E) (ha : cbcb29Inputs E (packPoint P)) (k : Fin 5) :
    cbcb29Outputs (cbcb29Env E) k = Ty.wrap (packPoint (shuffleCBCB P) k) := by
  exact (cbcb29_network E (packPoint P) hc ha k).trans (cbcb_pair P k)

def adda33Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v871 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%866)) (E.read (%26))
  let v872 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%867)) (E.read (%26))
  let v873 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%868)) (E.read (%26))
  let v874 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%869)) (E.read (%26))
  let v875 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2] (E.read (%870)) (E.read (%26))
  E[%871 := v871,
    %872 := v872,
    %873 := v873,
    %874 := v874,
    %875 := v875]

def adda33Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%866) = Ty.wrap (a 0) ∧
  E.read (%867) = Ty.wrap (a 1) ∧
  E.read (%868) = Ty.wrap (a 2) ∧
  E.read (%869) = Ty.wrap (a 3) ∧
  E.read (%870) = Ty.wrap (a 4)

def adda33Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%871), E.read (%872), E.read (%873), E.read (%874), E.read (%875)]

/-- Exact execution of body instructions [67, 72) in bb33.
All incoming registers and the entire state remain symbolic. -/
theorem adda33_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb33 p) E 67 5 s = .value (adda33Env E, s) := by
  simp [runSlice, avx2Kernel.bb33, adda33Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem adda33_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb33 p).runBodyFrom E 67 s =
      (avx2Kernel.bb33 p).runBodyFrom (adda33Env E) 72 s := by
  exact runBodyFrom_slice _ E (adda33Env E) 67 5 s s (adda33_slice p E s)

theorem adda33_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (adda33Env E) := by
  constructor <;> simp [adda33Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem adda33_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : adda33Inputs E a) (k : Fin 5) :
    adda33Outputs (adda33Env E) k =
      Operation.shufflevector addaMask (Ty.wrap (a k)) (Ty.poisoned (.vec 8 32)) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [adda33Outputs, adda33Env, addaMask, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem adda33_field (E : ⟪avx2Kernel.Γ⟫) (P : Point)
    (hc : Constants E) (ha : adda33Inputs E (packPoint P)) (k : Fin 5) :
    adda33Outputs (adda33Env E) k = Ty.wrap (packPoint (shuffleADDA P) k) := by
  exact (adda33_network E (packPoint P) hc ha k).trans (adda_pair P k)

def cbcb33Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v876 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%866)) (E.read (%26))
  let v877 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%867)) (E.read (%26))
  let v878 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%868)) (E.read (%26))
  let v879 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%869)) (E.read (%26))
  let v880 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3] (E.read (%870)) (E.read (%26))
  E[%876 := v876,
    %877 := v877,
    %878 := v878,
    %879 := v879,
    %880 := v880]

def cbcb33Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%866) = Ty.wrap (a 0) ∧
  E.read (%867) = Ty.wrap (a 1) ∧
  E.read (%868) = Ty.wrap (a 2) ∧
  E.read (%869) = Ty.wrap (a 3) ∧
  E.read (%870) = Ty.wrap (a 4)

def cbcb33Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%876), E.read (%877), E.read (%878), E.read (%879), E.read (%880)]

/-- Exact execution of body instructions [78, 83) in bb33.
All incoming registers and the entire state remain symbolic. -/
theorem cbcb33_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb33 p) E 78 5 s = .value (cbcb33Env E, s) := by
  simp [runSlice, avx2Kernel.bb33, cbcb33Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem cbcb33_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb33 p).runBodyFrom E 78 s =
      (avx2Kernel.bb33 p).runBodyFrom (cbcb33Env E) 83 s := by
  exact runBodyFrom_slice _ E (cbcb33Env E) 78 5 s s (cbcb33_slice p E s)

theorem cbcb33_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (cbcb33Env E) := by
  constructor <;> simp [cbcb33Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem cbcb33_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : cbcb33Inputs E a) (k : Fin 5) :
    cbcb33Outputs (cbcb33Env E) k =
      Operation.shufflevector cbcbMask (Ty.wrap (a k)) (Ty.poisoned (.vec 8 32)) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [cbcb33Outputs, cbcb33Env, cbcbMask, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem cbcb33_field (E : ⟪avx2Kernel.Γ⟫) (P : Point)
    (hc : Constants E) (ha : cbcb33Inputs E (packPoint P)) (k : Fin 5) :
    cbcb33Outputs (cbcb33Env E) k = Ty.wrap (packPoint (shuffleCBCB P) k) := by
  exact (cbcb33_network E (packPoint P) hc ha k).trans (cbcb_pair P k)


end Agave.Ed25519.Avx2PointAdd.CFG
