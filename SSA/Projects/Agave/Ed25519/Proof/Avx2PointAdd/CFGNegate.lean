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

def negate22Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v539 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%530)) (E.read (%26))
  let v540 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%532)) (E.read (%26))
  let v541 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%534)) (E.read (%26))
  let v542 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%536)) (E.read (%26))
  let v543 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%538)) (E.read (%26))
  let v544 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%204)) v539
  let v545 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%221)) v540
  let v546 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%221)) v541
  let v547 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%221)) v542
  let v548 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%221)) v543
  let v549 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v539 v544
  let v550 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v540 v545
  let v551 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v541 v546
  let v552 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v542 v547
  let v553 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v543 v548
  E[%539 := v539,
    %540 := v540,
    %541 := v541,
    %542 := v542,
    %543 := v543,
    %544 := v544,
    %545 := v545,
    %546 := v546,
    %547 := v547,
    %548 := v548,
    %549 := v549,
    %550 := v550,
    %551 := v551,
    %552 := v552,
    %553 := v553]

def negate22Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%530) = Ty.wrap (a 0) ∧
  E.read (%532) = Ty.wrap (a 1) ∧
  E.read (%534) = Ty.wrap (a 2) ∧
  E.read (%536) = Ty.wrap (a 3) ∧
  E.read (%538) = Ty.wrap (a 4)

def negate22Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%549), E.read (%550), E.read (%551), E.read (%552), E.read (%553)]

/-- Exact execution of body instructions [11, 26) in bb22.
All incoming registers and the entire state remain symbolic. -/
theorem negate22_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb22 p) E 11 15 s = .value (negate22Env E, s) := by
  simp [runSlice, avx2Kernel.bb22, negate22Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem negate22_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb22 p).runBodyFrom E 11 s =
      (avx2Kernel.bb22 p).runBodyFrom (negate22Env E) 26 s := by
  exact runBodyFrom_slice _ E (negate22Env E) 11 15 s s (negate22_slice p E s)

theorem negate22_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (negate22Env E) := by
  constructor <;> simp [negate22Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem negate22_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : negate22Inputs E a) (k : Fin 5) :
    negate22Outputs (negate22Env E) k =
      negateInstructions (Ty.wrap (a k)) (evenConstant k) (oddConstant k) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [negate22Outputs, negate22Env, negateInstructions, negateConstants, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem negate22_field (E : ⟪avx2Kernel.Γ⟫) (P : Point) (hP : pointReduced P)
    (hc : Constants E) (ha : negate22Inputs E (packPoint P)) (k : Fin 5) :
    negate22Outputs (negate22Env E) k = Ty.wrap (packPoint (negate P) k) := by
  exact (negate22_network E (packPoint P) hc ha k).trans (negate_pair hP k)

def negate29Env (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  let v720 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%711)) (E.read (%26))
  let v721 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%713)) (E.read (%26))
  let v722 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%715)) (E.read (%26))
  let v723 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%717)) (E.read (%26))
  let v724 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7] (E.read (%719)) (E.read (%26))
  let v725 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%204)) v720
  let v726 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%221)) v721
  let v727 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%221)) v722
  let v728 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%221)) v723
  let v729 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%221)) v724
  let v730 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v720 v725
  let v731 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v721 v726
  let v732 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v722 v727
  let v733 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v723 v728
  let v734 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v724 v729
  E[%720 := v720,
    %721 := v721,
    %722 := v722,
    %723 := v723,
    %724 := v724,
    %725 := v725,
    %726 := v726,
    %727 := v727,
    %728 := v728,
    %729 := v729,
    %730 := v730,
    %731 := v731,
    %732 := v732,
    %733 := v733,
    %734 := v734]

def negate29Inputs (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks) : Prop :=
  E.read (%711) = Ty.wrap (a 0) ∧
  E.read (%713) = Ty.wrap (a 1) ∧
  E.read (%715) = Ty.wrap (a 2) ∧
  E.read (%717) = Ty.wrap (a 3) ∧
  E.read (%719) = Ty.wrap (a 4)

def negate29Outputs (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%730), E.read (%731), E.read (%732), E.read (%733), E.read (%734)]

/-- Exact execution of body instructions [11, 26) in bb29.
All incoming registers and the entire state remain symbolic. -/
theorem negate29_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb29 p) E 11 15 s = .value (negate29Env E, s) := by
  simp [runSlice, avx2Kernel.bb29, negate29Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env]

/-- Rejoin this local result to the unchanged imported block suffix. -/
theorem negate29_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel.bb29 p).runBodyFrom E 11 s =
      (avx2Kernel.bb29 p).runBodyFrom (negate29Env E) 26 s := by
  exact runBodyFrom_slice _ E (negate29Env E) 11 15 s s (negate29_slice p E s)

theorem negate29_constants (E : ⟪avx2Kernel.Γ⟫) (h : Constants E) :
    Constants (negate29Env E) := by
  constructor <;> simp [negate29Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

theorem negate29_network (E : ⟪avx2Kernel.Γ⟫) (a : PointBlocks)
    (hc : Constants E) (ha : negate29Inputs E a) (k : Fin 5) :
    negate29Outputs (negate29Env E) k =
      negateInstructions (Ty.wrap (a k)) (evenConstant k) (oddConstant k) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  fin_cases k <;> apply Vector.ext
  all_goals
    intro i hi
    interval_cases i <;>
      simp [negate29Outputs, negate29Env, negateInstructions, negateConstants, Operation.shufflevector, Ty.wrap_vec, evenConstant, oddConstant,
        evenIndex, oddIndex, twiceP, word, hc.poison, hc.prepare0, hc.prepareN,
        hc.difference0, hc.differenceN, hc.negate0, hc.negateN, h0, h1, h2, h3, h4, mlir_env]

/-- The slice's output registers have the concrete packed field representation. -/
theorem negate29_field (E : ⟪avx2Kernel.Γ⟫) (P : Point) (hP : pointReduced P)
    (hc : Constants E) (ha : negate29Inputs E (packPoint P)) (k : Fin 5) :
    negate29Outputs (negate29Env E) k = Ty.wrap (packPoint (negate P) k) := by
  exact (negate29_network E (packPoint P) hc ha k).trans (negate_pair hP k)


end Agave.Ed25519.Avx2PointAdd.CFG
