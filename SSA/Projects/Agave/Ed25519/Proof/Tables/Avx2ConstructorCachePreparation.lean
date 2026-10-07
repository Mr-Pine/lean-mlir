import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCachePhases

/-! Both constructor cache preparations, including the initial signed flags,
refine the same concrete Y-X, Y+X, Z, T limb transformation. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.CachePreparation
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases CachePhases
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 250000
set_option maxHeartbeats 4000000

/-- Source network shared by both inline cached conversions. -/
def instructions (signed : Bool) (x : ⟦Ty.vec 8 32⟧) (even odd : BitVec 32) :
    ⟦Ty.vec 8 32⟧ :=
  let swapped := Operation.shufflevector
    #v[some 1, some 0, some 3, some 2, none, none, none, none] x (Ty.poisoned (.vec 8 32))
  let constants : ⟦Ty.vec 8 32⟧ :=
    #v[.value even, .poison, .value odd, .poison, .poison, .poison, .poison, .poison]
  let negated := Vector.zipWith (Operation.sub {nsw := signed}) constants x
  let picked := Operation.shufflevector
    #v[some 0, some 9, some 2, some 11, none, none, none, none] negated x
  let sums := Vector.zipWith (Operation.add {}) picked swapped
  Operation.shufflevector
    #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] sums x

theorem instructions_value (signed : Bool) (x : PackedVec32) (even odd : BitVec 32)
    (he : even.toNat < 2^28) (ho : odd.toNat < 2^28)
    (hx : ∀ i : Fin 8, (x[i]).toNat < 2^28) :
    instructions signed (Ty.wrap x) even odd = Ty.wrap (prepareVec x even odd) := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [instructions, prepareVec, Operation.shufflevector, Ty.wrap_vec]
  · erw [sub32_small_value signed _ _ he (hx 0)]
    simp [Operation.add]
  · simp [Operation.add]
  · erw [sub32_small_value signed _ _ ho (hx 2)]
    simp [Operation.add]
  · simp [Operation.add]

theorem instructions_point (signed : Bool) {P : Point} (hP : pointReduced P)
    (k : Fin 5) :
    instructions signed (Ty.wrap (packPoint P k)) (evenConstant k) (oddConstant k) =
      Ty.wrap (packPoint (prepare P) k) := by
  unfold evenConstant oddConstant
  rw [instructions_value signed _ _ _ (twiceP_word_small _) (twiceP_word_small _)
    (packPoint_small hP k)]
  exact congrArg Ty.wrap (prepareVec_packPoint hP k)

def initialInput (E : ⟪kernel.Γ⟫) (P : Point) : ⟪kernel.Γ⟫ :=
  E[%31 := Ty.poisoned (.vec 8 32),
    %52 := Avx2PointAdd.CFG.prepareConstants 0,
    %70 := Avx2PointAdd.CFG.prepareConstants 1,
    %504 := Ty.wrap (packPoint P 0), %485 := Ty.wrap (packPoint P 1),
    %489 := Ty.wrap (packPoint P 2), %493 := Ty.wrap (packPoint P 3),
    %497 := Ty.wrap (packPoint P 4)]

def initialReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%525), E.read (%526), E.read (%527), E.read (%528), E.read (%529)]

private theorem initial_network_0 (E : ⟪kernel.Γ⟫) (P : Point) :
    initialReads (initialCache1 (initialCache0 (initialInput E P))) 0 =
      instructions true (Ty.wrap (packPoint P 0)) (evenConstant 0) (oddConstant 0) := by
  simp only [initialReads, initialCache0, initialCache1, initialInput,
    instructions, Avx2PointAdd.CFG.prepareConstants, evenConstant, oddConstant,
    evenIndex, oddIndex, twiceP, word, mlir_env]
  rfl

private theorem initial_network_1 (E : ⟪kernel.Γ⟫) (P : Point) :
    initialReads (initialCache1 (initialCache0 (initialInput E P))) 1 =
      instructions true (Ty.wrap (packPoint P 1)) (evenConstant 1) (oddConstant 1) := by
  simp only [initialReads, initialCache0, initialCache1, initialInput,
    instructions, Avx2PointAdd.CFG.prepareConstants, evenConstant, oddConstant,
    evenIndex, oddIndex, twiceP, word, mlir_env]
  rfl

private theorem initial_network_2 (E : ⟪kernel.Γ⟫) (P : Point) :
    initialReads (initialCache1 (initialCache0 (initialInput E P))) 2 =
      instructions true (Ty.wrap (packPoint P 2)) (evenConstant 2) (oddConstant 2) := by
  simp only [initialReads, initialCache0, initialCache1, initialInput,
    instructions, Avx2PointAdd.CFG.prepareConstants, evenConstant, oddConstant,
    evenIndex, oddIndex, twiceP, word, mlir_env]
  rfl

private theorem initial_network_3 (E : ⟪kernel.Γ⟫) (P : Point) :
    initialReads (initialCache1 (initialCache0 (initialInput E P))) 3 =
      instructions true (Ty.wrap (packPoint P 3)) (evenConstant 3) (oddConstant 3) := by
  simp only [initialReads, initialCache0, initialCache1, initialInput,
    instructions, Avx2PointAdd.CFG.prepareConstants, evenConstant, oddConstant,
    evenIndex, oddIndex, twiceP, word, mlir_env]
  rfl

private theorem initial_network_4 (E : ⟪kernel.Γ⟫) (P : Point) :
    initialReads (initialCache1 (initialCache0 (initialInput E P))) 4 =
      instructions true (Ty.wrap (packPoint P 4)) (evenConstant 4) (oddConstant 4) := by
  simp only [initialReads, initialCache0, initialCache1, initialInput,
    instructions, Avx2PointAdd.CFG.prepareConstants, evenConstant, oddConstant,
    evenIndex, oddIndex, twiceP, word, mlir_env]
  rfl

theorem initial_network (E : ⟪kernel.Γ⟫) (P : Point) (k : Fin 5) :
    initialReads (initialCache1 (initialCache0 (initialInput E P))) k =
      instructions true (Ty.wrap (packPoint P k)) (evenConstant k) (oddConstant k) := by
  fin_cases k
  · exact initial_network_0 E P
  · exact initial_network_1 E P
  · exact initial_network_2 E P
  · exact initial_network_3 E P
  · exact initial_network_4 E P

theorem initial_point (E : ⟪kernel.Γ⟫) {P : Point} (hP : pointReduced P) (k : Fin 5) :
    initialReads (initialCache1 (initialCache0 (initialInput E P))) k =
      Ty.wrap (packPoint (prepare P) k) := by
  rw [initial_network, instructions_point true hP]

def successorInput (E : ⟪kernel.Γ⟫) (P : Point) : ⟪kernel.Γ⟫ :=
  E[%31 := Ty.poisoned (.vec 8 32),
    %52 := Avx2PointAdd.CFG.prepareConstants 0,
    %70 := Avx2PointAdd.CFG.prepareConstants 1,
    %876 := Ty.wrap (packPoint P 0), %877 := Ty.wrap (packPoint P 1),
    %878 := Ty.wrap (packPoint P 2), %879 := Ty.wrap (packPoint P 3),
    %880 := Ty.wrap (packPoint P 4)]

def successorReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%901), E.read (%902), E.read (%903), E.read (%904), E.read (%905)]

private theorem successor_network_0 (E : ⟪kernel.Γ⟫) (P : Point) :
    successorReads (successorCache1 (successorCache0 (successorInput E P))) 0 =
      instructions false (Ty.wrap (packPoint P 0)) (evenConstant 0) (oddConstant 0) := by
  simp only [successorReads, successorCache0, successorCache1, successorInput,
    instructions, Avx2PointAdd.CFG.prepareConstants, evenConstant, oddConstant,
    evenIndex, oddIndex, twiceP, word, mlir_env]
  rfl

private theorem successor_network_1 (E : ⟪kernel.Γ⟫) (P : Point) :
    successorReads (successorCache1 (successorCache0 (successorInput E P))) 1 =
      instructions false (Ty.wrap (packPoint P 1)) (evenConstant 1) (oddConstant 1) := by
  simp only [successorReads, successorCache0, successorCache1, successorInput,
    instructions, Avx2PointAdd.CFG.prepareConstants, evenConstant, oddConstant,
    evenIndex, oddIndex, twiceP, word, mlir_env]
  rfl

private theorem successor_network_2 (E : ⟪kernel.Γ⟫) (P : Point) :
    successorReads (successorCache1 (successorCache0 (successorInput E P))) 2 =
      instructions false (Ty.wrap (packPoint P 2)) (evenConstant 2) (oddConstant 2) := by
  simp only [successorReads, successorCache0, successorCache1, successorInput,
    instructions, Avx2PointAdd.CFG.prepareConstants, evenConstant, oddConstant,
    evenIndex, oddIndex, twiceP, word, mlir_env]
  rfl

private theorem successor_network_3 (E : ⟪kernel.Γ⟫) (P : Point) :
    successorReads (successorCache1 (successorCache0 (successorInput E P))) 3 =
      instructions false (Ty.wrap (packPoint P 3)) (evenConstant 3) (oddConstant 3) := by
  simp only [successorReads, successorCache0, successorCache1, successorInput,
    instructions, Avx2PointAdd.CFG.prepareConstants, evenConstant, oddConstant,
    evenIndex, oddIndex, twiceP, word, mlir_env]
  rfl

private theorem successor_network_4 (E : ⟪kernel.Γ⟫) (P : Point) :
    successorReads (successorCache1 (successorCache0 (successorInput E P))) 4 =
      instructions false (Ty.wrap (packPoint P 4)) (evenConstant 4) (oddConstant 4) := by
  simp only [successorReads, successorCache0, successorCache1, successorInput,
    instructions, Avx2PointAdd.CFG.prepareConstants, evenConstant, oddConstant,
    evenIndex, oddIndex, twiceP, word, mlir_env]
  rfl

theorem successor_network (E : ⟪kernel.Γ⟫) (P : Point) (k : Fin 5) :
    successorReads (successorCache1 (successorCache0 (successorInput E P))) k =
      instructions false (Ty.wrap (packPoint P k)) (evenConstant k) (oddConstant k) := by
  fin_cases k
  · exact successor_network_0 E P
  · exact successor_network_1 E P
  · exact successor_network_2 E P
  · exact successor_network_3 E P
  · exact successor_network_4 E P

theorem successor_point (E : ⟪kernel.Γ⟫) {P : Point} (hP : pointReduced P) (k : Fin 5) :
    successorReads (successorCache1 (successorCache0 (successorInput E P))) k =
      Ty.wrap (packPoint (prepare P) k) := by
  rw [successor_network, instructions_point false hP]

end Agave.Ed25519.Tables.Avx2Constructor.CachePreparation
