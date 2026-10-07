import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.Composition
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.Word
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.Instructions
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.DiffSumInstructions

/-! The register boundary between point instructions and field helpers.
Each equality below concerns actual RIR vector operations, with all eight
physical lanes explicit. No point-add execution contract is assumed. -/
namespace Agave.Ed25519.Avx2PointAdd.Phases
open LeanMLIR.RIR

abbrev PointBlocks := Fin 5 → PackedVec32

def evenIndex (k : Fin 5) : Fin 10 := ⟨2 * k.val, by omega⟩
def oddIndex (k : Fin 5) : Fin 10 := ⟨2 * k.val + 1, by omega⟩

/-- Physical A/B even, A/B odd, C/D even, C/D odd order. -/
def packPoint (P : Point) : PointBlocks := fun k =>
  let e := evenIndex k
  let o := oddIndex k
  #v[word (P.X e), word (P.Y e), word (P.X o), word (P.Y o),
     word (P.Z e), word (P.T e), word (P.Z o), word (P.T o)]

def evenConstant (k : Fin 5) : BitVec 32 := word (twiceP (evenIndex k))
def oddConstant (k : Fin 5) : BitVec 32 := word (twiceP (oddIndex k))

private theorem diff_word {a : Avx2FieldMul.Limbs} (ha : reduced a)
    (b : Avx2FieldMul.Limbs) (i : Fin 10) :
    (word (twiceP i) - word (a i)) + word (b i) = word (lazyDiff a b i) := by
  rw [BitVec.add_comm]
  exact lazyDiff_word ha i

theorem prepareVec_packPoint {P : Point} (hP : pointReduced P) (k : Fin 5) :
    prepareVec (packPoint P k) (evenConstant k) (oddConstant k) =
      packPoint (prepare P) k := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [prepareVec, packPoint, evenConstant, oddConstant, prepare,
      diff_word hP.1, lazySum_word]

theorem negateVec_packPoint {C : Point} (hC : pointReduced C) (k : Fin 5) :
    negateVec (packPoint C k) (evenConstant k) (oddConstant k) =
      packPoint (negate C) k := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [negateVec, packPoint, evenConstant, oddConstant, negate,
      lazyNeg_word hC.2.2.2]

theorem diffSumVec_packPoint {P : Point} (hP : pointReduced P) (k : Fin 5) :
    diffSumVec (packPoint P k) (evenConstant k) (oddConstant k) =
      packPoint (diffSum (shuffleABDC P)) k := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [diffSumVec, packPoint, evenConstant, oddConstant, diffSum, shuffleABDC,
      diff_word hP.1, diff_word hP.2.2.2, lazySum_word]

private theorem reduced_word_small {a : Avx2FieldMul.Limbs} (ha : reduced a)
    (i : Fin 10) : (word (a i)).toNat < 2^28 := by
  have hi := ha i
  have hm := Nat.mod_le (a i) (2^32)
  simp only [word, BitVec.toNat_ofNat]
  unfold radix at hi
  split_ifs at hi <;> norm_num at hi hm ⊢ <;> omega

theorem packPoint_small {P : Point} (hP : pointReduced P) (k : Fin 5)
    (i : Fin 8) : (packPoint P k)[i].toNat < 2^28 := by
  fin_cases i <;> simp only [packPoint, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals first
    | exact reduced_word_small hP.1 _
    | exact reduced_word_small hP.2.1 _
    | exact reduced_word_small hP.2.2.1 _
    | exact reduced_word_small hP.2.2.2 _

theorem twiceP_word_small (i : Fin 10) : (word (twiceP i)).toNat < 2^28 := by
  unfold twiceP word
  split_ifs <;> decide

/-- Preparation keeps Z/T unchanged while executing the exact poison-bearing
sub/shuffle/add network on X/Y. -/
theorem prepare_pair {P : Point} (hP : pointReduced P) (k : Fin 5) :
    prepareInstructions (Ty.wrap (packPoint P k)) (evenConstant k) (oddConstant k) =
      Ty.wrap (packPoint (prepare P) k) := by
  rw [prepareInstructions_eq, prepareVec_packPoint hP]

/-- Cached subtraction swaps X/Y and negates only T. -/
theorem negate_pair {C : Point} (hC : pointReduced C) (k : Fin 5) :
    negateInstructions (Ty.wrap (packPoint C k)) (evenConstant k) (oddConstant k) =
      Ty.wrap (packPoint (negate C) k) := by
  rw [negateInstructions_eq, negateVec_packPoint hC]

/-- The same theorem covers the CFG's unflagged pairs and the independently
optimized observation kernels' signed-overflow-flagged pairs. -/
theorem difference_pair {P : Point} (hP : pointReduced P) (signed : Bool) (k : Fin 5) :
    diffSumInstructions (Ty.wrap (packPoint P k)) signed (evenConstant k) (oddConstant k) =
      Ty.wrap (packPoint (diffSum (shuffleABDC P)) k) := by
  unfold evenConstant oddConstant
  rw [diffSumInstructions_eq _ _ _ _ (twiceP_word_small _) (twiceP_word_small _)
    (packPoint_small hP k)]
  exact congrArg Ty.wrap (diffSumVec_packPoint hP k)

def addaMask : Vector (Option (Fin 16)) 8 :=
  #v[some 0, some 5, some 2, some 7, some 5, some 0, some 7, some 2]

def cbcbMask : Vector (Option (Fin 16)) 8 :=
  #v[some 4, some 1, some 6, some 3, some 4, some 1, some 6, some 3]

theorem adda_pair (P : Point) (k : Fin 5) :
    Operation.shufflevector addaMask (Ty.wrap (packPoint P k)) (Ty.poisoned (.vec 8 32)) =
      Ty.wrap (packPoint (shuffleADDA P) k) := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [addaMask, packPoint, shuffleADDA, Ty.wrap_vec]

theorem cbcb_pair (P : Point) (k : Fin 5) :
    Operation.shufflevector cbcbMask (Ty.wrap (packPoint P k)) (Ty.poisoned (.vec 8 32)) =
      Ty.wrap (packPoint (shuffleCBCB P) k) := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [cbcbMask, packPoint, shuffleCBCB, Ty.wrap_vec]

end Agave.Ed25519.Avx2PointAdd.Phases
