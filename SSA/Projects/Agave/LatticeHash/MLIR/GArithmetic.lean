import SSA.Projects.Agave.LatticeHash.Compression
import SSA.Projects.SLLVM.Dialect

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM
open Blake3Compression

/-- The four funnel-left shifts emitted by rustc implement BLAKE3's right rotations. -/
theorem funnel16 (x : BitVec 32) : fshlBV x x 16 = x.rotateRight 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (((x ++ x) <<< (16 : Nat)).extractLsb' 32 32).getLsbD i = _
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.getLsbD_rotateRight]
  simp only [Nat.reduceMod, hi, decide_true, Bool.true_and]
  simp only [show 32 + i < 64 by omega, show ¬(32 + i < 16) by omega,
    decide_true, decide_false, Bool.not_false, Bool.true_and]
  split_ifs <;> first | omega | (congr 1; omega)

theorem funnel20 (x : BitVec 32) : fshlBV x x 20 = x.rotateRight 12 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (((x ++ x) <<< (20 : Nat)).extractLsb' 32 32).getLsbD i = _
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.getLsbD_rotateRight]
  simp only [Nat.reduceMod, hi, decide_true, Bool.true_and]
  simp only [show 32 + i < 64 by omega, show ¬(32 + i < 20) by omega,
    decide_true, decide_false, Bool.not_false, Bool.true_and]
  split_ifs <;> first | omega | (congr 1; omega)

theorem funnel24 (x : BitVec 32) : fshlBV x x 24 = x.rotateRight 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (((x ++ x) <<< (24 : Nat)).extractLsb' 32 32).getLsbD i = _
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.getLsbD_rotateRight]
  simp only [Nat.reduceMod, hi, decide_true, Bool.true_and]
  simp only [show 32 + i < 64 by omega, show ¬(32 + i < 24) by omega,
    decide_true, decide_false, Bool.not_false, Bool.true_and]
  split_ifs <;> first | omega | (congr 1; omega)

theorem funnel25 (x : BitVec 32) : fshlBV x x 25 = x.rotateRight 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (((x ++ x) <<< (25 : Nat)).extractLsb' 32 32).getLsbD i = _
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.getLsbD_rotateRight]
  simp only [Nat.reduceMod, hi, decide_true, Bool.true_and]
  simp only [show 32 + i < 64 by omega, show ¬(32 + i < 25) by omega,
    decide_true, decide_false, Bool.not_false, Bool.true_and]
  split_ifs <;> first | omega | (congr 1; omega)

theorem funnel16_bits (x : Word) : fshlBV x x 16#32 = x.rotateRight 16 := funnel16 x

theorem funnel20_bits (x : Word) : fshlBV x x 20#32 = x.rotateRight 12 := funnel20 x

theorem funnel24_bits (x : Word) : fshlBV x x 24#32 = x.rotateRight 8 := funnel24 x

theorem funnel25_bits (x : Word) : fshlBV x x 25#32 = x.rotateRight 7 := funnel25 x

/-- Arithmetic in the compiler's actual instruction order, including reassociation. -/
def compiledG (a b c d x y : Word) : Quad Word :=
  let a₁ := a + x + b
  let d₁ := fshlBV (a₁ ^^^ d) (a₁ ^^^ d) 16
  let c₁ := d₁ + c
  let b₁ := fshlBV (c₁ ^^^ b) (c₁ ^^^ b) 20
  let a₂ := a₁ + y + b₁
  let d₂ := fshlBV (a₂ ^^^ d₁) (a₂ ^^^ d₁) 24
  let c₂ := d₂ + c₁
  let b₂ := fshlBV (c₂ ^^^ b₁) (c₂ ^^^ b₁) 25
  ⟨a₂, b₂, c₂, d₂⟩

theorem add_swap (a b c : Word) : a + b + c = a + c + b := by
  rw [BitVec.add_assoc, BitVec.add_comm b c, ← BitVec.add_assoc]

theorem word_add_left_comm (a b c : Word) : a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

theorem compiledG_eq (a b c d x y : Word) :
    compiledG a b c d x y = scalarG a b c d x y := by
  simp only [compiledG, scalarG, funnel16, funnel20, funnel24, funnel25]
  rw [add_swap a x b]
  rw [BitVec.xor_comm (a + b + x) d, BitVec.add_comm _ c]
  rw [BitVec.xor_comm (c + _) b, add_swap (a + b + x) y _]
  rw [BitVec.xor_comm (a + b + x + _ + y) _, BitVec.add_comm _ (c + _)]
  rw [BitVec.xor_comm (c + _ + _) _]

/-- Simultaneous independent G applications, in compiler instruction order. -/
def gVectors {n : Nat} (a b c d x y : Vector Word n) : Quad (Vector Word n) :=
  let q := fun i : Fin n => compiledG a[i] b[i] c[i] d[i] x[i] y[i]
  ⟨Vector.ofFn (fun i => (q i).a), Vector.ofFn (fun i => (q i).b),
   Vector.ofFn (fun i => (q i).c), Vector.ofFn (fun i => (q i).d)⟩

theorem gVectors_lane {n : Nat} (a b c d x y : Vector Word n) (i : Fin n) :
    (⟨(gVectors a b c d x y).a[i], (gVectors a b c d x y).b[i],
      (gVectors a b c d x y).c[i], (gVectors a b c d x y).d[i]⟩ : Quad Word) =
      scalarG a[i] b[i] c[i] d[i] x[i] y[i] := by
  simpa [gVectors] using compiledG_eq a[i] b[i] c[i] d[i] x[i] y[i]


end AgaveLatticeHash.MLIR
