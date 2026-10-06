import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.Word
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.Reduced
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Words

/-! Word-level composition: multiplication plus the exact carry schedule.
The compiler's SIMD shuffle/bitcast and memory refinement remains a separate
obligation; this is not an execution theorem for `Program.program`. -/
namespace Agave.Ed25519.Avx2FieldMul

def wordProduct (x y : Limbs) : Fin 10 → BitVec 64 :=
  Reduce64.Word.reduce (wordColumn x y)

theorem wordProduct_toNat {x y : Limbs}
    (hx : LeftBound x) (hy : RightBound y) (i : Fin 10) :
    (wordProduct x y i).toNat = product x y i := by
  have hcol : Reduce64.ColumnsBound (fun k => (wordColumn x y k).toNat) := by
    intro k
    change (wordColumn x y k).toNat < 2^63
    rw [asymmetric_wordColumn_toNat hx hy]
    exact asymmetric_column_lt_i64 hx hy k
  rw [wordProduct, Reduce64.Word.toNat_reduce _ hcol]
  simp only [asymmetric_wordColumn_toNat hx hy]
  rfl

theorem wordProduct_mod {x y : Limbs} (hx : LeftBound x) (hy : RightBound y) :
    Field.decode10 (fun i => (wordProduct x y i).toNat) % Field.p =
      (Field.decode10 x * Field.decode10 y) % Field.p := by
  simp only [wordProduct_toNat hx hy]
  exact product_mod x y

theorem wordProduct_bounds {x y : Limbs} (hx : LeftBound x) (hy : RightBound y)
    (i : Fin 10) :
    (wordProduct x y i).toNat < 2 ^ (if i.val % 2 = 0 then 26 else 25) + 2 ^ 18 := by
  rw [wordProduct_toNat hx hy]
  exact asymmetric_product_bounds hx hy i

end Agave.Ed25519.Avx2FieldMul
