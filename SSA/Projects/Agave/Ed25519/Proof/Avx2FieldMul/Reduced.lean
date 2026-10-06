import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.Asymmetric
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Arithmetic

/-! Composition of the integer convolution and two-chain carry specification.
This file proves the arithmetic contract. It does not assert that the extracted
RIR program executes this specification. -/
namespace Agave.Ed25519.Avx2FieldMul

/-- Integer specification of one of the four parallel field multiplications. -/
def product (x y : Limbs) : Limbs := Reduce64.reduce (column x y)

theorem product_mod (x y : Limbs) :
    Field.decode10 (product x y) % Field.p =
      (Field.decode10 x * Field.decode10 y) % Field.p := by
  exact (Reduce64.residue (column x y)).symm.trans (convolution_mod x y)

theorem product_bounds {x y : Limbs} (hx : Bounded x) (hy : Bounded y) :
    ∀ i, product x y i < 2 ^ (if i.val % 2 = 0 then 26 else 25) + 2 ^ 18 :=
  Reduce64.output_bounds _ (column_bound hx hy)

/-- The arithmetic output can be fed to another multiplication with the same
one-bit-slack premise. -/
theorem product_bounded {x y : Limbs} (hx : Bounded x) (hy : Bounded y) :
    Bounded (product x y) := by
  intro i
  have hi := product_bounds hx hy i
  split_ifs at hi ⊢ <;> norm_num at hi ⊢ <;> omega

/-- This statement applies independently to A, B, C and D, using the actual
physical SIMD lane layout from `Field.Packed`. -/
theorem packed_product_mod (x y : Field.Packed) (e : Field.Element) :
    Field.decode10 (product (Field.flatten (Field.lo x e) (Field.hi x e))
      (Field.flatten (Field.lo y e) (Field.hi y e))) % Field.p =
      (Field.packedValue x e * Field.packedValue y e) % Field.p := by
  rw [product_mod, Field.decode_flatten, Field.decode_flatten]
  rfl

/-- Callers that establish the shared loose coefficient invariant discharge
all u32 and u64 convolution-overflow premises. -/
theorem loose_columns_bound {x y : Field.Packed} {e : Field.Element}
    (hx : Field.Loose2625 (Field.lo x e) (Field.hi x e))
    (hy : Field.Loose2625 (Field.lo y e) (Field.hi y e)) :
    ∀ k, column (Field.flatten (Field.lo x e) (Field.hi x e))
      (Field.flatten (Field.lo y e) (Field.hi y e)) k < 2 ^ 63 :=
  column_bound (Field.loose_mulBound hx) (Field.loose_mulBound hy)

/-- Reduction restores the shared loose output bound after multiplication
under the asymmetric point-caller contract. -/
theorem asymmetric_product_bounds {x y : Limbs}
    (hx : LeftBound x) (hy : RightBound y) :
    ∀ i, product x y i < 2 ^ (if i.val % 2 = 0 then 26 else 25) + 2 ^ 18 :=
  Reduce64.output_bounds _ (asymmetric_column_lt_i64 hx hy)

theorem asymmetric_product_bounded {x y : Limbs}
    (hx : LeftBound x) (hy : RightBound y) : Bounded (product x y) := by
  intro i
  have hi := asymmetric_product_bounds hx hy i
  split_ifs at hi ⊢ <;> norm_num at hi ⊢ <;> omega

end Agave.Ed25519.Avx2FieldMul
