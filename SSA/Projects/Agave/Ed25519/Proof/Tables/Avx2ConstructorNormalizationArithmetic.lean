import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorPackingArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheArithmetic

/-! The exact parallel carry schedule restores the point invariant from
one-carry-bit serial inputs. The first packing stage preserves whole integers;
this second stage preserves their residues modulo 2^255-19. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Normalization
open Packing CacheArithmetic Avx2PointAdd PointArithmetic

/-- Initial carry32 normalization, before conversion to cached coordinates. -/
def normalizedLimbs (a : SerialPoint) (e : Fin 4) : Fin 10 → Nat :=
  carry32 (limbs a e)

def normalizedPoint (a : SerialPoint) : Point :=
  ⟨normalizedLimbs a 0, normalizedLimbs a 1, normalizedLimbs a 2, normalizedLimbs a 3⟩

/-- A uniform 26-bit bound permits at most one incoming carry in an even
limb and at most one carry times 19 in limb zero. -/
theorem carry32_reduced (z : Fin 10 → Nat) (hz : ∀ i, z i < 2^26) :
    reduced (carry32 z) := by
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2; have h3 := hz 3
  have h4 := hz 4; have h5 := hz 5; have h6 := hz 6; have h7 := hz 7
  have h8 := hz 8; have h9 := hz 9
  intro i
  unfold radix
  fin_cases i <;> simp only [carry32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  all_goals norm_num at *
  all_goals omega

theorem normalized_reduced (a : SerialPoint) (ha : ∀ e k, (a e k).toNat < 2^52) :
    pointReduced (normalizedPoint a) := by
  exact ⟨carry32_reduced _ (limbs_bound52 a ha 0),
    carry32_reduced _ (limbs_bound52 a ha 1),
    carry32_reduced _ (limbs_bound52 a ha 2),
    carry32_reduced _ (limbs_bound52 a ha 3)⟩

def serialPointValue (a : SerialPoint) : Extended K :=
  ⟨Field.serialValue (a 0), Field.serialValue (a 1),
    Field.serialValue (a 2), Field.serialValue (a 3)⟩

theorem normalized_limb_value (a : SerialPoint)
    (ha : ∀ e k, (a e k).toNat < 2^52) (e : Fin 4) :
    value (normalizedLimbs a e) = (Field.serialValue (a e) : K) := by
  rw [normalizedLimbs, value_carry32]
  unfold value
  rw [limbs_value_of_lt58 a (fun e k => lt_trans (ha e k) (by norm_num)) e]

/-- The constructor's carry normalization preserves the original point under
the verifier's actual Tight (<2^52) input invariant. -/
theorem normalized_value (a : SerialPoint) (ha : ∀ e k, (a e k).toNat < 2^52) :
    pointValue (normalizedPoint a) = serialPointValue a := by
  ext <;> exact normalized_limb_value a ha _

/-- Both arithmetic preconditions and the advertised cache value follow from
Tight inputs; no strict <2^51 premise is required. The remaining execution
bridge must connect these schedules to the retained RIR cache instructions. -/
theorem normalized_cache (a : SerialPoint) (ha : ∀ e k, (a e k).toNat < 2^52) :
    pointReduced (cache (normalizedPoint a)) ∧
      pointValue (cache (normalizedPoint a)) = avx2Cache (serialPointValue a) := by
  have h := normalized_reduced a ha
  exact ⟨cache_reduced h, (cache_value h).trans (congrArg avx2Cache (normalized_value a ha))⟩

end Agave.Ed25519.Tables.Avx2Constructor.Normalization
