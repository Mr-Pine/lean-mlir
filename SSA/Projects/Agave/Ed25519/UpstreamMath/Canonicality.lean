import SSA.Projects.Agave.Ed25519.UpstreamMath.ToBytesMath

/-!
Mathematical scalar and encoding facts for solana-ed25519 0.2.4.
The order is the same as upstream `Proofs/ScalarDenote.lean:Ell`; the
proofs here use natural numbers and do not import extracted scalar code.
`scalarParserTest` models the high-bit guard plus equality to a correct
reduction. The missing machine-code reduction/byte-equality bridge is not
assumed as an axiom or claimed proved by this file.
-/
namespace Agave.Ed25519.UpstreamMath.Canonicality

/-- Prime subgroup order, distinct from the base field modulus. -/
def ell : Nat := 2^252 + 27742317777372353535851937790883648493

theorem ell_upstream : ell =
    7237005577332262213973186563042994240857116359379907606001950938285454250989 := by
  decide

theorem ell_pos : 0 < ell := by decide

theorem ell_lt_253 : ell < 2^253 := by decide

/-- The parser's high-bit check plus exact reduction equality, at integer level. -/
def scalarParserTest (s : Nat) : Prop := s < 2^255 ∧ s = s % ell

/-- A correct reduction-equality parser accepts exactly canonical scalars. -/
theorem scalarParserTest_iff (s : Nat) : scalarParserTest s ↔ s < ell := by
  constructor
  · rintro ⟨_, h⟩
    have hmod := Nat.mod_lt s ell_pos
    omega
  · intro h
    have hbound := ell_lt_253
    exact ⟨by omega, (Nat.mod_eq_of_lt h).symm⟩

theorem canonical_has_clear_high_bit {s : Nat} (h : s < ell) : s / 2^255 = 0 := by
  have hb := (scalarParserTest_iff s).mpr h
  exact Nat.div_eq_of_lt hb.1

/-- Encoding y and the sign bit into a 256-bit natural number. -/
def encode (y sign : Nat) : Nat := y + (sign % 2) * 2^255

theorem decode_y (y sign : Nat) (hy : y < 2^255) :
    encode y sign % 2^255 = y := by
  unfold encode
  omega

theorem decode_sign (y sign : Nat) (hy : y < 2^255) :
    encode y sign / 2^255 = sign % 2 := by
  unfold encode
  omega

theorem encode_injective (y₁ y₂ s₁ s₂ : Nat)
    (h₁ : y₁ < 2^255) (h₂ : y₂ < 2^255) :
    encode y₁ s₁ = encode y₂ s₂ ↔ y₁ = y₂ ∧ s₁ % 2 = s₂ % 2 := by
  constructor
  · intro h
    constructor
    · have he := congrArg (fun n => n % 2^255) h
      simpa only [decode_y _ _ h₁, decode_y _ _ h₂] using he
    · have he := congrArg (fun n => n / 2^255) h
      simpa only [decode_sign _ _ h₁, decode_sign _ _ h₂] using he
  · rintro ⟨rfl, hs⟩
    simp only [encode, hs]

end Agave.Ed25519.UpstreamMath.Canonicality
