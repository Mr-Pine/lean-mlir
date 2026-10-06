import SSA.Projects.Agave.Ed25519.UpstreamMath.EdwardsEncoding

/-!
Independent mathematical specification of the current strict guards.
This is not an extracted program or a Rust/LLVM refinement theorem. Decoder,
small-order, scalar reduction, compression and recomputation refinement remain
separate obligations. All semantic assumptions are explicit theorem parameters.
-/
namespace Agave.Ed25519.UpstreamMath.Strict

/-- Acceptance after mathematical interpretations of the current strict
verifier's decoding, scalar and group operations have been supplied. -/
def Accepts {Point : Type*} (encode : Point → Nat)
    (smallOrder : Point → Prop) (minusA : Point)
    (decodedR : Option Point) (s rBytes : Nat) (recomputed : Point) : Prop :=
  ¬ smallOrder minusA ∧
    ∃ R, decodedR = some R ∧ ¬ smallOrder R ∧
      s < Canonicality.ell ∧ encode recomputed = rBytes

/-- Encoding injectivity upgrades the byte equation to a point equation.
All current strict guards remain present; none is replaced by a blacklist. -/
theorem point_equation {Point : Type*} (encode : Point → Nat)
    (injective : Function.Injective encode) (smallOrder : Point → Prop)
    (minusA R recomputed : Point) (s rBytes : Nat)
    (henc : rBytes = encode R) :
    Accepts encode smallOrder minusA (some R) s rBytes recomputed ↔
      ¬ smallOrder minusA ∧ ¬ smallOrder R ∧
        s < Canonicality.ell ∧ recomputed = R := by
  unfold Accepts
  simp only [Option.some.injEq, exists_eq_left, henc]
  rw [injective.eq_iff]

theorem rejects_decode_failure {Point : Type*} (encode : Point → Nat)
    (smallOrder : Point → Prop) (minusA recomputed : Point) (s rBytes : Nat) :
    ¬ Accepts encode smallOrder minusA none s rBytes recomputed := by
  simp [Accepts]

end Agave.Ed25519.UpstreamMath.Strict
