import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.Agreement
import SSA.Projects.Agave.Ed25519.Bridge.Challenge

/-!
Exact arithmetic certificates for one Firedancer digest.

`FiredancerScalarCanonicalAt` is a kernel-computable proposition over the actual
poison-aware source expression. Proving it establishes both defined reduction
and the canonical residue modulo L for that digest. The call theorem below
uses the exact MLIR reducer in arbitrary well-formed readable memory.

This file does not prove that every digest has a certificate. Its checked
boundary instances are concrete arithmetic results, not a universal signed
carry/range proof for the radix-2^21 algorithm.
-/

namespace Agave.Ed25519.Bridge
open LeanMLIR SLLVM Firedancer Firedancer.Common

/-- One exact source evaluation: `none` cannot satisfy the certificate, and
the 32-byte output must equal the full canonical little-endian residue. -/
def FiredancerScalarCanonicalAt (digest : BitVec 512) : Prop :=
  (ScalarArithmetic.sourceReduce digest).map packWords = some (Challenge.reducedBytes digest)

noncomputable instance (digest : BitVec 512) : Decidable (FiredancerScalarCanonicalAt digest) :=
  inferInstanceAs (Decidable ((ScalarArithmetic.sourceReduce digest).map packWords =
    some (Challenge.reducedBytes digest)))

/-- A certificate rules out poison and supplies the actual source words. -/
theorem FiredancerScalarCanonicalAt.returns {digest : BitVec 512}
    (h : FiredancerScalarCanonicalAt digest) :
    ∃ words, ScalarArithmetic.sourceReduce digest = some words := by
  change (ScalarArithmetic.sourceReduce digest).map packWords = some _ at h
  cases hw : ScalarArithmetic.sourceReduce digest with
  | none => simp [hw] at h
  | some words => exact ⟨words, rfl⟩

/-- The bytes of every returned source result have the canonical value. -/
theorem FiredancerScalarCanonicalAt.value {digest : BitVec 512}
    (h : FiredancerScalarCanonicalAt digest) (words : Fin 4 → BitVec 64)
    (hw : ScalarArithmetic.sourceReduce digest = some words) :
    (packWords words).toNat = hashToScalar digest := by
  change (ScalarArithmetic.sourceReduce digest).map packWords = some _ at h
  rw [hw] at h
  have hbytes : packWords words = Challenge.reducedBytes digest := Option.some.inj h
  rw [hbytes, Challenge.reducedBytes_toNat]

set_option maxHeartbeats 4000000 in
/-- The certified arithmetic result of the exact reducer call in arbitrary
well-formed memory. Input and output may overlap, as in the verifier. -/
theorem firedancerScalarCanonicalAt_run
    (out inp : Pointer) (state : GlobalState) (hwf : state.WF)
    (hout : IsByteBufPtr state.mem out) (hoff : inp.offset.toNat + 64 ≤ 2 ^ 64)
    (hin : Fits state.mem inp (64 * 8))
    (hcertificate : FiredancerScalarCanonicalAt (readWord hin)) :
    ∃ finalState,
      StateT.run (runFunction (fd_curve25519_scalar_reduce.denote
        (Ctxt.Valuation.ofHVector [.value inp, .value out]ₕ))) state =
        .value ([.value out]ₕ, finalState) ∧
      ∃ hout' : IsByteBufPtr finalState.mem out,
        (readBuf hout').toNat = (readWord hin).toNat % groupOrder := by
  obtain ⟨words, hwords⟩ :=
    hcertificate.returns
  obtain ⟨finalState, hrun, hequiv⟩ :=
    (ScalarArithmetic.sourceReduce_by out inp state hwf hout hoff hin).1 words hwords
  have hbuf : IsByteBufPtr (scalarOutMem state.mem out words) out :=
    isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice hout)))
  have hout' : IsByteBufPtr finalState.mem out :=
    ⟨fits_of_live?_eq (hequiv.live out.id) hbuf.1, hbuf.2⟩
  refine ⟨finalState, hrun, hout', ?_⟩
  have hread : readBuf hout' = packWords words :=
    (readBuf_of_live?_eq (hequiv.live out.id)).trans (readBuf_scalarOutMem hout hbuf)
  rw [hread]
  exact hcertificate.value words hwords


end Agave.Ed25519.Bridge
