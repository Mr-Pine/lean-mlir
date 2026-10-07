import SSA.Projects.Agave.Ed25519.Bridge.FiredancerScalarArithmetic
import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.Correctness

/-! The one-digest scalar correctness certificate is now available for every
512-bit digest, from the exact source evaluator and checked LLVM semantics. -/

namespace Agave.Ed25519.Bridge
open LeanMLIR SLLVM Firedancer Firedancer.Common

set_option maxHeartbeats 4000000 in
/-- The scalar obligation used by invocation readiness holds for every digest. -/
theorem firedancerScalarCanonical (digest : BitVec 512) :
    FiredancerScalarCanonicalAt digest := by
  obtain ⟨words, hw, hv⟩ := ScalarArithmetic.sourceReduce_correct digest
  change (ScalarArithmetic.sourceReduce digest).map packWords = some _
  refine (congrArg (Option.map packWords) hw).trans ?_
  change some (packWords words) = some (Challenge.reducedBytes digest)
  apply congrArg some
  apply BitVec.eq_of_toNat_eq
  rw [hv, Challenge.reducedBytes_toNat]
  rfl

/-- The exact reducer succeeds on every readable 64-byte input in well-formed
memory. Its output is the canonical little-endian residue, including when the
input and output overlap. -/
theorem firedancerScalarReduce_run
    (out inp : Pointer) (state : GlobalState) (hwf : state.WF)
    (hout : IsByteBufPtr state.mem out) (hoff : inp.offset.toNat + 64 ≤ 2 ^ 64)
    (hin : Fits state.mem inp (64 * 8)) :
    ∃ finalState,
      StateT.run (runFunction (fd_curve25519_scalar_reduce.denote
        (Ctxt.Valuation.ofHVector [.value inp, .value out]ₕ))) state =
        .value ([.value out]ₕ, finalState) ∧
      ∃ hout' : IsByteBufPtr finalState.mem out,
        (readBuf hout').toNat = (readWord hin).toNat % groupOrder :=
  firedancerScalarCanonicalAt_run out inp state hwf hout hoff hin
    (firedancerScalarCanonical (readWord hin))

end Agave.Ed25519.Bridge
