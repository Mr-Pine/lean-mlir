import SSA.Projects.Agave.Ed25519.Bridge.ChallengeFiredancer
import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedResidualLeaves

/-! The Agave verifier's bounded challenge and the cross-client hash-to-scalar
specification are the same value on the same original byte transcript. These
identities have no SHA, scalar-reduction, or execution hypotheses. -/
namespace Agave.Ed25519.Bridge
open Verifier Verifier.Execution

theorem agave_transcript_eq (r a : BitVec 256) (message : HashBytes) :
    Execution.Challenge.transcript r a message = hashTranscript r a message := rfl

theorem agave_scalarChallenge_eq_messageChallenge
    (sha : Execution.Challenge.Sha512Model) (r a : BitVec 256) (message : HashBytes) :
    (ResidualLeaves.scalarChallenge sha r a message).val =
      messageChallenge sha.digest r a message := rfl

end Agave.Ed25519.Bridge
