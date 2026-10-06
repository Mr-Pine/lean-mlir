import SSA.Projects.Agave.Ed25519.Proof.Conformance.ScalarAvx2
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Composition

namespace Agave.Ed25519.Conformance

open PointArithmetic Tables

/-- The scalar/AVX2 equality includes the emitted digit-control network and its
poison checks. NAF safety discharges those checks without a successful-run
premise. This is an instruction-control endpoint, not a whole CFG theorem. -/
theorem scalar_avx2_byte_control_compression_eq (h s : Nat) (A : Extended F) :
    (compressMath <$> DoubleBase.Execution.serialByteControl h A s) =
      (compressMath <$> DoubleBase.Execution.avx2ByteControl h A s) :=
  (DoubleBase.Execution.double_base_byte_control_compress_eq encodeAffine h s A).symm

end Agave.Ed25519.Conformance
