import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityAllocation
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityProducts
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.SerializerXL

namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR
open Verifier.Execution.PointConstantTimeEq
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

/-- The exact environment produced by allocation and the first two product
calls. Those calls return no registers; the two GEPs are the only later writes. -/
def firstSerializerEnv (s : GlobalState) (left right : Pointer) : Env program.Γ :=
  (EqualityAllocation.preparedEnv
    (Env.init (program.args (.value left) (.value right)).get) s)[%55 := .value (right.add 80), %56 := .value (left.add 80)]

/-- All 45 hoisted constants have the source values; the 152 locals of the
first serializer are still poison because no earlier instruction writes them.
The pointers come from the actual fourth and eighth allocations. -/
theorem firstSerializer_ready (s : GlobalState) (left right : Pointer) :
    SerializerXL.embedding.pull (firstSerializerEnv s left right) =
      SerializerSource.constantEnv
        (Env.init (Encoding.Decompress.Execution.ToBytes.program.args
          (.value (EqualityAllocation.slot3 s))
          (.value (EqualityAllocation.slot7 s))).get) := by
  apply Transport.env_ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

end Agave.Ed25519.SmallOrder.Execution
