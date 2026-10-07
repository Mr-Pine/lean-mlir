import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialLadderState
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.LinkedHelperContracts

namespace Agave.Ed25519.DoubleBase.RIR

/-- Every arithmetic call in the serial ladder is its checked imported body.
The constructor is a separate setup operation and is not a premise here. -/
theorem serialLinked_ladderHelpers (d2 : Tables.SerialConstructor.Globals)
    (panic : SerialPanic) : SerialLadderHelpers (serialLinkedPrimitives d2 panic) where
  double := SerialPoint.Execution.double_contract
  multiply := rfl
  cachedSub := serialResidualPointContracts.cachedSub
  cachedAdd := SerialPoint.Execution.cached_add_contract
  affineSub := serialResidualPointContracts.affineSub
  affineAdd := serialResidualPointContracts.affineAdd
  square := rfl

end Agave.Ed25519.DoubleBase.RIR
