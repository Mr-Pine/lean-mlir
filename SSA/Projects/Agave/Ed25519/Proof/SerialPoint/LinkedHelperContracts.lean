import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.ResidualContractsLink
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialPointContracts
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SerialContractsLink

namespace Agave.Ed25519.DoubleBase.RIR

/-- All three formerly residual point leaves resolve to their imported bodies. -/
theorem serialResidualPointContracts : SerialResidualPointContracts where
  cachedSub := SerialPoint.Execution.cached_sub_contract
  affineSub := SerialPoint.Execution.affine_sub_contract
  affineAdd := SerialPoint.Execution.affine_add_contract

/-- Full linked helper bundle: the only remaining premise is the independent
table constructor contract. Every point and field helper is discharged here. -/
theorem serialLinkedHelperContracts (d2 : Tables.SerialConstructor.Globals)
    (panic : SerialPanic)
    (table : SerialContracts.TableContract
      (Tables.SerialConstructor.kernel serialConstructorPrimitives d2).call) :
    SerialContracts.Helpers (serialLinkedPrimitives d2 panic) where
  table := table
  double := SerialPoint.Execution.double_contract
  multiply := rfl
  cachedSub := SerialPoint.Execution.cached_sub_contract
  cachedAdd := SerialPoint.Execution.cached_add_contract
  affineSub := SerialPoint.Execution.affine_sub_contract
  affineAdd := SerialPoint.Execution.affine_add_contract
  square := SerialPoint.Execution.square_contract

end Agave.Ed25519.DoubleBase.RIR
