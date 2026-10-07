import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialLinked

/-! Independent interface for the three serial residual point primitives. -/
namespace Agave.Ed25519.DoubleBase.RIR
structure SerialResidualPointContracts : Prop where
  cachedSub : SerialContracts.BinaryPointContract SerialPoint.cached_sub.call 160
    SerialContracts.readCached SerialPoint.cachedSubCompleted
  affineSub : SerialContracts.BinaryPointContract SerialPoint.affine_sub.call 120
    SerialContracts.readAffineCached
    (fun P C => SerialPoint.affineSubCompleted P C.X C.Y C.T)
  affineAdd : SerialContracts.BinaryPointContract SerialPoint.affine_add.call 120
    SerialContracts.readAffineCached
    (fun P C => SerialPoint.affineAddCompleted P C.X C.Y C.T)

end Agave.Ed25519.DoubleBase.RIR
