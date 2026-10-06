import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlaceData
namespace AgaveLatticeHash.MLIR.PortableInPlace
open LeanMLIR SLLVM PortableXof
set_option maxRecDepth 32768
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

theorem round_certificate : BlockPrefix.Renamed rename preRound.pre rounds.pre finalMap := by
  repeat first | apply BlockPrefix.Renamed.var | exact BlockPrefix.Renamed.nil _

end AgaveLatticeHash.MLIR.PortableInPlace
