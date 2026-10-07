import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Prefix

/-! The exact inherited register reads used by the normalization slice.
An opaque entry environment avoids repeatedly expanding all preceding writes. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR

structure NormalizationInputs (E : Env program.Γ) (temp : Pointer) : Prop where
  read2 : E.read (%2) = .value 40#64
  read4 : E.read (%4) = .value 48#64
  read5 : E.read (%5) = .value 56#64
  read6 : E.read (%6) = .value 64#64
  read7 : E.read (%7) = .value 72#64
  read8 : E.read (%8) = .value 51#64
  read9 : E.read (%9) = .value 2251799813685247#64
  read10 : E.read (%10) = .value 19#64
  read11 : E.read (%11) = .value 8#64
  read12 : E.read (%12) = .value 16#64
  read13 : E.read (%13) = .value 24#64
  read14 : E.read (%14) = .value 32#64
  read15 : E.read (%15) = .value 7#64
  read16 : E.read (%16) = .value 3#64
  read17 : E.read (%17) = .value 5#64
  read18 : E.read (%18) = .value 13#64
  read19 : E.read (%19) = .value 21#64
  read20 : E.read (%20) = .value 29#64
  read21 : E.read (%21) = .value 37#64
  read22 : E.read (%22) = .value 45#64
  read23 : E.read (%23) = .value 6#64
  read24 : E.read (%24) = .value 2#64
  read25 : E.read (%25) = .value 10#64
  read26 : E.read (%26) = .value 18#64
  read27 : E.read (%27) = .value 26#64
  read28 : E.read (%28) = .value 34#64
  read29 : E.read (%29) = .value 42#64
  read30 : E.read (%30) = .value 50#64
  read31 : E.read (%31) = .value 1#64
  read32 : E.read (%32) = .value 15#64
  read33 : E.read (%33) = .value 23#64
  read34 : E.read (%34) = .value 31#64
  read35 : E.read (%35) = .value 39#64
  read36 : E.read (%36) = .value 47#64
  read37 : E.read (%37) = .value 4#64
  read38 : E.read (%38) = .value 12#64
  read39 : E.read (%39) = .value 20#64
  read40 : E.read (%40) = .value 28#64
  read41 : E.read (%41) = .value 36#64
  read42 : E.read (%42) = .value 44#64
  read43 : E.read (%43) = .value 1#8
  read58 : E.read (%58) = .value temp
  read62 : E.read (%62) = .value (temp.add 40)

set_option maxHeartbeats 1000000 in
theorem affineEnv_normalizationInputs (E : Env program.Γ) (initial : GlobalState)
    (input : Pointer) :
    NormalizationInputs (affineEnv E initial input) (scratch initial 5) := by
  constructor <;>
    simp [affineEnv, allocatedEnv, constantEnv, mlir_env]

end Agave.Ed25519.Encoding.Compress.Execution
