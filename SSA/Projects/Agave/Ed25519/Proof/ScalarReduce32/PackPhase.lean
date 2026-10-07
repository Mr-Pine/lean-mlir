import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Pack

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR

structure PackReady (E : Env program.Γ) (x0 x1 x2 x3 x4 : BitVec 64) : Prop where
  h331 : E.read (%331) = .value x0
  h332 : E.read (%332) = .value (x0 &&& 4503599627370495#64)
  h336 : E.read (%336) = .value x1
  h337 : E.read (%337) = .value (x1 &&& 4503599627370495#64)
  h341 : E.read (%341) = .value x2
  h342 : E.read (%342) = .value (x2 &&& 4503599627370495#64)
  h344 : E.read (%344) = .value x3
  h349 : E.read (%349) = .value x4
  hk1 : E.read (%1) = .value 4#64
  hk2 : E.read (%2) = .value 32#64
  hk4 : E.read (%4) = .value 40#64
  hk6 : E.read (%6) = .value 48#64
  hk9 : E.read (%9) = .value 8#64
  hk10 : E.read (%10) = .value 12#64
  hk13 : E.read (%13) = .value 16#64
  hk16 : E.read (%16) = .value 24#64
  hk17 : E.read (%17) = .value 20#64
  hk22 : E.read (%22) = .value 36#64
  hk45 : E.read (%45) = .value 28#64
  hk46 : E.read (%46) = .value 44#64
  hbound : x3.toNat < 2 ^ 53

theorem pack_phase (E : Env program.Γ) (s : GlobalState) (x0 x1 x2 x3 x4 : BitVec 64)
    (hr : PackReady E x0 x1 x2 x3 x4) :
    List.foldlM Instr.run E pack s = .value (packedEnv E x0 x1 x2 x3 x4, s) := by
  exact pack_body E x0 x1 x2 x3 x4 s
    hr.h331 hr.h332 hr.h336 hr.h337 hr.h341 hr.h342 hr.h344 hr.h349 hr.hk1 hr.hk2 hr.hk4 hr.hk6 hr.hk9 hr.hk10 hr.hk13 hr.hk16 hr.hk17 hr.hk22 hr.hk45 hr.hk46 hr.hbound

end Agave.Ed25519.ScalarReduce32.Execution
