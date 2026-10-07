import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackChunk0
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackChunk1
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackChunk2
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackChunk3
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackChunk4
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Phases

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def packedEnv (E : Env program.Γ) (x0 x1 x2 x3 x4 : BitVec 64) : Env program.Γ :=
  packEnv4 (packEnv3 (packEnv2 (packEnv1 (packEnv0 E x0) x0 x1) x2) x2 x3) x4

theorem pack_body_decomposition : pack =
    packBlock0.body ++ packBlock1.body ++ packBlock2.body ++
      packBlock3.body ++ packBlock4.body := rfl

/-- The packer executes under its actual register equations. Only the unmasked
fourth carry word needs a magnitude bound; all masked-input flags are proved. -/
theorem pack_body (E : Env program.Γ) (x0 x1 x2 x3 x4 : BitVec 64)
    (s : GlobalState)
    (h331 : E.read (%331) = .value x0)
    (h332 : E.read (%332) = .value (x0 &&& 4503599627370495#64))
    (h336 : E.read (%336) = .value x1)
    (h337 : E.read (%337) = .value (x1 &&& 4503599627370495#64))
    (h341 : E.read (%341) = .value x2)
    (h342 : E.read (%342) = .value (x2 &&& 4503599627370495#64))
    (h344 : E.read (%344) = .value x3)
    (h349 : E.read (%349) = .value x4)
    (hk1 : E.read (%1) = .value 4#64)
    (hk2 : E.read (%2) = .value 32#64)
    (hk4 : E.read (%4) = .value 40#64)
    (hk6 : E.read (%6) = .value 48#64)
    (hk9 : E.read (%9) = .value 8#64)
    (hk10 : E.read (%10) = .value 12#64)
    (hk13 : E.read (%13) = .value 16#64)
    (hk16 : E.read (%16) = .value 24#64)
    (hk17 : E.read (%17) = .value 20#64)
    (hk22 : E.read (%22) = .value 36#64)
    (hk45 : E.read (%45) = .value 28#64)
    (hk46 : E.read (%46) = .value 44#64)
    (hbound : x3.toNat < 2 ^ 53) :
    List.foldlM Instr.run E pack s = .value (packedEnv E x0 x1 x2 x3 x4, s) := by
  let E0 := E
  let E1 := packEnv0 E0 x0
  have h0 := pack_chunk0 E0 x0 s
    (by simpa [E0, mlir_env] using h331)
    (by simpa [E0, mlir_env] using hk2)
    (by simpa [E0, mlir_env] using hk4)
    (by simpa [E0, mlir_env] using hk9)
    (by simpa [E0, mlir_env] using hk13)
    (by simpa [E0, mlir_env] using hk16)
  change List.foldlM Instr.run E0 packBlock0.body s = .value (E1, s) at h0
  let E2 := packEnv1 E1 x0 x1
  have h1 := pack_chunk1 E1 x0 x1 s
    (by simpa [E0, E1, packEnv0, mlir_env] using h332)
    (by simpa [E0, E1, packEnv0, mlir_env] using h336)
    (by simpa [E0, E1, packEnv0, mlir_env] using h337)
    (by simpa [E0, E1, packEnv0, mlir_env] using hk1)
    (by simpa [E0, E1, packEnv0, mlir_env] using hk6)
    (by simpa [E0, E1, packEnv0, mlir_env] using hk10)
    (by simpa [E0, E1, packEnv0, mlir_env] using hk17)
    (by simpa [E0, E1, packEnv0, mlir_env] using hk22)
    (by simpa [E0, E1, packEnv0, mlir_env] using hk45)
    (by simpa [E0, E1, packEnv0, mlir_env] using hk46)
  change List.foldlM Instr.run E1 packBlock1.body s = .value (E2, s) at h1
  let E3 := packEnv2 E2 x2
  have h2 := pack_chunk2 E2 x2 s
    (by simpa [E0, E1, packEnv0, E2, packEnv1, mlir_env] using h341)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, mlir_env] using hk2)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, mlir_env] using hk4)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, mlir_env] using hk9)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, mlir_env] using hk13)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, mlir_env] using hk16)
  change List.foldlM Instr.run E2 packBlock2.body s = .value (E3, s) at h2
  let E4 := packEnv3 E3 x2 x3
  have h3 := pack_chunk3 E3 x2 x3 s
    (by simpa [E0, E1, packEnv0, E2, packEnv1, E3, packEnv2, mlir_env] using h342)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, E3, packEnv2, mlir_env] using h344)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, E3, packEnv2, mlir_env] using hk1)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, E3, packEnv2, mlir_env] using hk6)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, E3, packEnv2, mlir_env] using hk10)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, E3, packEnv2, mlir_env] using hk17)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, E3, packEnv2, mlir_env] using hk22)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, E3, packEnv2, mlir_env] using hk45)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, E3, packEnv2, mlir_env] using hk46)
    hbound
  change List.foldlM Instr.run E3 packBlock3.body s = .value (E4, s) at h3
  let E5 := packEnv4 E4 x4
  have h4 := pack_chunk4 E4 x4 s
    (by simpa [E0, E1, packEnv0, E2, packEnv1, E3, packEnv2, E4, packEnv3, mlir_env] using h349)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, E3, packEnv2, E4, packEnv3, mlir_env] using hk2)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, E3, packEnv2, E4, packEnv3, mlir_env] using hk4)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, E3, packEnv2, E4, packEnv3, mlir_env] using hk9)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, E3, packEnv2, E4, packEnv3, mlir_env] using hk13)
    (by simpa [E0, E1, packEnv0, E2, packEnv1, E3, packEnv2, E4, packEnv3, mlir_env] using hk16)
  change List.foldlM Instr.run E4 packBlock4.body s = .value (E5, s) at h4
  have hf : List.foldlM Instr.run E0 pack s = .value (E5, s) := by
    rw [pack_body_decomposition]
    simp only [List.foldlM_append, EffectM.bind_eq, h0, h1, h2, h3, h4,
      PoisonOr.value_bind]
  exact hf

end Agave.Ed25519.ScalarReduce32.Execution
