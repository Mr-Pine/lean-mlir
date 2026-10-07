import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Product

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

structure ProductReady (E : Env program.Γ) (x : Fin 5 → BitVec 64)
    (scratch : Fin 9 → Pointer) : Prop where
  x0 : E.read (%176) = .value (x 0)
  x1 : E.read (%175) = .value (x 1)
  x2 : E.read (%174) = .value (x 2)
  x3 : E.read (%172) = .value (x 3)
  x4 : E.read (%171) = .value (x 4)
  p0 : E.read (%81) = .value (scratch 0)
  p1 : E.read (%82) = .value (scratch 1)
  p2 : E.read (%83) = .value (scratch 2)
  p3 : E.read (%84) = .value (scratch 3)
  p4 : E.read (%85) = .value (scratch 4)
  p5 : E.read (%86) = .value (scratch 5)
  p6 : E.read (%87) = .value (scratch 6)
  p7 : E.read (%88) = .value (scratch 7)
  p8 : E.read (%89) = .value (scratch 8)
  c24 : E.read (%24) = .value 4302102966953709#128
  c25 : E.read (%25) = .value 1049714374468698#128
  c26 : E.read (%26) = .value 4503599278581019#128
  c27 : E.read (%27) = .value 4503599627370495#128
  c28 : E.read (%28) = .value 17592186044415#128

def productPhaseEnv (E : Env program.Γ) (x : Fin 5 → BitVec 64) : Env program.Γ :=
  let E0 := E
  let E1 := productEnv0 E0 (x 0) (x 1) (x 2) (x 3) (x 4)
  let E2 := productEnv1 E1 (x 0) (x 1) (x 2) (x 3) (x 4)
  let E3 := productEnv2 E2 (x 0) (x 1) (x 2) (x 3) (x 4)
  let E4 := productEnv3 E3 (x 0) (x 1) (x 2) (x 3) (x 4)
  let E5 := productEnv4 E4 (x 0) (x 1) (x 2) (x 3) (x 4)
  let E6 := productEnv5 E5 (x 0) (x 1) (x 2) (x 3) (x 4)
  let E7 := productEnv6 E6 (x 0) (x 1) (x 2) (x 3) (x 4)
  let E8 := productEnv7 E7 (x 0) (x 1) (x 2) (x 3) (x 4)
  let E9 := productEnv8 E8 (x 0) (x 1) (x 2) (x 3) (x 4)
  E9

def productPhaseState (s : GlobalState) (x : Fin 5 → BitVec 64)
    (scratch : Fin 9 → Pointer) : GlobalState :=
  let m0 := s.mem
  let m1 := m0.storeAt (scratch 0) (productWord0 (x 0) (x 1) (x 2) (x 3) (x 4))
  let m2 := m1.storeAt (scratch 1) (productWord1 (x 0) (x 1) (x 2) (x 3) (x 4))
  let m3 := m2.storeAt (scratch 2) (productWord2 (x 0) (x 1) (x 2) (x 3) (x 4))
  let m4 := m3.storeAt (scratch 3) (productWord3 (x 0) (x 1) (x 2) (x 3) (x 4))
  let m5 := m4.storeAt (scratch 4) (productWord4 (x 0) (x 1) (x 2) (x 3) (x 4))
  let m6 := m5.storeAt (scratch 5) (productWord5 (x 0) (x 1) (x 2) (x 3) (x 4))
  let m7 := m6.storeAt (scratch 6) (productWord6 (x 0) (x 1) (x 2) (x 3) (x 4))
  let m8 := m7.storeAt (scratch 7) (productWord7 (x 0) (x 1) (x 2) (x 3) (x 4))
  let m9 := m8.storeAt (scratch 8) (productWord8 (x 0) (x 1) (x 2) (x 3) (x 4))
  {s with mem := m9}

/-- The complete 69-instruction multiplication phase, from operand and
private-pointer invariants, including all source stores and flags. -/
theorem product_phase (E : Env program.Γ) (s : GlobalState)
    (x : Fin 5 → BitVec 64) (scratch : Fin 9 → Pointer)
    (hr : ProductReady E x scratch) (hx : ∀ i, (x i).toNat < 2 ^ 52)
    (hfit : ∀ i, SmallRange s.mem (scratch i) 16) :
    List.foldlM Instr.run E multiplication s =
      .value (productPhaseEnv E x, productPhaseState s x scratch) := by
  let E0 := E
  let s0 := s
  let E1 := productEnv0 E0 (x 0) (x 1) (x 2) (x 3) (x 4)
  let s1 : GlobalState := {s0 with mem := s0.mem.storeAt (scratch 0) (productWord0 (x 0) (x 1) (x 2) (x 3) (x 4))}
  have hf0 : SmallRange s0.mem (scratch 0) 16 := by
    exact hfit 0
  have h0 := product_chunk0 E0 s0 (x 0) (x 1) (x 2) (x 3) (x 4) (scratch 0)
    (hx 0) (hx 1) (hx 2) (hx 3) (hx 4) hf0
    (by simpa [E0, mlir_env] using hr.p0)
    (by simpa [E0, mlir_env] using hr.x0)
    (by simpa [E0, mlir_env] using hr.c24)
  change List.foldlM Instr.run E0 productBlock0.body s0 = .value (E1, s1) at h0
  let E2 := productEnv1 E1 (x 0) (x 1) (x 2) (x 3) (x 4)
  let s2 : GlobalState := {s1 with mem := s1.mem.storeAt (scratch 1) (productWord1 (x 0) (x 1) (x 2) (x 3) (x 4))}
  have hf1 : SmallRange s1.mem (scratch 1) 16 := by
    dsimp only [s1, s0]
    repeat' apply SmallRange.storeAt
    exact hfit 1
  have h1 := product_chunk1 E1 s1 (x 0) (x 1) (x 2) (x 3) (x 4) (scratch 1)
    (hx 0) (hx 1) (hx 2) (hx 3) (hx 4) hf1
    (by simpa [E0, E1, productEnv0, mlir_env] using hr.p1)
    (by simpa [E0, E1, productEnv0, mlir_env] using hr.x1)
    (by simp [E0, E1, productEnv0, mlir_env])
    (by simpa [E0, E1, productEnv0, mlir_env] using hr.c24)
    (by simpa [E0, E1, productEnv0, mlir_env] using hr.c25)
  change List.foldlM Instr.run E1 productBlock1.body s1 = .value (E2, s2) at h1
  let E3 := productEnv2 E2 (x 0) (x 1) (x 2) (x 3) (x 4)
  let s3 : GlobalState := {s2 with mem := s2.mem.storeAt (scratch 2) (productWord2 (x 0) (x 1) (x 2) (x 3) (x 4))}
  have hf2 : SmallRange s2.mem (scratch 2) 16 := by
    dsimp only [s2, s1, s0]
    repeat' apply SmallRange.storeAt
    exact hfit 2
  have h2 := product_chunk2 E2 s2 (x 0) (x 1) (x 2) (x 3) (x 4) (scratch 2)
    (hx 0) (hx 1) (hx 2) (hx 3) (hx 4) hf2
    (by simpa [E0, E1, productEnv0, E2, productEnv1, mlir_env] using hr.p2)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, mlir_env] using hr.x2)
    (by simp [E0, E1, productEnv0, E2, productEnv1, mlir_env])
    (by simp [E0, E1, productEnv0, E2, productEnv1, mlir_env])
    (by simpa [E0, E1, productEnv0, E2, productEnv1, mlir_env] using hr.c24)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, mlir_env] using hr.c25)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, mlir_env] using hr.c26)
  change List.foldlM Instr.run E2 productBlock2.body s2 = .value (E3, s3) at h2
  let E4 := productEnv3 E3 (x 0) (x 1) (x 2) (x 3) (x 4)
  let s4 : GlobalState := {s3 with mem := s3.mem.storeAt (scratch 3) (productWord3 (x 0) (x 1) (x 2) (x 3) (x 4))}
  have hf3 : SmallRange s3.mem (scratch 3) 16 := by
    dsimp only [s3, s2, s1, s0]
    repeat' apply SmallRange.storeAt
    exact hfit 3
  have h3 := product_chunk3 E3 s3 (x 0) (x 1) (x 2) (x 3) (x 4) (scratch 3)
    (hx 0) (hx 1) (hx 2) (hx 3) (hx 4) hf3
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, mlir_env] using hr.p3)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, mlir_env] using hr.x3)
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, mlir_env])
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, mlir_env])
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, mlir_env])
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, mlir_env] using hr.c24)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, mlir_env] using hr.c25)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, mlir_env] using hr.c26)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, mlir_env] using hr.c27)
  change List.foldlM Instr.run E3 productBlock3.body s3 = .value (E4, s4) at h3
  let E5 := productEnv4 E4 (x 0) (x 1) (x 2) (x 3) (x 4)
  let s5 : GlobalState := {s4 with mem := s4.mem.storeAt (scratch 4) (productWord4 (x 0) (x 1) (x 2) (x 3) (x 4))}
  have hf4 : SmallRange s4.mem (scratch 4) 16 := by
    dsimp only [s4, s3, s2, s1, s0]
    repeat' apply SmallRange.storeAt
    exact hfit 4
  have h4 := product_chunk4 E4 s4 (x 0) (x 1) (x 2) (x 3) (x 4) (scratch 4)
    (hx 0) (hx 1) (hx 2) (hx 3) (hx 4) hf4
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, mlir_env] using hr.p4)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, mlir_env] using hr.x4)
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, mlir_env])
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, mlir_env])
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, mlir_env])
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, mlir_env])
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, mlir_env] using hr.c24)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, mlir_env] using hr.c25)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, mlir_env] using hr.c26)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, mlir_env] using hr.c27)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, mlir_env] using hr.c28)
  change List.foldlM Instr.run E4 productBlock4.body s4 = .value (E5, s5) at h4
  let E6 := productEnv5 E5 (x 0) (x 1) (x 2) (x 3) (x 4)
  let s6 : GlobalState := {s5 with mem := s5.mem.storeAt (scratch 5) (productWord5 (x 0) (x 1) (x 2) (x 3) (x 4))}
  have hf5 : SmallRange s5.mem (scratch 5) 16 := by
    dsimp only [s5, s4, s3, s2, s1, s0]
    repeat' apply SmallRange.storeAt
    exact hfit 5
  have h5 := product_chunk5 E5 s5 (x 0) (x 1) (x 2) (x 3) (x 4) (scratch 5)
    (hx 0) (hx 1) (hx 2) (hx 3) (hx 4) hf5
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, mlir_env] using hr.p5)
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, mlir_env])
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, mlir_env])
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, mlir_env])
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, mlir_env])
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, mlir_env] using hr.c25)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, mlir_env] using hr.c26)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, mlir_env] using hr.c27)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, mlir_env] using hr.c28)
  change List.foldlM Instr.run E5 productBlock5.body s5 = .value (E6, s6) at h5
  let E7 := productEnv6 E6 (x 0) (x 1) (x 2) (x 3) (x 4)
  let s7 : GlobalState := {s6 with mem := s6.mem.storeAt (scratch 6) (productWord6 (x 0) (x 1) (x 2) (x 3) (x 4))}
  have hf6 : SmallRange s6.mem (scratch 6) 16 := by
    dsimp only [s6, s5, s4, s3, s2, s1, s0]
    repeat' apply SmallRange.storeAt
    exact hfit 6
  have h6 := product_chunk6 E6 s6 (x 0) (x 1) (x 2) (x 3) (x 4) (scratch 6)
    (hx 0) (hx 1) (hx 2) (hx 3) (hx 4) hf6
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, E6, productEnv5, mlir_env] using hr.p6)
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, E6, productEnv5, mlir_env])
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, E6, productEnv5, mlir_env])
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, E6, productEnv5, mlir_env])
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, E6, productEnv5, mlir_env] using hr.c26)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, E6, productEnv5, mlir_env] using hr.c27)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, E6, productEnv5, mlir_env] using hr.c28)
  change List.foldlM Instr.run E6 productBlock6.body s6 = .value (E7, s7) at h6
  let E8 := productEnv7 E7 (x 0) (x 1) (x 2) (x 3) (x 4)
  let s8 : GlobalState := {s7 with mem := s7.mem.storeAt (scratch 7) (productWord7 (x 0) (x 1) (x 2) (x 3) (x 4))}
  have hf7 : SmallRange s7.mem (scratch 7) 16 := by
    dsimp only [s7, s6, s5, s4, s3, s2, s1, s0]
    repeat' apply SmallRange.storeAt
    exact hfit 7
  have h7 := product_chunk7 E7 s7 (x 0) (x 1) (x 2) (x 3) (x 4) (scratch 7)
    (hx 0) (hx 1) (hx 2) (hx 3) (hx 4) hf7
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, E6, productEnv5, E7, productEnv6, mlir_env] using hr.p7)
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, E6, productEnv5, E7, productEnv6, mlir_env])
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, E6, productEnv5, E7, productEnv6, mlir_env])
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, E6, productEnv5, E7, productEnv6, mlir_env] using hr.c27)
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, E6, productEnv5, E7, productEnv6, mlir_env] using hr.c28)
  change List.foldlM Instr.run E7 productBlock7.body s7 = .value (E8, s8) at h7
  let E9 := productEnv8 E8 (x 0) (x 1) (x 2) (x 3) (x 4)
  let s9 : GlobalState := {s8 with mem := s8.mem.storeAt (scratch 8) (productWord8 (x 0) (x 1) (x 2) (x 3) (x 4))}
  have hf8 : SmallRange s8.mem (scratch 8) 16 := by
    dsimp only [s8, s7, s6, s5, s4, s3, s2, s1, s0]
    repeat' apply SmallRange.storeAt
    exact hfit 8
  have h8 := product_chunk8 E8 s8 (x 0) (x 1) (x 2) (x 3) (x 4) (scratch 8)
    (hx 0) (hx 1) (hx 2) (hx 3) (hx 4) hf8
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, E6, productEnv5, E7, productEnv6, E8, productEnv7, mlir_env] using hr.p8)
    (by simp [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, E6, productEnv5, E7, productEnv6, E8, productEnv7, mlir_env])
    (by simpa [E0, E1, productEnv0, E2, productEnv1, E3, productEnv2, E4, productEnv3, E5, productEnv4, E6, productEnv5, E7, productEnv6, E8, productEnv7, mlir_env] using hr.c28)
  change List.foldlM Instr.run E8 productBlock8.body s8 = .value (E9, s9) at h8
  have hf : List.foldlM Instr.run E0 multiplication s0 = .value (E9, s9) := by
    rw [product_body_decomposition]
    simp only [List.foldlM_append, EffectM.bind_eq, product_prefix,
      h0, h1, h2, h3, h4, h5, h6, h7, h8, product_suffix, PoisonOr.value_bind]
  exact hf

end Agave.Ed25519.ScalarReduce32.Execution
