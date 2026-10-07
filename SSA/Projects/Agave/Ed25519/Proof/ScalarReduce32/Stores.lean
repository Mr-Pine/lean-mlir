import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.StoreChunk3
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Memory
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

/-! Execution of instructions 470–532 of the exact imported scalar reducer.
The slice retains its instructions, Γ, parameter map and original return.
Reaching this slice with the canonical bytes and then executing private
zeroization remains separate from this store-phase theorem. -/
namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def storeEnv (E : Env program.Γ) (bytes : Bytes) : Env program.Γ :=
  E[%47 := .value 1#64,
    %48 := .value 2#64,
    %49 := .value 3#64,
    %1 := .value 4#64,
    %3 := .value 5#64,
    %5 := .value 6#64,
    %7 := .value 7#64,
    %9 := .value 8#64,
    %50 := .value 9#64,
    %51 := .value 10#64,
    %52 := .value 11#64,
    %10 := .value 12#64,
    %11 := .value 13#64,
    %12 := .value 14#64,
    %53 := .value 15#64,
    %13 := .value 16#64,
    %54 := .value 17#64,
    %14 := .value 18#64,
    %15 := .value 19#64,
    %17 := .value 20#64,
    %55 := .value 21#64,
    %56 := .value 22#64,
    %57 := .value 23#64,
    %16 := .value 24#64,
    %18 := .value 25#64,
    %19 := .value 26#64,
    %58 := .value 27#64,
    %45 := .value 28#64,
    %59 := .value 29#64,
    %20 := .value 30#64,
    %60 := .value 31#64,
    %351 := .value (bytes 0),
    %353 := .value (bytes 1),
    %355 := .value (bytes 2),
    %357 := .value (bytes 3),
    %359 := .value (bytes 4),
    %361 := .value (bytes 5),
    %365 := .value (bytes 6),
    %367 := .value (bytes 7),
    %369 := .value (bytes 8),
    %371 := .value (bytes 9),
    %373 := .value (bytes 10),
    %375 := .value (bytes 11),
    %377 := .value (bytes 12),
    %378 := .value (bytes 13),
    %380 := .value (bytes 14),
    %382 := .value (bytes 15),
    %384 := .value (bytes 16),
    %386 := .value (bytes 17),
    %388 := .value (bytes 18),
    %392 := .value (bytes 19),
    %394 := .value (bytes 20),
    %396 := .value (bytes 21),
    %398 := .value (bytes 22),
    %400 := .value (bytes 23),
    %402 := .value (bytes 24),
    %404 := .value (bytes 25),
    %405 := .value (bytes 26),
    %407 := .value (bytes 27),
    %409 := .value (bytes 28),
    %411 := .value (bytes 29),
    %413 := .value (bytes 30),
    %415 := .value (bytes 31)]

/-- This is precisely the 32 output stores and their 31 address calculations. -/
@[reducible] def storeProgram : Func :=
  { program with blocks := fun _ =>
      { program.entry with body := (program.entry.body.drop 470).take 63 } }

theorem storeProgram_body :
    (storeProgram.blocks 0).body = (program.entry.body.drop 470).take 63 := rfl

def storeFinalEnv (E : Env program.Γ) (out : Pointer) : Env program.Γ :=
  chunkEnv3 (chunkEnv2 (chunkEnv1 (chunkEnv0 E out) out) out) out

theorem store_body_decomposition : (storeProgram.blocks 0).body =
    storeBlock0.body ++ storeBlock1.body ++ storeBlock2.body ++ storeBlock3.body := rfl

/-- The four independently checked exact chunks compose to the original store body. -/
theorem store_body (E : Env program.Γ) (out : Pointer) (bytes : Bytes)
    (s : GlobalState) (hr : SmallRange s.mem out 32)
    (hout : E.read (%arg0) = .value out) :
    List.foldlM Instr.run (storeEnv E bytes) (storeProgram.blocks 0).body s =
      .value (storeFinalEnv (storeEnv E bytes) out,
        {s with mem := storeBytes s.mem out bytes}) := by
  let E0 := storeEnv E bytes
  let s0 := s
  let E1 := chunkEnv0 E0 out
  let s1 : GlobalState := {s0 with mem := chunkMemory0 s0.mem out bytes}
  have hr0 : SmallRange s0.mem out 32 := by
    exact hr
  have h0 := store_chunk0 E0 out bytes s0 hr0
    (by simpa [E0, storeEnv, mlir_env] using hout)
    (by simp [E0, storeEnv, mlir_env])
    (by simp [E0, storeEnv, mlir_env])
    (by simp [E0, storeEnv, mlir_env])
    (by simp [E0, storeEnv, mlir_env])
    (by simp [E0, storeEnv, mlir_env])
    (by simp [E0, storeEnv, mlir_env])
    (by simp [E0, storeEnv, mlir_env])
    (by simp [E0, storeEnv, mlir_env])
    (by simp [E0, storeEnv, mlir_env])
    (by simp [E0, storeEnv, mlir_env])
    (by simp [E0, storeEnv, mlir_env])
    (by simp [E0, storeEnv, mlir_env])
    (by simp [E0, storeEnv, mlir_env])
    (by simp [E0, storeEnv, mlir_env])
    (by simp [E0, storeEnv, mlir_env])
  change List.foldlM Instr.run E0 storeBlock0.body s0 = .value (E1, s1) at h0
  let E2 := chunkEnv1 E1 out
  let s2 : GlobalState := {s1 with mem := chunkMemory1 s1.mem out bytes}
  have hr1 : SmallRange s1.mem out 32 := by
    change SmallRange (chunkMemory0 s0.mem out bytes) out 32
    unfold chunkMemory0
    repeat' apply SmallRange.storeAt
    exact hr
  have h1 := store_chunk1 E1 out bytes s1 hr1
    (by simpa [E0, storeEnv, E1, chunkEnv0, mlir_env] using hout)
    (by simp [E0, storeEnv, E1, chunkEnv0, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, mlir_env])
  change List.foldlM Instr.run E1 storeBlock1.body s1 = .value (E2, s2) at h1
  let E3 := chunkEnv2 E2 out
  let s3 : GlobalState := {s2 with mem := chunkMemory2 s2.mem out bytes}
  have hr2 : SmallRange s2.mem out 32 := by
    change SmallRange (chunkMemory1 s1.mem out bytes) out 32
    unfold chunkMemory1
    repeat' apply SmallRange.storeAt
    exact hr
  have h2 := store_chunk2 E2 out bytes s2 hr2
    (by simpa [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env] using hout)
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, mlir_env])
  change List.foldlM Instr.run E2 storeBlock2.body s2 = .value (E3, s3) at h2
  let E4 := chunkEnv3 E3 out
  let s4 : GlobalState := {s3 with mem := chunkMemory3 s3.mem out bytes}
  have hr3 : SmallRange s3.mem out 32 := by
    change SmallRange (chunkMemory2 s2.mem out bytes) out 32
    unfold chunkMemory2
    repeat' apply SmallRange.storeAt
    exact hr
  have h3 := store_chunk3 E3 out bytes s3 hr3
    (by simpa [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env] using hout)
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env])
    (by simp [E0, storeEnv, E1, chunkEnv0, E2, chunkEnv1, E3, chunkEnv2, mlir_env])
  change List.foldlM Instr.run E3 storeBlock3.body s3 = .value (E4, s4) at h3
  have hfold : List.foldlM Instr.run E0 (storeProgram.blocks 0).body s0 =
      .value (E4, s4) := by
    rw [store_body_decomposition]
    simp only [List.foldlM_append, EffectM.bind_eq, h0, h1, h2, h3, PoisonOr.value_bind]
  exact hfold

/-- Every emitted byte store executes from a live 32-byte destination. -/
theorem store_run (E : Env program.Γ) (out : Pointer) (bytes : Bytes)
    (s : GlobalState) (hr : SmallRange s.mem out 32)
    (hout : E.read (%arg0) = .value out) :
    storeProgram.runFrom (storeEnv E bytes) 0 s =
      .value (.nil, {s with mem := storeBytes s.mem out bytes}) := by
  have hb := store_body E out bytes s hr hout
  rw [Func.runFrom_eq]
  change (do
    let ((E', res), s') ← (storeProgram.blocks 0).run storeProgram.blockParams (storeEnv E bytes) s
    Func.continue (func := storeProgram) E' res s') = _
  simp only [BasicBlock.run, EffectM.bind_eq, hb, PoisonOr.value_bind]
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
