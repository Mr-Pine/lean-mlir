import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.StoreChunk0

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def storeBlock1 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 485).take 16}

def chunkEnv1 (E : Env program.Γ) (out : Pointer) : Env program.Γ :=
  E[%423 := .value (out.add 8#64)][%424 := .value (out.add 9#64)][%425 := .value (out.add 10#64)][%426 := .value (out.add 11#64)][%427 := .value (out.add 12#64)][%428 := .value (out.add 13#64)][%429 := .value (out.add 14#64)][%430 := .value (out.add 15#64)]

def chunkMemory1 (m : MemoryState) (out : Pointer) (bytes : Bytes) : MemoryState :=
  ((((((((m).storeAt (out.add 8#64) (bytes 8)).storeAt (out.add 9#64) (bytes 9)).storeAt (out.add 10#64) (bytes 10)).storeAt (out.add 11#64) (bytes 11)).storeAt (out.add 12#64) (bytes 12)).storeAt (out.add 13#64) (bytes 13)).storeAt (out.add 14#64) (bytes 14)).storeAt (out.add 15#64) (bytes 15)

theorem store_chunk1 (E : Env program.Γ) (out : Pointer) (bytes : Bytes)
    (s : GlobalState) (hr : SmallRange s.mem out 32)
    (hout : E.read (%arg0) = .value out)
    (hb8 : E.read (%369) = .value (bytes 8))
    (hk8 : E.read (%9) = .value 8#64)
    (hb9 : E.read (%371) = .value (bytes 9))
    (hk9 : E.read (%50) = .value 9#64)
    (hb10 : E.read (%373) = .value (bytes 10))
    (hk10 : E.read (%51) = .value 10#64)
    (hb11 : E.read (%375) = .value (bytes 11))
    (hk11 : E.read (%52) = .value 11#64)
    (hb12 : E.read (%377) = .value (bytes 12))
    (hk12 : E.read (%10) = .value 12#64)
    (hb13 : E.read (%378) = .value (bytes 13))
    (hk13 : E.read (%11) = .value 13#64)
    (hb14 : E.read (%380) = .value (bytes 14))
    (hk14 : E.read (%12) = .value 14#64)
    (hb15 : E.read (%382) = .value (bytes 15))
    (hk15 : E.read (%53) = .value 15#64)
    : storeBlock1.runBodyFrom E 0 s =
      .value (chunkEnv1 E out, {s with mem := chunkMemory1 s.mem out bytes}) := by
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      storeBlock1.runBodyFrom E' 0 S =
        .value (chunkEnv1 E out, {s with mem := chunkMemory1 s.mem out bytes}) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hEargs : E'.args = E.args := by rw [hE]
  have hrS : SmallRange S.mem out 32 := by rw [hS]; exact hr
  have hf8 := hrS.fits_add (k := 8) (count := 1) (by decide)
  have hf9 := hrS.fits_add (k := 9) (count := 1) (by decide)
  have hf10 := hrS.fits_add (k := 10) (count := 1) (by decide)
  have hf11 := hrS.fits_add (k := 11) (count := 1) (by decide)
  have hf12 := hrS.fits_add (k := 12) (count := 1) (by decide)
  have hf13 := hrS.fits_add (k := 13) (count := 1) (by decide)
  have hf14 := hrS.fits_add (k := 14) (count := 1) (by decide)
  have hf15 := hrS.fits_add (k := 15) (count := 1) (by decide)
  change E.args 0 = .value out at hout
  have hgep := hrS.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk8]
  clear hgep
  step_store [hout, hb8]
  have hgep := hrS.gep (k := 9) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk9]
  clear hgep
  step_store [hout, hb9]
  have hgep := hrS.gep (k := 10) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk10]
  clear hgep
  step_store [hout, hb10]
  have hgep := hrS.gep (k := 11) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk11]
  clear hgep
  step_store [hout, hb11]
  have hgep := hrS.gep (k := 12) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk12]
  clear hgep
  step_store [hout, hb12]
  have hgep := hrS.gep (k := 13) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk13]
  clear hgep
  step_store [hout, hb13]
  have hgep := hrS.gep (k := 14) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk14]
  clear hgep
  step_store [hout, hb14]
  have hgep := hrS.gep (k := 15) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk15]
  clear hgep
  step_store [hout, hb15]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
