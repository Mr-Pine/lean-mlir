import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Program
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Memory
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def storeBlock0 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 470).take 15}

def chunkEnv0 (E : Env program.Γ) (out : Pointer) : Env program.Γ :=
  E[%416 := .value (out.add 1#64)][%417 := .value (out.add 2#64)][%418 := .value (out.add 3#64)][%419 := .value (out.add 4#64)][%420 := .value (out.add 5#64)][%421 := .value (out.add 6#64)][%422 := .value (out.add 7#64)]

def chunkMemory0 (m : MemoryState) (out : Pointer) (bytes : Bytes) : MemoryState :=
  ((((((((m).storeAt out (bytes 0)).storeAt (out.add 1#64) (bytes 1)).storeAt (out.add 2#64) (bytes 2)).storeAt (out.add 3#64) (bytes 3)).storeAt (out.add 4#64) (bytes 4)).storeAt (out.add 5#64) (bytes 5)).storeAt (out.add 6#64) (bytes 6)).storeAt (out.add 7#64) (bytes 7)

theorem store_chunk0 (E : Env program.Γ) (out : Pointer) (bytes : Bytes)
    (s : GlobalState) (hr : SmallRange s.mem out 32)
    (hout : E.read (%arg0) = .value out)
    (hb0 : E.read (%351) = .value (bytes 0))
    (hb1 : E.read (%353) = .value (bytes 1))
    (hk1 : E.read (%47) = .value 1#64)
    (hb2 : E.read (%355) = .value (bytes 2))
    (hk2 : E.read (%48) = .value 2#64)
    (hb3 : E.read (%357) = .value (bytes 3))
    (hk3 : E.read (%49) = .value 3#64)
    (hb4 : E.read (%359) = .value (bytes 4))
    (hk4 : E.read (%1) = .value 4#64)
    (hb5 : E.read (%361) = .value (bytes 5))
    (hk5 : E.read (%3) = .value 5#64)
    (hb6 : E.read (%365) = .value (bytes 6))
    (hk6 : E.read (%5) = .value 6#64)
    (hb7 : E.read (%367) = .value (bytes 7))
    (hk7 : E.read (%7) = .value 7#64)
    : storeBlock0.runBodyFrom E 0 s =
      .value (chunkEnv0 E out, {s with mem := chunkMemory0 s.mem out bytes}) := by
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      storeBlock0.runBodyFrom E' 0 S =
        .value (chunkEnv0 E out, {s with mem := chunkMemory0 s.mem out bytes}) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hEargs : E'.args = E.args := by rw [hE]
  have hrS : SmallRange S.mem out 32 := by rw [hS]; exact hr
  have hf0 := hrS.fits_add (k := 0) (count := 1) (by decide)
  have hf1 := hrS.fits_add (k := 1) (count := 1) (by decide)
  have hf2 := hrS.fits_add (k := 2) (count := 1) (by decide)
  have hf3 := hrS.fits_add (k := 3) (count := 1) (by decide)
  have hf4 := hrS.fits_add (k := 4) (count := 1) (by decide)
  have hf5 := hrS.fits_add (k := 5) (count := 1) (by decide)
  have hf6 := hrS.fits_add (k := 6) (count := 1) (by decide)
  have hf7 := hrS.fits_add (k := 7) (count := 1) (by decide)
  simp only [Pointer.add_zero] at hf0
  change E.args 0 = .value out at hout
  step_store [hout, hb0]
  have hgep := hrS.gep (k := 1) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk1]
  clear hgep
  step_store [hout, hb1]
  have hgep := hrS.gep (k := 2) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk2]
  clear hgep
  step_store [hout, hb2]
  have hgep := hrS.gep (k := 3) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk3]
  clear hgep
  step_store [hout, hb3]
  have hgep := hrS.gep (k := 4) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk4]
  clear hgep
  step_store [hout, hb4]
  have hgep := hrS.gep (k := 5) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk5]
  clear hgep
  step_store [hout, hb5]
  have hgep := hrS.gep (k := 6) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk6]
  clear hgep
  step_store [hout, hb6]
  have hgep := hrS.gep (k := 7) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk7]
  clear hgep
  step_store [hout, hb7]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
