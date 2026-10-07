import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.StoreChunk2

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def storeBlock3 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 517).take 16}

def chunkEnv3 (E : Env program.Γ) (out : Pointer) : Env program.Γ :=
  E[%439 := .value (out.add 24#64)][%440 := .value (out.add 25#64)][%441 := .value (out.add 26#64)][%442 := .value (out.add 27#64)][%443 := .value (out.add 28#64)][%444 := .value (out.add 29#64)][%445 := .value (out.add 30#64)][%446 := .value (out.add 31#64)]

def chunkMemory3 (m : MemoryState) (out : Pointer) (bytes : Bytes) : MemoryState :=
  ((((((((m).storeAt (out.add 24#64) (bytes 24)).storeAt (out.add 25#64) (bytes 25)).storeAt (out.add 26#64) (bytes 26)).storeAt (out.add 27#64) (bytes 27)).storeAt (out.add 28#64) (bytes 28)).storeAt (out.add 29#64) (bytes 29)).storeAt (out.add 30#64) (bytes 30)).storeAt (out.add 31#64) (bytes 31)

theorem store_chunk3 (E : Env program.Γ) (out : Pointer) (bytes : Bytes)
    (s : GlobalState) (hr : SmallRange s.mem out 32)
    (hout : E.read (%arg0) = .value out)
    (hb24 : E.read (%402) = .value (bytes 24))
    (hk24 : E.read (%16) = .value 24#64)
    (hb25 : E.read (%404) = .value (bytes 25))
    (hk25 : E.read (%18) = .value 25#64)
    (hb26 : E.read (%405) = .value (bytes 26))
    (hk26 : E.read (%19) = .value 26#64)
    (hb27 : E.read (%407) = .value (bytes 27))
    (hk27 : E.read (%58) = .value 27#64)
    (hb28 : E.read (%409) = .value (bytes 28))
    (hk28 : E.read (%45) = .value 28#64)
    (hb29 : E.read (%411) = .value (bytes 29))
    (hk29 : E.read (%59) = .value 29#64)
    (hb30 : E.read (%413) = .value (bytes 30))
    (hk30 : E.read (%20) = .value 30#64)
    (hb31 : E.read (%415) = .value (bytes 31))
    (hk31 : E.read (%60) = .value 31#64)
    : storeBlock3.runBodyFrom E 0 s =
      .value (chunkEnv3 E out, {s with mem := chunkMemory3 s.mem out bytes}) := by
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      storeBlock3.runBodyFrom E' 0 S =
        .value (chunkEnv3 E out, {s with mem := chunkMemory3 s.mem out bytes}) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hEargs : E'.args = E.args := by rw [hE]
  have hrS : SmallRange S.mem out 32 := by rw [hS]; exact hr
  have hf24 := hrS.fits_add (k := 24) (count := 1) (by decide)
  have hf25 := hrS.fits_add (k := 25) (count := 1) (by decide)
  have hf26 := hrS.fits_add (k := 26) (count := 1) (by decide)
  have hf27 := hrS.fits_add (k := 27) (count := 1) (by decide)
  have hf28 := hrS.fits_add (k := 28) (count := 1) (by decide)
  have hf29 := hrS.fits_add (k := 29) (count := 1) (by decide)
  have hf30 := hrS.fits_add (k := 30) (count := 1) (by decide)
  have hf31 := hrS.fits_add (k := 31) (count := 1) (by decide)
  change E.args 0 = .value out at hout
  have hgep := hrS.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk24]
  clear hgep
  step_store [hout, hb24]
  have hgep := hrS.gep (k := 25) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk25]
  clear hgep
  step_store [hout, hb25]
  have hgep := hrS.gep (k := 26) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk26]
  clear hgep
  step_store [hout, hb26]
  have hgep := hrS.gep (k := 27) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk27]
  clear hgep
  step_store [hout, hb27]
  have hgep := hrS.gep (k := 28) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk28]
  clear hgep
  step_store [hout, hb28]
  have hgep := hrS.gep (k := 29) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk29]
  clear hgep
  step_store [hout, hb29]
  have hgep := hrS.gep (k := 30) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk30]
  clear hgep
  step_store [hout, hb30]
  have hgep := hrS.gep (k := 31) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk31]
  clear hgep
  step_store [hout, hb31]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
