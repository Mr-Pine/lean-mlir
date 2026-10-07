import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.StoreChunk1

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def storeBlock2 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 501).take 16}

def chunkEnv2 (E : Env program.Γ) (out : Pointer) : Env program.Γ :=
  E[%431 := .value (out.add 16#64)][%432 := .value (out.add 17#64)][%433 := .value (out.add 18#64)][%434 := .value (out.add 19#64)][%435 := .value (out.add 20#64)][%436 := .value (out.add 21#64)][%437 := .value (out.add 22#64)][%438 := .value (out.add 23#64)]

def chunkMemory2 (m : MemoryState) (out : Pointer) (bytes : Bytes) : MemoryState :=
  ((((((((m).storeAt (out.add 16#64) (bytes 16)).storeAt (out.add 17#64) (bytes 17)).storeAt (out.add 18#64) (bytes 18)).storeAt (out.add 19#64) (bytes 19)).storeAt (out.add 20#64) (bytes 20)).storeAt (out.add 21#64) (bytes 21)).storeAt (out.add 22#64) (bytes 22)).storeAt (out.add 23#64) (bytes 23)

theorem store_chunk2 (E : Env program.Γ) (out : Pointer) (bytes : Bytes)
    (s : GlobalState) (hr : SmallRange s.mem out 32)
    (hout : E.read (%arg0) = .value out)
    (hb16 : E.read (%384) = .value (bytes 16))
    (hk16 : E.read (%13) = .value 16#64)
    (hb17 : E.read (%386) = .value (bytes 17))
    (hk17 : E.read (%54) = .value 17#64)
    (hb18 : E.read (%388) = .value (bytes 18))
    (hk18 : E.read (%14) = .value 18#64)
    (hb19 : E.read (%392) = .value (bytes 19))
    (hk19 : E.read (%15) = .value 19#64)
    (hb20 : E.read (%394) = .value (bytes 20))
    (hk20 : E.read (%17) = .value 20#64)
    (hb21 : E.read (%396) = .value (bytes 21))
    (hk21 : E.read (%55) = .value 21#64)
    (hb22 : E.read (%398) = .value (bytes 22))
    (hk22 : E.read (%56) = .value 22#64)
    (hb23 : E.read (%400) = .value (bytes 23))
    (hk23 : E.read (%57) = .value 23#64)
    : storeBlock2.runBodyFrom E 0 s =
      .value (chunkEnv2 E out, {s with mem := chunkMemory2 s.mem out bytes}) := by
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      storeBlock2.runBodyFrom E' 0 S =
        .value (chunkEnv2 E out, {s with mem := chunkMemory2 s.mem out bytes}) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hEargs : E'.args = E.args := by rw [hE]
  have hrS : SmallRange S.mem out 32 := by rw [hS]; exact hr
  have hf16 := hrS.fits_add (k := 16) (count := 1) (by decide)
  have hf17 := hrS.fits_add (k := 17) (count := 1) (by decide)
  have hf18 := hrS.fits_add (k := 18) (count := 1) (by decide)
  have hf19 := hrS.fits_add (k := 19) (count := 1) (by decide)
  have hf20 := hrS.fits_add (k := 20) (count := 1) (by decide)
  have hf21 := hrS.fits_add (k := 21) (count := 1) (by decide)
  have hf22 := hrS.fits_add (k := 22) (count := 1) (by decide)
  have hf23 := hrS.fits_add (k := 23) (count := 1) (by decide)
  change E.args 0 = .value out at hout
  have hgep := hrS.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk16]
  clear hgep
  step_store [hout, hb16]
  have hgep := hrS.gep (k := 17) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk17]
  clear hgep
  step_store [hout, hb17]
  have hgep := hrS.gep (k := 18) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk18]
  clear hgep
  step_store [hout, hb18]
  have hgep := hrS.gep (k := 19) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk19]
  clear hgep
  step_store [hout, hb19]
  have hgep := hrS.gep (k := 20) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk20]
  clear hgep
  step_store [hout, hb20]
  have hgep := hrS.gep (k := 21) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk21]
  clear hgep
  step_store [hout, hb21]
  have hgep := hrS.gep (k := 22) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk22]
  clear hgep
  step_store [hout, hb22]
  have hgep := hrS.gep (k := 23) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, hout, hk23]
  clear hgep
  step_store [hout, hb23]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
