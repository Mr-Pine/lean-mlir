import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.DoublePhases
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.PointOutput
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

/-! The original completed-point store suffix, with its original GEPs,
twenty stores, lifetime markers and return. The arithmetic prefix must supply
the store-value registers; this module derives all output bounds and readback. -/
namespace Agave.Ed25519.SmallOrder.Execution.DoublePhases
open LeanMLIR.RIR Verifier.Execution.SmallOrderProjectiveDouble
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def storeEnv (E : Env program.Γ) (value : PointWords) : Env program.Γ :=
  E[%4 := .value 8#64,
    %5 := .value 16#64,
    %6 := .value 24#64,
    %7 := .value 32#64,
    %1 := .value 40#64,
    %15 := .value 48#64,
    %8 := .value 56#64,
    %16 := .value 64#64,
    %9 := .value 72#64,
    %2 := .value 80#64,
    %17 := .value 88#64,
    %18 := .value 96#64,
    %19 := .value 104#64,
    %20 := .value 112#64,
    %21 := .value 120#64,
    %22 := .value 128#64,
    %23 := .value 136#64,
    %24 := .value 144#64,
    %25 := .value 152#64,
    %141 := .value (value 0),
    %142 := .value (value 1),
    %143 := .value (value 2),
    %144 := .value (value 3),
    %145 := .value (value 4),
    %72 := .value (value 5),
    %75 := .value (value 6),
    %78 := .value (value 7),
    %81 := .value (value 8),
    %84 := .value (value 9),
    %106 := .value (value 10),
    %107 := .value (value 11),
    %108 := .value (value 12),
    %109 := .value (value 13),
    %110 := .value (value 14),
    %167 := .value (value 15),
    %168 := .value (value 16),
    %169 := .value (value 17),
    %170 := .value (value 18),
    %171 := .value (value 19)]

abbrev storeProgram (p : Primitives) : Func :=
  {program p with blocks := fun _ =>
    {program.entry p with body := (program.entry p).body.drop 190}}

theorem store_run (p : Primitives) (E : Env program.Γ) (r : Pointer)
    (value : PointWords) (s : GlobalState) (hr : SmallRange s.mem r 160)
    (harg : E.read (%arg0) = .value r) :
    (storeProgram p).runFrom (storeEnv E value) 0 s =
      .value (.nil, {s with mem := storePointWords s.mem r value}) := by
  have hr0 := hr.fits_add (k := 0) (count := 8) (by decide)
  have hr8 := hr.fits_add (k := 8) (count := 8) (by decide)
  have hr16 := hr.fits_add (k := 16) (count := 8) (by decide)
  have hr24 := hr.fits_add (k := 24) (count := 8) (by decide)
  have hr32 := hr.fits_add (k := 32) (count := 8) (by decide)
  have hr40 := hr.fits_add (k := 40) (count := 8) (by decide)
  have hr48 := hr.fits_add (k := 48) (count := 8) (by decide)
  have hr56 := hr.fits_add (k := 56) (count := 8) (by decide)
  have hr64 := hr.fits_add (k := 64) (count := 8) (by decide)
  have hr72 := hr.fits_add (k := 72) (count := 8) (by decide)
  have hr80 := hr.fits_add (k := 80) (count := 8) (by decide)
  have hr88 := hr.fits_add (k := 88) (count := 8) (by decide)
  have hr96 := hr.fits_add (k := 96) (count := 8) (by decide)
  have hr104 := hr.fits_add (k := 104) (count := 8) (by decide)
  have hr112 := hr.fits_add (k := 112) (count := 8) (by decide)
  have hr120 := hr.fits_add (k := 120) (count := 8) (by decide)
  have hr128 := hr.fits_add (k := 128) (count := 8) (by decide)
  have hr136 := hr.fits_add (k := 136) (count := 8) (by decide)
  have hr144 := hr.fits_add (k := 144) (count := 8) (by decide)
  have hr152 := hr.fits_add (k := 152) (count := 8) (by decide)
  simp only [Pointer.add_zero] at hr0
  change E.args 0 = .value r at harg
  generalize hE : storeEnv E value = E'
  symm at hE
  have hEargs : E'.args = E.args := by
    simpa only [storeEnv, Env.write_args] using congrArg Env.args hE
  dsimp only [storeEnv] at hE
  extract_state
  block_init
  step_store [harg]
  have hgep := hr.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 40) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 48) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 56) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 64) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 72) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 80) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 88) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 96) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 104) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 112) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 120) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 128) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 136) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 144) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  have hgep := hr.gep (k := 152) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [harg, hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store [harg]
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  finish_block
  rw [hS]
  rfl

/-- Whole-payload readback follows from the actual stores rather than a
post-store representation premise. -/
theorem store_payload_run (p : Primitives) (E : Env program.Γ) (r : Pointer)
    (P : ConcretePoint) (s : GlobalState) (hr : SmallRange s.mem r 160)
    (harg : E.read (%arg0) = .value r) :
    ∃ t, (storeProgram p).runFrom (storeEnv E (payloadWords P)) 0 s =
        .value (.nil, t) ∧
      Verifier.Execution.Dalek.ReadBytes t r 160 P.bytes := by
  refine ⟨{s with mem := storePointWords s.mem r (payloadWords P)},
    store_run p E r (payloadWords P) s hr harg, ?_⟩
  exact ⟨smallRange_storePointWords hr r (payloadWords P), pointStore_read1280 s.mem r P hr⟩

end Agave.Ed25519.SmallOrder.Execution.DoublePhases
