import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Output

/-! The actual black_box, shift, disjoint OR and 32-store suffix (instructions
240–306). The only external execution premise is one black_box byte call. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

abbrev signStoreProgram (p : Primitives) : Func :=
  {program p with blocks := fun _ =>
    {program.entry p with body := (program.entry p).body.drop 240}}

def signStoreEnv (E : Env program.Γ) (x y : Field.Serial) : Env program.Γ :=
  (storeEnv E (encodedBytes x y))[%221 := .value
    ((toBytes (fun j => (x j).toNat)).extractLsb' 0 8 &&& 1#8),
    %183 := .value ((toBytes (fun j => (y j).toNat)).extractLsb' 248 8),
    %44 := .value 7#8]

theorem signStoreEnv_args (E : Env program.Γ) (x y : Field.Serial) :
    (signStoreEnv E x y).args = E.args := by
  simp only [signStoreEnv, Env.write_args, storeEnv_args]

theorem sign_store_run (p : Primitives) (E : Env program.Γ)
    (out : Pointer) (x y : Field.Serial) (s t : GlobalState)
    (hr : SmallRange t.mem out 32) (hout : E.read (%arg0) = .value out)
    (hblack : p.blackBoxByte (.cons (.value
      ((toBytes (fun j => (x j).toNat)).extractLsb' 0 8 &&& 1#8)) .nil) s =
      .value (.cons (.value
        ((toBytes (fun j => (x j).toNat)).extractLsb' 0 8 &&& 1#8)) .nil, t)) :
    (signStoreProgram p).runFrom (signStoreEnv E x y) 0 s =
      .value (.nil, {t with mem := storeBytes t.mem out (encodedBytes x y)}) := by
  have htop : ((toBytes (fun j => (y j).toNat)).extractLsb' 248 8)[7] = false := by
    have hy := serialized_top_clear y
    simpa [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_extractLsb'] using hy
  have hdis := insertSign_disjoint
    ((toBytes (fun j => (x j).toNat)).extractLsb' 0 8)
    ((toBytes (fun j => (y j).toNat)).extractLsb' 248 8) htop
  simp only [BitVec.ofNat_eq_ofNat] at hdis
  have hr0 := hr.fits_add (k := 0) (count := 1) (by decide)
  have hr1 := hr.fits_add (k := 1) (count := 1) (by decide)
  have hr2 := hr.fits_add (k := 2) (count := 1) (by decide)
  have hr3 := hr.fits_add (k := 3) (count := 1) (by decide)
  have hr4 := hr.fits_add (k := 4) (count := 1) (by decide)
  have hr5 := hr.fits_add (k := 5) (count := 1) (by decide)
  have hr6 := hr.fits_add (k := 6) (count := 1) (by decide)
  have hr7 := hr.fits_add (k := 7) (count := 1) (by decide)
  have hr8 := hr.fits_add (k := 8) (count := 1) (by decide)
  have hr9 := hr.fits_add (k := 9) (count := 1) (by decide)
  have hr10 := hr.fits_add (k := 10) (count := 1) (by decide)
  have hr11 := hr.fits_add (k := 11) (count := 1) (by decide)
  have hr12 := hr.fits_add (k := 12) (count := 1) (by decide)
  have hr13 := hr.fits_add (k := 13) (count := 1) (by decide)
  have hr14 := hr.fits_add (k := 14) (count := 1) (by decide)
  have hr15 := hr.fits_add (k := 15) (count := 1) (by decide)
  have hr16 := hr.fits_add (k := 16) (count := 1) (by decide)
  have hr17 := hr.fits_add (k := 17) (count := 1) (by decide)
  have hr18 := hr.fits_add (k := 18) (count := 1) (by decide)
  have hr19 := hr.fits_add (k := 19) (count := 1) (by decide)
  have hr20 := hr.fits_add (k := 20) (count := 1) (by decide)
  have hr21 := hr.fits_add (k := 21) (count := 1) (by decide)
  have hr22 := hr.fits_add (k := 22) (count := 1) (by decide)
  have hr23 := hr.fits_add (k := 23) (count := 1) (by decide)
  have hr24 := hr.fits_add (k := 24) (count := 1) (by decide)
  have hr25 := hr.fits_add (k := 25) (count := 1) (by decide)
  have hr26 := hr.fits_add (k := 26) (count := 1) (by decide)
  have hr27 := hr.fits_add (k := 27) (count := 1) (by decide)
  have hr28 := hr.fits_add (k := 28) (count := 1) (by decide)
  have hr29 := hr.fits_add (k := 29) (count := 1) (by decide)
  have hr30 := hr.fits_add (k := 30) (count := 1) (by decide)
  have hr31 := hr.fits_add (k := 31) (count := 1) (by decide)
  simp only [Pointer.add_zero] at hr0
  change E.args 0 = .value out at hout
  generalize hE : signStoreEnv E x y = E'
  symm at hE
  have hEargs : E'.args = E.args :=
    (congrArg Env.args hE).trans (signStoreEnv_args E x y)
  dsimp only [signStoreEnv, storeEnv] at hE
  extract_state
  block_init
  rw [hS] at hblack
  step_impure => exact run_call (by simpa only [hS] using hblack)
  have hr : SmallRange S.mem out 32 := by simpa only [hS] using hr
  step_pure
  step_pure [hdis]
  step_store [hout]
  have hgep := hr.gep (k := 1) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 2) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 3) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 4) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 5) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 6) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 7) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 9) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 10) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 11) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 12) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 13) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 14) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 15) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 17) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 18) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 19) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 20) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 21) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 22) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 23) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 25) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 26) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 27) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 28) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 29) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 30) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  have hgep := hr.gep (k := 31) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, hout, GepIndex.inboundsOffset]
  clear hgep
  step_store [hout]
  step_pure
  rw [BasicBlock.runBodyFrom_done (Nat.le_of_ble_eq_true rfl)]
  simp only [EffectM.pure_eq, PoisonOr.value_bind, reduceBlockExit,
    reduceFuncContinue, Exit.run, Regs.read_nil]
  simp only [hS] <;> rfl

end Agave.Ed25519.Encoding.Compress.Execution
