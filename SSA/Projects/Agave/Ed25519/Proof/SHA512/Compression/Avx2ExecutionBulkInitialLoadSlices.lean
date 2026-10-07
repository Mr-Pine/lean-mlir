import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkInitialVectors
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkInitialSetup
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairStore

/-! The eight original bb9 dual-block load, byte-reversal, and cache-store slices.
Only concrete register values, live ranges, and input memory reads are premises. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

def bulkInitialPairState (mem : GlobalState) (scratch cache : Pointer) (j : Nat)
    (lo hi lo' hi' : Word) : GlobalState :=
  pairStoreState (pairStoreState mem scratch j lo hi) cache j lo' hi'

def bulkInitialSlice0Env (E : Env program.Γ) (data : Pointer) (first second : Bytes)
    (k0 k1 : Word) : Env program.Γ :=
  E[%361 := .value (data.add 128#64),
    %362 := pairVec (readWordNative second 0) (readWordNative second 1),
    %363 := pairVec (readWordNative first 0) (readWordNative first 1),
    %364 := bulkVec (readWordNative first 0) (readWordNative first 1) (readWordNative second 0) (readWordNative second 1),
    %365 := bulkInitialBytes (readWordNative first 0) (readWordNative first 1) (readWordNative second 0) (readWordNative second 1),
    %366 := bulkInitialShuffle (readWordNative first 0) (readWordNative first 1) (readWordNative second 0) (readWordNative second 1),
    %367 := bulkVec (readWordBE first 0) (readWordBE first 1) (readWordBE second 0) (readWordBE second 1),
    %368 := bulkVec (readWordBE first 0+k0) (readWordBE first 1+k1) (readWordBE second 0+k0) (readWordBE second 1+k1),
    %369 := pairVec (readWordBE first 0+k0) (readWordBE first 1+k1),
    %370 := pairVec (readWordBE second 0+k0) (readWordBE second 1+k1)]

theorem bulk_initial_slice0_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch cache : Pointer) (first second : Bytes) (k0 k1 : Word)
    (hd : SmallRange mem.mem data 256) (hs : SmallRange mem.mem scratch 128)
    (hc : SmallRange mem.mem cache 128)
    (hp : E.read (%360) = .value data)
    (hsp : E.read (%83) = .value (scratch.add 0#64))
    (hcp : E.read (%82) = .value (cache.add 0#64))
    (hhigh : E.read (%47) = .value 128#64)
    (hk : E.read (%51) = bulkVec k0 k1 k0 k1)
    (hrfirst : mem.mem.readAt data 128 = readWordNative first 1 ++ readWordNative first 0)
    (hrsecond : mem.mem.readAt (data.add 128#64) 128 = readWordNative second 1 ++ readWordNative second 0) :
    List.foldlM Instr.run E ((program.bb9.body.drop 3).take 12) mem =
      .value (bulkInitialSlice0Env E data first second k0 k1,
        bulkInitialPairState mem scratch cache 0
          (readWordBE first 0+k0) (readWordBE first 1+k1) (readWordBE second 0+k0) (readWordBE second 1+k1)) := by
  have hgHigh := hd.gep (k := 128) (by decide)
  have hfHigh := hd.fits_add (k := 128) (count := 16) (by decide)
  have hfLow := hd.fits_add (k := 0) (count := 16) (by decide)
  have hfScratch := hs.fits_add (k := 0) (count := 16) (by decide)
  have hfCache := (hc.fits_add (k := 0) (count := 16) (by decide)).storeAt
    (q := scratch.add 0#64) (x := (readWordBE first 1+k1) ++ (readWordBE first 0+k0))
  norm_num only at hgHigh
  simp only [Pointer.add_zero] at hsp hcp hfLow hfScratch hfCache
  have hshuffle := bulkInitialShuffle_any (readWordNative first 0) (readWordNative first 1) (readWordNative second 0) (readWordNative second 1) (E.read (%50))
  simp only [bulkInitialMask, bulkInitialBytes] at hshuffle
  have hcast := bulkInitialWords_native first second 0 0
  unfold bulkInitialWords at hcast
  let Epre : Env program.Γ := E[%361 := .value (data.add 128#64),
    %362 := pairVec (readWordNative second 0) (readWordNative second 1),
    %363 := pairVec (readWordNative first 0) (readWordNative first 1),
    %364 := bulkVec (readWordNative first 0) (readWordNative first 1) (readWordNative second 0) (readWordNative second 1),
    %365 := bulkInitialBytes (readWordNative first 0) (readWordNative first 1) (readWordNative second 0) (readWordNative second 1),
    %366 := bulkInitialShuffle (readWordNative first 0) (readWordNative first 1) (readWordNative second 0) (readWordNative second 1),
    %367 := bulkVec (readWordBE first 0) (readWordBE first 1) (readWordBE second 0) (readWordBE second 1),
    %368 := bulkVec (readWordBE first 0+k0) (readWordBE first 1+k1) (readWordBE second 0+k0) (readWordBE second 1+k1),
    %369 := pairVec (readWordBE first 0+k0) (readWordBE first 1+k1)]
  let mem1 := pairStoreState mem scratch 0 (readWordBE first 0+k0) (readWordBE first 1+k1)
  have hprefix : List.foldlM Instr.run E ((program.bb9.body.drop 3).take 9) mem =
      .value (Epre, mem) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run, Epre,
      hp, hhigh, hk, hgHigh, hfHigh, hfLow, hrfirst, hrsecond,
      pairVec_unflatten, -Ty.unflatten_vec,
      hshuffle, hcast, bulkVec_concat, bulkVec_add, bulkVec_lo,
      UnOp.compute, GepIndex.inboundsOffset, Operation.load,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]
    rw [bulkVec_concat]
    repeat' first
      | rw [bulkVec_concat]
      | rw [hshuffle]
      | rw [hcast]
      | rw [bulkVec_add]
      | rw [bulkVec_lo]
    rfl
  have hstoreFirst : List.foldlM Instr.run Epre ((program.bb9.body.drop 12).take 1) mem =
      .value (Epre, mem1) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      Epre, mem1, pairStoreState, pairScratchStore, hsp, hfScratch,
      pairVec_flatten, Operation.store, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, throwUBIf]
  have hhighVec : List.foldlM Instr.run Epre ((program.bb9.body.drop 13).take 1) mem1 =
      .value (bulkInitialSlice0Env E data first second k0 k1, mem1) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      Epre, bulkInitialSlice0Env, bulkVec_hi, BinOp.compute, bulkVec, pairVec, Ty.wrap_vec, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect]
  have hstoreSecond : List.foldlM Instr.run (bulkInitialSlice0Env E data first second k0 k1)
      ((program.bb9.body.drop 14).take 1) mem1 =
      .value (bulkInitialSlice0Env E data first second k0 k1,
        bulkInitialPairState mem scratch cache 0
          (readWordBE first 0+k0) (readWordBE first 1+k1) (readWordBE second 0+k0) (readWordBE second 1+k1)) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      bulkInitialSlice0Env, bulkInitialPairState, mem1, pairStoreState, pairScratchStore,
      hcp, hfCache, pairVec_flatten, Operation.store, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, throwUBIf]
  have hcut : (program.bb9.body.drop 3).take 12 =
      (program.bb9.body.drop 3).take 9 ++
      (program.bb9.body.drop 12).take 1 ++
      (program.bb9.body.drop 13).take 1 ++
      (program.bb9.body.drop 14).take 1 := by rfl
  rw [hcut]
  simp only [List.foldlM_append, EffectM.bind_eq, hprefix, LeanMLIR.RIR.PoisonOr.value_bind,
    hstoreFirst, hhighVec, hstoreSecond]

theorem bulkInitialSlice0Env_frame (E : Env program.Γ) (data : Pointer)
    (first second : Bytes) (k0 k1 : Word) :
    RegFrame 361 370 E (bulkInitialSlice0Env E data first second k0 k1) := by
  unfold bulkInitialSlice0Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

def bulkInitialSlice1Env (E : Env program.Γ) (data : Pointer) (first second : Bytes)
    (k0 k1 : Word) : Env program.Γ :=
  E[%371 := .value (data.add 144#64),
    %372 := pairVec (readWordNative second 2) (readWordNative second 3),
    %373 := .value (data.add 16#64),
    %374 := pairVec (readWordNative first 2) (readWordNative first 3),
    %375 := bulkVec (readWordNative first 2) (readWordNative first 3) (readWordNative second 2) (readWordNative second 3),
    %376 := bulkInitialBytes (readWordNative first 2) (readWordNative first 3) (readWordNative second 2) (readWordNative second 3),
    %377 := bulkInitialShuffle (readWordNative first 2) (readWordNative first 3) (readWordNative second 2) (readWordNative second 3),
    %378 := bulkVec (readWordBE first 2) (readWordBE first 3) (readWordBE second 2) (readWordBE second 3),
    %379 := bulkVec (readWordBE first 2+k0) (readWordBE first 3+k1) (readWordBE second 2+k0) (readWordBE second 3+k1),
    %380 := pairVec (readWordBE first 2+k0) (readWordBE first 3+k1),
    %381 := pairVec (readWordBE second 2+k0) (readWordBE second 3+k1)]

theorem bulk_initial_slice1_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch cache : Pointer) (first second : Bytes) (k0 k1 : Word)
    (hd : SmallRange mem.mem data 256) (hs : SmallRange mem.mem scratch 128)
    (hc : SmallRange mem.mem cache 128)
    (hp : E.read (%360) = .value data)
    (hsp : E.read (%321) = .value (scratch.add 16#64))
    (hcp : E.read (%322) = .value (cache.add 16#64))
    (hhigh : E.read (%52) = .value 144#64)
    (hlow : E.read (%4) = .value 16#64)
    (hk : E.read (%53) = bulkVec k0 k1 k0 k1)
    (hrfirst : mem.mem.readAt (data.add 16#64) 128 = readWordNative first 3 ++ readWordNative first 2)
    (hrsecond : mem.mem.readAt (data.add 144#64) 128 = readWordNative second 3 ++ readWordNative second 2) :
    List.foldlM Instr.run E ((program.bb9.body.drop 15).take 13) mem =
      .value (bulkInitialSlice1Env E data first second k0 k1,
        bulkInitialPairState mem scratch cache 1
          (readWordBE first 2+k0) (readWordBE first 3+k1) (readWordBE second 2+k0) (readWordBE second 3+k1)) := by
  have hgHigh := hd.gep (k := 144) (by decide)
  have hfHigh := hd.fits_add (k := 144) (count := 16) (by decide)
  have hfLow := hd.fits_add (k := 16) (count := 16) (by decide)
  have hfScratch := hs.fits_add (k := 16) (count := 16) (by decide)
  have hfCache := (hc.fits_add (k := 16) (count := 16) (by decide)).storeAt
    (q := scratch.add 16#64) (x := (readWordBE first 3+k1) ++ (readWordBE first 2+k0))
  have hgLow := hd.gep (k := 16) (by decide)
  norm_num only at hgHigh hgLow
  have hshuffle := bulkInitialShuffle_any (readWordNative first 2) (readWordNative first 3) (readWordNative second 2) (readWordNative second 3) (E.read (%50))
  simp only [bulkInitialMask, bulkInitialBytes] at hshuffle
  have hcast := bulkInitialWords_native first second 2 2
  unfold bulkInitialWords at hcast
  let Epre : Env program.Γ := E[%371 := .value (data.add 144#64),
    %372 := pairVec (readWordNative second 2) (readWordNative second 3),
    %373 := .value (data.add 16#64),
    %374 := pairVec (readWordNative first 2) (readWordNative first 3),
    %375 := bulkVec (readWordNative first 2) (readWordNative first 3) (readWordNative second 2) (readWordNative second 3),
    %376 := bulkInitialBytes (readWordNative first 2) (readWordNative first 3) (readWordNative second 2) (readWordNative second 3),
    %377 := bulkInitialShuffle (readWordNative first 2) (readWordNative first 3) (readWordNative second 2) (readWordNative second 3),
    %378 := bulkVec (readWordBE first 2) (readWordBE first 3) (readWordBE second 2) (readWordBE second 3),
    %379 := bulkVec (readWordBE first 2+k0) (readWordBE first 3+k1) (readWordBE second 2+k0) (readWordBE second 3+k1),
    %380 := pairVec (readWordBE first 2+k0) (readWordBE first 3+k1)]
  let mem1 := pairStoreState mem scratch 1 (readWordBE first 2+k0) (readWordBE first 3+k1)
  have hprefix : List.foldlM Instr.run E ((program.bb9.body.drop 15).take 10) mem =
      .value (Epre, mem) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run, Epre,
      hp, hhigh, hlow, hk, hgHigh, hgLow, hfHigh, hfLow, hrfirst, hrsecond,
      pairVec_unflatten, -Ty.unflatten_vec,
      hshuffle, hcast, bulkVec_concat, bulkVec_add, bulkVec_lo,
      UnOp.compute, GepIndex.inboundsOffset, Operation.load,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]
    rw [bulkVec_concat]
    repeat' first
      | rw [bulkVec_concat]
      | rw [hshuffle]
      | rw [hcast]
      | rw [bulkVec_add]
      | rw [bulkVec_lo]
    rfl
  have hstoreFirst : List.foldlM Instr.run Epre ((program.bb9.body.drop 25).take 1) mem =
      .value (Epre, mem1) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      Epre, mem1, pairStoreState, pairScratchStore, hsp, hfScratch,
      pairVec_flatten, Operation.store, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, throwUBIf]
  have hhighVec : List.foldlM Instr.run Epre ((program.bb9.body.drop 26).take 1) mem1 =
      .value (bulkInitialSlice1Env E data first second k0 k1, mem1) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      Epre, bulkInitialSlice1Env, bulkVec_hi, BinOp.compute, bulkVec, pairVec, Ty.wrap_vec, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect]
  have hstoreSecond : List.foldlM Instr.run (bulkInitialSlice1Env E data first second k0 k1)
      ((program.bb9.body.drop 27).take 1) mem1 =
      .value (bulkInitialSlice1Env E data first second k0 k1,
        bulkInitialPairState mem scratch cache 1
          (readWordBE first 2+k0) (readWordBE first 3+k1) (readWordBE second 2+k0) (readWordBE second 3+k1)) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      bulkInitialSlice1Env, bulkInitialPairState, mem1, pairStoreState, pairScratchStore,
      hcp, hfCache, pairVec_flatten, Operation.store, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, throwUBIf]
  have hcut : (program.bb9.body.drop 15).take 13 =
      (program.bb9.body.drop 15).take 10 ++
      (program.bb9.body.drop 25).take 1 ++
      (program.bb9.body.drop 26).take 1 ++
      (program.bb9.body.drop 27).take 1 := by rfl
  rw [hcut]
  simp only [List.foldlM_append, EffectM.bind_eq, hprefix, LeanMLIR.RIR.PoisonOr.value_bind,
    hstoreFirst, hhighVec, hstoreSecond]

theorem bulkInitialSlice1Env_frame (E : Env program.Γ) (data : Pointer)
    (first second : Bytes) (k0 k1 : Word) :
    RegFrame 371 381 E (bulkInitialSlice1Env E data first second k0 k1) := by
  unfold bulkInitialSlice1Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

def bulkInitialSlice2Env (E : Env program.Γ) (data : Pointer) (first second : Bytes)
    (k0 k1 : Word) : Env program.Γ :=
  E[%382 := .value (data.add 160#64),
    %383 := pairVec (readWordNative second 4) (readWordNative second 5),
    %384 := .value (data.add 32#64),
    %385 := pairVec (readWordNative first 4) (readWordNative first 5),
    %386 := bulkVec (readWordNative first 4) (readWordNative first 5) (readWordNative second 4) (readWordNative second 5),
    %387 := bulkInitialBytes (readWordNative first 4) (readWordNative first 5) (readWordNative second 4) (readWordNative second 5),
    %388 := bulkInitialShuffle (readWordNative first 4) (readWordNative first 5) (readWordNative second 4) (readWordNative second 5),
    %389 := bulkVec (readWordBE first 4) (readWordBE first 5) (readWordBE second 4) (readWordBE second 5),
    %390 := bulkVec (readWordBE first 4+k0) (readWordBE first 5+k1) (readWordBE second 4+k0) (readWordBE second 5+k1),
    %391 := pairVec (readWordBE first 4+k0) (readWordBE first 5+k1),
    %392 := pairVec (readWordBE second 4+k0) (readWordBE second 5+k1)]

theorem bulk_initial_slice2_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch cache : Pointer) (first second : Bytes) (k0 k1 : Word)
    (hd : SmallRange mem.mem data 256) (hs : SmallRange mem.mem scratch 128)
    (hc : SmallRange mem.mem cache 128)
    (hp : E.read (%360) = .value data)
    (hsp : E.read (%323) = .value (scratch.add 32#64))
    (hcp : E.read (%324) = .value (cache.add 32#64))
    (hhigh : E.read (%54) = .value 160#64)
    (hlow : E.read (%6) = .value 32#64)
    (hk : E.read (%55) = bulkVec k0 k1 k0 k1)
    (hrfirst : mem.mem.readAt (data.add 32#64) 128 = readWordNative first 5 ++ readWordNative first 4)
    (hrsecond : mem.mem.readAt (data.add 160#64) 128 = readWordNative second 5 ++ readWordNative second 4) :
    List.foldlM Instr.run E ((program.bb9.body.drop 28).take 13) mem =
      .value (bulkInitialSlice2Env E data first second k0 k1,
        bulkInitialPairState mem scratch cache 2
          (readWordBE first 4+k0) (readWordBE first 5+k1) (readWordBE second 4+k0) (readWordBE second 5+k1)) := by
  have hgHigh := hd.gep (k := 160) (by decide)
  have hfHigh := hd.fits_add (k := 160) (count := 16) (by decide)
  have hfLow := hd.fits_add (k := 32) (count := 16) (by decide)
  have hfScratch := hs.fits_add (k := 32) (count := 16) (by decide)
  have hfCache := (hc.fits_add (k := 32) (count := 16) (by decide)).storeAt
    (q := scratch.add 32#64) (x := (readWordBE first 5+k1) ++ (readWordBE first 4+k0))
  have hgLow := hd.gep (k := 32) (by decide)
  norm_num only at hgHigh hgLow
  have hshuffle := bulkInitialShuffle_any (readWordNative first 4) (readWordNative first 5) (readWordNative second 4) (readWordNative second 5) (E.read (%50))
  simp only [bulkInitialMask, bulkInitialBytes] at hshuffle
  have hcast := bulkInitialWords_native first second 4 4
  unfold bulkInitialWords at hcast
  let Epre : Env program.Γ := E[%382 := .value (data.add 160#64),
    %383 := pairVec (readWordNative second 4) (readWordNative second 5),
    %384 := .value (data.add 32#64),
    %385 := pairVec (readWordNative first 4) (readWordNative first 5),
    %386 := bulkVec (readWordNative first 4) (readWordNative first 5) (readWordNative second 4) (readWordNative second 5),
    %387 := bulkInitialBytes (readWordNative first 4) (readWordNative first 5) (readWordNative second 4) (readWordNative second 5),
    %388 := bulkInitialShuffle (readWordNative first 4) (readWordNative first 5) (readWordNative second 4) (readWordNative second 5),
    %389 := bulkVec (readWordBE first 4) (readWordBE first 5) (readWordBE second 4) (readWordBE second 5),
    %390 := bulkVec (readWordBE first 4+k0) (readWordBE first 5+k1) (readWordBE second 4+k0) (readWordBE second 5+k1),
    %391 := pairVec (readWordBE first 4+k0) (readWordBE first 5+k1)]
  let mem1 := pairStoreState mem scratch 2 (readWordBE first 4+k0) (readWordBE first 5+k1)
  have hprefix : List.foldlM Instr.run E ((program.bb9.body.drop 28).take 10) mem =
      .value (Epre, mem) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run, Epre,
      hp, hhigh, hlow, hk, hgHigh, hgLow, hfHigh, hfLow, hrfirst, hrsecond,
      pairVec_unflatten, -Ty.unflatten_vec,
      hshuffle, hcast, bulkVec_concat, bulkVec_add, bulkVec_lo,
      UnOp.compute, GepIndex.inboundsOffset, Operation.load,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]
    rw [bulkVec_concat]
    repeat' first
      | rw [bulkVec_concat]
      | rw [hshuffle]
      | rw [hcast]
      | rw [bulkVec_add]
      | rw [bulkVec_lo]
    rfl
  have hstoreFirst : List.foldlM Instr.run Epre ((program.bb9.body.drop 38).take 1) mem =
      .value (Epre, mem1) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      Epre, mem1, pairStoreState, pairScratchStore, hsp, hfScratch,
      pairVec_flatten, Operation.store, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, throwUBIf]
  have hhighVec : List.foldlM Instr.run Epre ((program.bb9.body.drop 39).take 1) mem1 =
      .value (bulkInitialSlice2Env E data first second k0 k1, mem1) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      Epre, bulkInitialSlice2Env, bulkVec_hi, BinOp.compute, bulkVec, pairVec, Ty.wrap_vec, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect]
  have hstoreSecond : List.foldlM Instr.run (bulkInitialSlice2Env E data first second k0 k1)
      ((program.bb9.body.drop 40).take 1) mem1 =
      .value (bulkInitialSlice2Env E data first second k0 k1,
        bulkInitialPairState mem scratch cache 2
          (readWordBE first 4+k0) (readWordBE first 5+k1) (readWordBE second 4+k0) (readWordBE second 5+k1)) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      bulkInitialSlice2Env, bulkInitialPairState, mem1, pairStoreState, pairScratchStore,
      hcp, hfCache, pairVec_flatten, Operation.store, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, throwUBIf]
  have hcut : (program.bb9.body.drop 28).take 13 =
      (program.bb9.body.drop 28).take 10 ++
      (program.bb9.body.drop 38).take 1 ++
      (program.bb9.body.drop 39).take 1 ++
      (program.bb9.body.drop 40).take 1 := by rfl
  rw [hcut]
  simp only [List.foldlM_append, EffectM.bind_eq, hprefix, LeanMLIR.RIR.PoisonOr.value_bind,
    hstoreFirst, hhighVec, hstoreSecond]

theorem bulkInitialSlice2Env_frame (E : Env program.Γ) (data : Pointer)
    (first second : Bytes) (k0 k1 : Word) :
    RegFrame 382 392 E (bulkInitialSlice2Env E data first second k0 k1) := by
  unfold bulkInitialSlice2Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

def bulkInitialSlice3Env (E : Env program.Γ) (data : Pointer) (first second : Bytes)
    (k0 k1 : Word) : Env program.Γ :=
  E[%393 := .value (data.add 176#64),
    %394 := pairVec (readWordNative second 6) (readWordNative second 7),
    %395 := .value (data.add 48#64),
    %396 := pairVec (readWordNative first 6) (readWordNative first 7),
    %397 := bulkVec (readWordNative first 6) (readWordNative first 7) (readWordNative second 6) (readWordNative second 7),
    %398 := bulkInitialBytes (readWordNative first 6) (readWordNative first 7) (readWordNative second 6) (readWordNative second 7),
    %399 := bulkInitialShuffle (readWordNative first 6) (readWordNative first 7) (readWordNative second 6) (readWordNative second 7),
    %400 := bulkVec (readWordBE first 6) (readWordBE first 7) (readWordBE second 6) (readWordBE second 7),
    %401 := bulkVec (readWordBE first 6+k0) (readWordBE first 7+k1) (readWordBE second 6+k0) (readWordBE second 7+k1),
    %402 := pairVec (readWordBE first 6+k0) (readWordBE first 7+k1),
    %403 := pairVec (readWordBE second 6+k0) (readWordBE second 7+k1)]

theorem bulk_initial_slice3_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch cache : Pointer) (first second : Bytes) (k0 k1 : Word)
    (hd : SmallRange mem.mem data 256) (hs : SmallRange mem.mem scratch 128)
    (hc : SmallRange mem.mem cache 128)
    (hp : E.read (%360) = .value data)
    (hsp : E.read (%325) = .value (scratch.add 48#64))
    (hcp : E.read (%326) = .value (cache.add 48#64))
    (hhigh : E.read (%56) = .value 176#64)
    (hlow : E.read (%8) = .value 48#64)
    (hk : E.read (%57) = bulkVec k0 k1 k0 k1)
    (hrfirst : mem.mem.readAt (data.add 48#64) 128 = readWordNative first 7 ++ readWordNative first 6)
    (hrsecond : mem.mem.readAt (data.add 176#64) 128 = readWordNative second 7 ++ readWordNative second 6) :
    List.foldlM Instr.run E ((program.bb9.body.drop 41).take 13) mem =
      .value (bulkInitialSlice3Env E data first second k0 k1,
        bulkInitialPairState mem scratch cache 3
          (readWordBE first 6+k0) (readWordBE first 7+k1) (readWordBE second 6+k0) (readWordBE second 7+k1)) := by
  have hgHigh := hd.gep (k := 176) (by decide)
  have hfHigh := hd.fits_add (k := 176) (count := 16) (by decide)
  have hfLow := hd.fits_add (k := 48) (count := 16) (by decide)
  have hfScratch := hs.fits_add (k := 48) (count := 16) (by decide)
  have hfCache := (hc.fits_add (k := 48) (count := 16) (by decide)).storeAt
    (q := scratch.add 48#64) (x := (readWordBE first 7+k1) ++ (readWordBE first 6+k0))
  have hgLow := hd.gep (k := 48) (by decide)
  norm_num only at hgHigh hgLow
  have hshuffle := bulkInitialShuffle_any (readWordNative first 6) (readWordNative first 7) (readWordNative second 6) (readWordNative second 7) (E.read (%50))
  simp only [bulkInitialMask, bulkInitialBytes] at hshuffle
  have hcast := bulkInitialWords_native first second 6 6
  unfold bulkInitialWords at hcast
  let Epre : Env program.Γ := E[%393 := .value (data.add 176#64),
    %394 := pairVec (readWordNative second 6) (readWordNative second 7),
    %395 := .value (data.add 48#64),
    %396 := pairVec (readWordNative first 6) (readWordNative first 7),
    %397 := bulkVec (readWordNative first 6) (readWordNative first 7) (readWordNative second 6) (readWordNative second 7),
    %398 := bulkInitialBytes (readWordNative first 6) (readWordNative first 7) (readWordNative second 6) (readWordNative second 7),
    %399 := bulkInitialShuffle (readWordNative first 6) (readWordNative first 7) (readWordNative second 6) (readWordNative second 7),
    %400 := bulkVec (readWordBE first 6) (readWordBE first 7) (readWordBE second 6) (readWordBE second 7),
    %401 := bulkVec (readWordBE first 6+k0) (readWordBE first 7+k1) (readWordBE second 6+k0) (readWordBE second 7+k1),
    %402 := pairVec (readWordBE first 6+k0) (readWordBE first 7+k1)]
  let mem1 := pairStoreState mem scratch 3 (readWordBE first 6+k0) (readWordBE first 7+k1)
  have hprefix : List.foldlM Instr.run E ((program.bb9.body.drop 41).take 10) mem =
      .value (Epre, mem) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run, Epre,
      hp, hhigh, hlow, hk, hgHigh, hgLow, hfHigh, hfLow, hrfirst, hrsecond,
      pairVec_unflatten, -Ty.unflatten_vec,
      hshuffle, hcast, bulkVec_concat, bulkVec_add, bulkVec_lo,
      UnOp.compute, GepIndex.inboundsOffset, Operation.load,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]
    rw [bulkVec_concat]
    repeat' first
      | rw [bulkVec_concat]
      | rw [hshuffle]
      | rw [hcast]
      | rw [bulkVec_add]
      | rw [bulkVec_lo]
    rfl
  have hstoreFirst : List.foldlM Instr.run Epre ((program.bb9.body.drop 51).take 1) mem =
      .value (Epre, mem1) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      Epre, mem1, pairStoreState, pairScratchStore, hsp, hfScratch,
      pairVec_flatten, Operation.store, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, throwUBIf]
  have hhighVec : List.foldlM Instr.run Epre ((program.bb9.body.drop 52).take 1) mem1 =
      .value (bulkInitialSlice3Env E data first second k0 k1, mem1) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      Epre, bulkInitialSlice3Env, bulkVec_hi, BinOp.compute, bulkVec, pairVec, Ty.wrap_vec, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect]
  have hstoreSecond : List.foldlM Instr.run (bulkInitialSlice3Env E data first second k0 k1)
      ((program.bb9.body.drop 53).take 1) mem1 =
      .value (bulkInitialSlice3Env E data first second k0 k1,
        bulkInitialPairState mem scratch cache 3
          (readWordBE first 6+k0) (readWordBE first 7+k1) (readWordBE second 6+k0) (readWordBE second 7+k1)) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      bulkInitialSlice3Env, bulkInitialPairState, mem1, pairStoreState, pairScratchStore,
      hcp, hfCache, pairVec_flatten, Operation.store, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, throwUBIf]
  have hcut : (program.bb9.body.drop 41).take 13 =
      (program.bb9.body.drop 41).take 10 ++
      (program.bb9.body.drop 51).take 1 ++
      (program.bb9.body.drop 52).take 1 ++
      (program.bb9.body.drop 53).take 1 := by rfl
  rw [hcut]
  simp only [List.foldlM_append, EffectM.bind_eq, hprefix, LeanMLIR.RIR.PoisonOr.value_bind,
    hstoreFirst, hhighVec, hstoreSecond]

theorem bulkInitialSlice3Env_frame (E : Env program.Γ) (data : Pointer)
    (first second : Bytes) (k0 k1 : Word) :
    RegFrame 393 403 E (bulkInitialSlice3Env E data first second k0 k1) := by
  unfold bulkInitialSlice3Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

def bulkInitialSlice4Env (E : Env program.Γ) (data : Pointer) (first second : Bytes)
    (k0 k1 : Word) : Env program.Γ :=
  E[%404 := .value (data.add 192#64),
    %405 := pairVec (readWordNative second 8) (readWordNative second 9),
    %406 := .value (data.add 64#64),
    %407 := pairVec (readWordNative first 8) (readWordNative first 9),
    %408 := bulkVec (readWordNative first 8) (readWordNative first 9) (readWordNative second 8) (readWordNative second 9),
    %409 := bulkInitialBytes (readWordNative first 8) (readWordNative first 9) (readWordNative second 8) (readWordNative second 9),
    %410 := bulkInitialShuffle (readWordNative first 8) (readWordNative first 9) (readWordNative second 8) (readWordNative second 9),
    %411 := bulkVec (readWordBE first 8) (readWordBE first 9) (readWordBE second 8) (readWordBE second 9),
    %412 := bulkVec (readWordBE first 8+k0) (readWordBE first 9+k1) (readWordBE second 8+k0) (readWordBE second 9+k1),
    %413 := pairVec (readWordBE first 8+k0) (readWordBE first 9+k1),
    %414 := pairVec (readWordBE second 8+k0) (readWordBE second 9+k1)]

theorem bulk_initial_slice4_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch cache : Pointer) (first second : Bytes) (k0 k1 : Word)
    (hd : SmallRange mem.mem data 256) (hs : SmallRange mem.mem scratch 128)
    (hc : SmallRange mem.mem cache 128)
    (hp : E.read (%360) = .value data)
    (hsp : E.read (%327) = .value (scratch.add 64#64))
    (hcp : E.read (%328) = .value (cache.add 64#64))
    (hhigh : E.read (%58) = .value 192#64)
    (hlow : E.read (%15) = .value 64#64)
    (hk : E.read (%59) = bulkVec k0 k1 k0 k1)
    (hrfirst : mem.mem.readAt (data.add 64#64) 128 = readWordNative first 9 ++ readWordNative first 8)
    (hrsecond : mem.mem.readAt (data.add 192#64) 128 = readWordNative second 9 ++ readWordNative second 8) :
    List.foldlM Instr.run E ((program.bb9.body.drop 54).take 13) mem =
      .value (bulkInitialSlice4Env E data first second k0 k1,
        bulkInitialPairState mem scratch cache 4
          (readWordBE first 8+k0) (readWordBE first 9+k1) (readWordBE second 8+k0) (readWordBE second 9+k1)) := by
  have hgHigh := hd.gep (k := 192) (by decide)
  have hfHigh := hd.fits_add (k := 192) (count := 16) (by decide)
  have hfLow := hd.fits_add (k := 64) (count := 16) (by decide)
  have hfScratch := hs.fits_add (k := 64) (count := 16) (by decide)
  have hfCache := (hc.fits_add (k := 64) (count := 16) (by decide)).storeAt
    (q := scratch.add 64#64) (x := (readWordBE first 9+k1) ++ (readWordBE first 8+k0))
  have hgLow := hd.gep (k := 64) (by decide)
  norm_num only at hgHigh hgLow
  have hshuffle := bulkInitialShuffle_any (readWordNative first 8) (readWordNative first 9) (readWordNative second 8) (readWordNative second 9) (E.read (%50))
  simp only [bulkInitialMask, bulkInitialBytes] at hshuffle
  have hcast := bulkInitialWords_native first second 8 8
  unfold bulkInitialWords at hcast
  let Epre : Env program.Γ := E[%404 := .value (data.add 192#64),
    %405 := pairVec (readWordNative second 8) (readWordNative second 9),
    %406 := .value (data.add 64#64),
    %407 := pairVec (readWordNative first 8) (readWordNative first 9),
    %408 := bulkVec (readWordNative first 8) (readWordNative first 9) (readWordNative second 8) (readWordNative second 9),
    %409 := bulkInitialBytes (readWordNative first 8) (readWordNative first 9) (readWordNative second 8) (readWordNative second 9),
    %410 := bulkInitialShuffle (readWordNative first 8) (readWordNative first 9) (readWordNative second 8) (readWordNative second 9),
    %411 := bulkVec (readWordBE first 8) (readWordBE first 9) (readWordBE second 8) (readWordBE second 9),
    %412 := bulkVec (readWordBE first 8+k0) (readWordBE first 9+k1) (readWordBE second 8+k0) (readWordBE second 9+k1),
    %413 := pairVec (readWordBE first 8+k0) (readWordBE first 9+k1)]
  let mem1 := pairStoreState mem scratch 4 (readWordBE first 8+k0) (readWordBE first 9+k1)
  have hprefix : List.foldlM Instr.run E ((program.bb9.body.drop 54).take 10) mem =
      .value (Epre, mem) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run, Epre,
      hp, hhigh, hlow, hk, hgHigh, hgLow, hfHigh, hfLow, hrfirst, hrsecond,
      pairVec_unflatten, -Ty.unflatten_vec,
      hshuffle, hcast, bulkVec_concat, bulkVec_add, bulkVec_lo,
      UnOp.compute, GepIndex.inboundsOffset, Operation.load,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]
    rw [bulkVec_concat]
    repeat' first
      | rw [bulkVec_concat]
      | rw [hshuffle]
      | rw [hcast]
      | rw [bulkVec_add]
      | rw [bulkVec_lo]
    rfl
  have hstoreFirst : List.foldlM Instr.run Epre ((program.bb9.body.drop 64).take 1) mem =
      .value (Epre, mem1) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      Epre, mem1, pairStoreState, pairScratchStore, hsp, hfScratch,
      pairVec_flatten, Operation.store, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, throwUBIf]
  have hhighVec : List.foldlM Instr.run Epre ((program.bb9.body.drop 65).take 1) mem1 =
      .value (bulkInitialSlice4Env E data first second k0 k1, mem1) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      Epre, bulkInitialSlice4Env, bulkVec_hi, BinOp.compute, bulkVec, pairVec, Ty.wrap_vec, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect]
  have hstoreSecond : List.foldlM Instr.run (bulkInitialSlice4Env E data first second k0 k1)
      ((program.bb9.body.drop 66).take 1) mem1 =
      .value (bulkInitialSlice4Env E data first second k0 k1,
        bulkInitialPairState mem scratch cache 4
          (readWordBE first 8+k0) (readWordBE first 9+k1) (readWordBE second 8+k0) (readWordBE second 9+k1)) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      bulkInitialSlice4Env, bulkInitialPairState, mem1, pairStoreState, pairScratchStore,
      hcp, hfCache, pairVec_flatten, Operation.store, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, throwUBIf]
  have hcut : (program.bb9.body.drop 54).take 13 =
      (program.bb9.body.drop 54).take 10 ++
      (program.bb9.body.drop 64).take 1 ++
      (program.bb9.body.drop 65).take 1 ++
      (program.bb9.body.drop 66).take 1 := by rfl
  rw [hcut]
  simp only [List.foldlM_append, EffectM.bind_eq, hprefix, LeanMLIR.RIR.PoisonOr.value_bind,
    hstoreFirst, hhighVec, hstoreSecond]

theorem bulkInitialSlice4Env_frame (E : Env program.Γ) (data : Pointer)
    (first second : Bytes) (k0 k1 : Word) :
    RegFrame 404 414 E (bulkInitialSlice4Env E data first second k0 k1) := by
  unfold bulkInitialSlice4Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

def bulkInitialSlice5Env (E : Env program.Γ) (data : Pointer) (first second : Bytes)
    (k0 k1 : Word) : Env program.Γ :=
  E[%415 := .value (data.add 208#64),
    %416 := pairVec (readWordNative second 10) (readWordNative second 11),
    %417 := .value (data.add 80#64),
    %418 := pairVec (readWordNative first 10) (readWordNative first 11),
    %419 := bulkVec (readWordNative first 10) (readWordNative first 11) (readWordNative second 10) (readWordNative second 11),
    %420 := bulkInitialBytes (readWordNative first 10) (readWordNative first 11) (readWordNative second 10) (readWordNative second 11),
    %421 := bulkInitialShuffle (readWordNative first 10) (readWordNative first 11) (readWordNative second 10) (readWordNative second 11),
    %422 := bulkVec (readWordBE first 10) (readWordBE first 11) (readWordBE second 10) (readWordBE second 11),
    %423 := bulkVec (readWordBE first 10+k0) (readWordBE first 11+k1) (readWordBE second 10+k0) (readWordBE second 11+k1),
    %424 := pairVec (readWordBE first 10+k0) (readWordBE first 11+k1),
    %425 := pairVec (readWordBE second 10+k0) (readWordBE second 11+k1)]

theorem bulk_initial_slice5_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch cache : Pointer) (first second : Bytes) (k0 k1 : Word)
    (hd : SmallRange mem.mem data 256) (hs : SmallRange mem.mem scratch 128)
    (hc : SmallRange mem.mem cache 128)
    (hp : E.read (%360) = .value data)
    (hsp : E.read (%329) = .value (scratch.add 80#64))
    (hcp : E.read (%330) = .value (cache.add 80#64))
    (hhigh : E.read (%60) = .value 208#64)
    (hlow : E.read (%17) = .value 80#64)
    (hk : E.read (%61) = bulkVec k0 k1 k0 k1)
    (hrfirst : mem.mem.readAt (data.add 80#64) 128 = readWordNative first 11 ++ readWordNative first 10)
    (hrsecond : mem.mem.readAt (data.add 208#64) 128 = readWordNative second 11 ++ readWordNative second 10) :
    List.foldlM Instr.run E ((program.bb9.body.drop 67).take 13) mem =
      .value (bulkInitialSlice5Env E data first second k0 k1,
        bulkInitialPairState mem scratch cache 5
          (readWordBE first 10+k0) (readWordBE first 11+k1) (readWordBE second 10+k0) (readWordBE second 11+k1)) := by
  have hgHigh := hd.gep (k := 208) (by decide)
  have hfHigh := hd.fits_add (k := 208) (count := 16) (by decide)
  have hfLow := hd.fits_add (k := 80) (count := 16) (by decide)
  have hfScratch := hs.fits_add (k := 80) (count := 16) (by decide)
  have hfCache := (hc.fits_add (k := 80) (count := 16) (by decide)).storeAt
    (q := scratch.add 80#64) (x := (readWordBE first 11+k1) ++ (readWordBE first 10+k0))
  have hgLow := hd.gep (k := 80) (by decide)
  norm_num only at hgHigh hgLow
  have hshuffle := bulkInitialShuffle_any (readWordNative first 10) (readWordNative first 11) (readWordNative second 10) (readWordNative second 11) (E.read (%50))
  simp only [bulkInitialMask, bulkInitialBytes] at hshuffle
  have hcast := bulkInitialWords_native first second 10 10
  unfold bulkInitialWords at hcast
  let Epre : Env program.Γ := E[%415 := .value (data.add 208#64),
    %416 := pairVec (readWordNative second 10) (readWordNative second 11),
    %417 := .value (data.add 80#64),
    %418 := pairVec (readWordNative first 10) (readWordNative first 11),
    %419 := bulkVec (readWordNative first 10) (readWordNative first 11) (readWordNative second 10) (readWordNative second 11),
    %420 := bulkInitialBytes (readWordNative first 10) (readWordNative first 11) (readWordNative second 10) (readWordNative second 11),
    %421 := bulkInitialShuffle (readWordNative first 10) (readWordNative first 11) (readWordNative second 10) (readWordNative second 11),
    %422 := bulkVec (readWordBE first 10) (readWordBE first 11) (readWordBE second 10) (readWordBE second 11),
    %423 := bulkVec (readWordBE first 10+k0) (readWordBE first 11+k1) (readWordBE second 10+k0) (readWordBE second 11+k1),
    %424 := pairVec (readWordBE first 10+k0) (readWordBE first 11+k1)]
  let mem1 := pairStoreState mem scratch 5 (readWordBE first 10+k0) (readWordBE first 11+k1)
  have hprefix : List.foldlM Instr.run E ((program.bb9.body.drop 67).take 10) mem =
      .value (Epre, mem) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run, Epre,
      hp, hhigh, hlow, hk, hgHigh, hgLow, hfHigh, hfLow, hrfirst, hrsecond,
      pairVec_unflatten, -Ty.unflatten_vec,
      hshuffle, hcast, bulkVec_concat, bulkVec_add, bulkVec_lo,
      UnOp.compute, GepIndex.inboundsOffset, Operation.load,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]
    rw [bulkVec_concat]
    repeat' first
      | rw [bulkVec_concat]
      | rw [hshuffle]
      | rw [hcast]
      | rw [bulkVec_add]
      | rw [bulkVec_lo]
    rfl
  have hstoreFirst : List.foldlM Instr.run Epre ((program.bb9.body.drop 77).take 1) mem =
      .value (Epre, mem1) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      Epre, mem1, pairStoreState, pairScratchStore, hsp, hfScratch,
      pairVec_flatten, Operation.store, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, throwUBIf]
  have hhighVec : List.foldlM Instr.run Epre ((program.bb9.body.drop 78).take 1) mem1 =
      .value (bulkInitialSlice5Env E data first second k0 k1, mem1) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      Epre, bulkInitialSlice5Env, bulkVec_hi, BinOp.compute, bulkVec, pairVec, Ty.wrap_vec, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect]
  have hstoreSecond : List.foldlM Instr.run (bulkInitialSlice5Env E data first second k0 k1)
      ((program.bb9.body.drop 79).take 1) mem1 =
      .value (bulkInitialSlice5Env E data first second k0 k1,
        bulkInitialPairState mem scratch cache 5
          (readWordBE first 10+k0) (readWordBE first 11+k1) (readWordBE second 10+k0) (readWordBE second 11+k1)) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      bulkInitialSlice5Env, bulkInitialPairState, mem1, pairStoreState, pairScratchStore,
      hcp, hfCache, pairVec_flatten, Operation.store, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, throwUBIf]
  have hcut : (program.bb9.body.drop 67).take 13 =
      (program.bb9.body.drop 67).take 10 ++
      (program.bb9.body.drop 77).take 1 ++
      (program.bb9.body.drop 78).take 1 ++
      (program.bb9.body.drop 79).take 1 := by rfl
  rw [hcut]
  simp only [List.foldlM_append, EffectM.bind_eq, hprefix, LeanMLIR.RIR.PoisonOr.value_bind,
    hstoreFirst, hhighVec, hstoreSecond]

theorem bulkInitialSlice5Env_frame (E : Env program.Γ) (data : Pointer)
    (first second : Bytes) (k0 k1 : Word) :
    RegFrame 415 425 E (bulkInitialSlice5Env E data first second k0 k1) := by
  unfold bulkInitialSlice5Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

def bulkInitialSlice6Env (E : Env program.Γ) (data : Pointer) (first second : Bytes)
    (k0 k1 : Word) : Env program.Γ :=
  E[%426 := .value (data.add 224#64),
    %427 := pairVec (readWordNative second 12) (readWordNative second 13),
    %428 := .value (data.add 96#64),
    %429 := pairVec (readWordNative first 12) (readWordNative first 13),
    %430 := bulkVec (readWordNative first 12) (readWordNative first 13) (readWordNative second 12) (readWordNative second 13),
    %431 := bulkInitialBytes (readWordNative first 12) (readWordNative first 13) (readWordNative second 12) (readWordNative second 13),
    %432 := bulkInitialShuffle (readWordNative first 12) (readWordNative first 13) (readWordNative second 12) (readWordNative second 13),
    %433 := bulkVec (readWordBE first 12) (readWordBE first 13) (readWordBE second 12) (readWordBE second 13),
    %434 := bulkVec (readWordBE first 12+k0) (readWordBE first 13+k1) (readWordBE second 12+k0) (readWordBE second 13+k1),
    %435 := pairVec (readWordBE first 12+k0) (readWordBE first 13+k1),
    %436 := pairVec (readWordBE second 12+k0) (readWordBE second 13+k1)]

theorem bulk_initial_slice6_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch cache : Pointer) (first second : Bytes) (k0 k1 : Word)
    (hd : SmallRange mem.mem data 256) (hs : SmallRange mem.mem scratch 128)
    (hc : SmallRange mem.mem cache 128)
    (hp : E.read (%360) = .value data)
    (hsp : E.read (%331) = .value (scratch.add 96#64))
    (hcp : E.read (%332) = .value (cache.add 96#64))
    (hhigh : E.read (%62) = .value 224#64)
    (hlow : E.read (%19) = .value 96#64)
    (hk : E.read (%63) = bulkVec k0 k1 k0 k1)
    (hrfirst : mem.mem.readAt (data.add 96#64) 128 = readWordNative first 13 ++ readWordNative first 12)
    (hrsecond : mem.mem.readAt (data.add 224#64) 128 = readWordNative second 13 ++ readWordNative second 12) :
    List.foldlM Instr.run E ((program.bb9.body.drop 80).take 13) mem =
      .value (bulkInitialSlice6Env E data first second k0 k1,
        bulkInitialPairState mem scratch cache 6
          (readWordBE first 12+k0) (readWordBE first 13+k1) (readWordBE second 12+k0) (readWordBE second 13+k1)) := by
  have hgHigh := hd.gep (k := 224) (by decide)
  have hfHigh := hd.fits_add (k := 224) (count := 16) (by decide)
  have hfLow := hd.fits_add (k := 96) (count := 16) (by decide)
  have hfScratch := hs.fits_add (k := 96) (count := 16) (by decide)
  have hfCache := (hc.fits_add (k := 96) (count := 16) (by decide)).storeAt
    (q := scratch.add 96#64) (x := (readWordBE first 13+k1) ++ (readWordBE first 12+k0))
  have hgLow := hd.gep (k := 96) (by decide)
  norm_num only at hgHigh hgLow
  have hshuffle := bulkInitialShuffle_any (readWordNative first 12) (readWordNative first 13) (readWordNative second 12) (readWordNative second 13) (E.read (%50))
  simp only [bulkInitialMask, bulkInitialBytes] at hshuffle
  have hcast := bulkInitialWords_native first second 12 12
  unfold bulkInitialWords at hcast
  let Epre : Env program.Γ := E[%426 := .value (data.add 224#64),
    %427 := pairVec (readWordNative second 12) (readWordNative second 13),
    %428 := .value (data.add 96#64),
    %429 := pairVec (readWordNative first 12) (readWordNative first 13),
    %430 := bulkVec (readWordNative first 12) (readWordNative first 13) (readWordNative second 12) (readWordNative second 13),
    %431 := bulkInitialBytes (readWordNative first 12) (readWordNative first 13) (readWordNative second 12) (readWordNative second 13),
    %432 := bulkInitialShuffle (readWordNative first 12) (readWordNative first 13) (readWordNative second 12) (readWordNative second 13),
    %433 := bulkVec (readWordBE first 12) (readWordBE first 13) (readWordBE second 12) (readWordBE second 13),
    %434 := bulkVec (readWordBE first 12+k0) (readWordBE first 13+k1) (readWordBE second 12+k0) (readWordBE second 13+k1),
    %435 := pairVec (readWordBE first 12+k0) (readWordBE first 13+k1)]
  let mem1 := pairStoreState mem scratch 6 (readWordBE first 12+k0) (readWordBE first 13+k1)
  have hprefix : List.foldlM Instr.run E ((program.bb9.body.drop 80).take 10) mem =
      .value (Epre, mem) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run, Epre,
      hp, hhigh, hlow, hk, hgHigh, hgLow, hfHigh, hfLow, hrfirst, hrsecond,
      pairVec_unflatten, -Ty.unflatten_vec,
      hshuffle, hcast, bulkVec_concat, bulkVec_add, bulkVec_lo,
      UnOp.compute, GepIndex.inboundsOffset, Operation.load,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]
    rw [bulkVec_concat]
    repeat' first
      | rw [bulkVec_concat]
      | rw [hshuffle]
      | rw [hcast]
      | rw [bulkVec_add]
      | rw [bulkVec_lo]
    rfl
  have hstoreFirst : List.foldlM Instr.run Epre ((program.bb9.body.drop 90).take 1) mem =
      .value (Epre, mem1) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      Epre, mem1, pairStoreState, pairScratchStore, hsp, hfScratch,
      pairVec_flatten, Operation.store, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, throwUBIf]
  have hhighVec : List.foldlM Instr.run Epre ((program.bb9.body.drop 91).take 1) mem1 =
      .value (bulkInitialSlice6Env E data first second k0 k1, mem1) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      Epre, bulkInitialSlice6Env, bulkVec_hi, BinOp.compute, bulkVec, pairVec, Ty.wrap_vec, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect]
  have hstoreSecond : List.foldlM Instr.run (bulkInitialSlice6Env E data first second k0 k1)
      ((program.bb9.body.drop 92).take 1) mem1 =
      .value (bulkInitialSlice6Env E data first second k0 k1,
        bulkInitialPairState mem scratch cache 6
          (readWordBE first 12+k0) (readWordBE first 13+k1) (readWordBE second 12+k0) (readWordBE second 13+k1)) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      bulkInitialSlice6Env, bulkInitialPairState, mem1, pairStoreState, pairScratchStore,
      hcp, hfCache, pairVec_flatten, Operation.store, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, throwUBIf]
  have hcut : (program.bb9.body.drop 80).take 13 =
      (program.bb9.body.drop 80).take 10 ++
      (program.bb9.body.drop 90).take 1 ++
      (program.bb9.body.drop 91).take 1 ++
      (program.bb9.body.drop 92).take 1 := by rfl
  rw [hcut]
  simp only [List.foldlM_append, EffectM.bind_eq, hprefix, LeanMLIR.RIR.PoisonOr.value_bind,
    hstoreFirst, hhighVec, hstoreSecond]

theorem bulkInitialSlice6Env_frame (E : Env program.Γ) (data : Pointer)
    (first second : Bytes) (k0 k1 : Word) :
    RegFrame 426 436 E (bulkInitialSlice6Env E data first second k0 k1) := by
  unfold bulkInitialSlice6Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

def bulkInitialSlice7Env (E : Env program.Γ) (data : Pointer) (first second : Bytes)
    (k0 k1 : Word) : Env program.Γ :=
  E[%437 := .value (data.add 240#64),
    %438 := pairVec (readWordNative second 14) (readWordNative second 15),
    %439 := .value (data.add 112#64),
    %440 := pairVec (readWordNative first 14) (readWordNative first 15),
    %441 := bulkVec (readWordNative first 14) (readWordNative first 15) (readWordNative second 14) (readWordNative second 15),
    %442 := bulkInitialBytes (readWordNative first 14) (readWordNative first 15) (readWordNative second 14) (readWordNative second 15),
    %443 := bulkInitialShuffle (readWordNative first 14) (readWordNative first 15) (readWordNative second 14) (readWordNative second 15),
    %444 := bulkVec (readWordBE first 14) (readWordBE first 15) (readWordBE second 14) (readWordBE second 15),
    %445 := bulkVec (readWordBE first 14+k0) (readWordBE first 15+k1) (readWordBE second 14+k0) (readWordBE second 15+k1),
    %446 := pairVec (readWordBE first 14+k0) (readWordBE first 15+k1),
    %447 := pairVec (readWordBE second 14+k0) (readWordBE second 15+k1)]

theorem bulk_initial_slice7_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch cache : Pointer) (first second : Bytes) (k0 k1 : Word)
    (hd : SmallRange mem.mem data 256) (hs : SmallRange mem.mem scratch 128)
    (hc : SmallRange mem.mem cache 128)
    (hp : E.read (%360) = .value data)
    (hsp : E.read (%333) = .value (scratch.add 112#64))
    (hcp : E.read (%334) = .value (cache.add 112#64))
    (hhigh : E.read (%64) = .value 240#64)
    (hlow : E.read (%21) = .value 112#64)
    (hk : E.read (%65) = bulkVec k0 k1 k0 k1)
    (hrfirst : mem.mem.readAt (data.add 112#64) 128 = readWordNative first 15 ++ readWordNative first 14)
    (hrsecond : mem.mem.readAt (data.add 240#64) 128 = readWordNative second 15 ++ readWordNative second 14) :
    List.foldlM Instr.run E ((program.bb9.body.drop 93).take 13) mem =
      .value (bulkInitialSlice7Env E data first second k0 k1,
        bulkInitialPairState mem scratch cache 7
          (readWordBE first 14+k0) (readWordBE first 15+k1) (readWordBE second 14+k0) (readWordBE second 15+k1)) := by
  have hgHigh := hd.gep (k := 240) (by decide)
  have hfHigh := hd.fits_add (k := 240) (count := 16) (by decide)
  have hfLow := hd.fits_add (k := 112) (count := 16) (by decide)
  have hfScratch := hs.fits_add (k := 112) (count := 16) (by decide)
  have hfCache := (hc.fits_add (k := 112) (count := 16) (by decide)).storeAt
    (q := scratch.add 112#64) (x := (readWordBE first 15+k1) ++ (readWordBE first 14+k0))
  have hgLow := hd.gep (k := 112) (by decide)
  norm_num only at hgHigh hgLow
  have hshuffle := bulkInitialShuffle_any (readWordNative first 14) (readWordNative first 15) (readWordNative second 14) (readWordNative second 15) (E.read (%50))
  simp only [bulkInitialMask, bulkInitialBytes] at hshuffle
  have hcast := bulkInitialWords_native first second 14 14
  unfold bulkInitialWords at hcast
  let Epre : Env program.Γ := E[%437 := .value (data.add 240#64),
    %438 := pairVec (readWordNative second 14) (readWordNative second 15),
    %439 := .value (data.add 112#64),
    %440 := pairVec (readWordNative first 14) (readWordNative first 15),
    %441 := bulkVec (readWordNative first 14) (readWordNative first 15) (readWordNative second 14) (readWordNative second 15),
    %442 := bulkInitialBytes (readWordNative first 14) (readWordNative first 15) (readWordNative second 14) (readWordNative second 15),
    %443 := bulkInitialShuffle (readWordNative first 14) (readWordNative first 15) (readWordNative second 14) (readWordNative second 15),
    %444 := bulkVec (readWordBE first 14) (readWordBE first 15) (readWordBE second 14) (readWordBE second 15),
    %445 := bulkVec (readWordBE first 14+k0) (readWordBE first 15+k1) (readWordBE second 14+k0) (readWordBE second 15+k1),
    %446 := pairVec (readWordBE first 14+k0) (readWordBE first 15+k1)]
  let mem1 := pairStoreState mem scratch 7 (readWordBE first 14+k0) (readWordBE first 15+k1)
  have hprefix : List.foldlM Instr.run E ((program.bb9.body.drop 93).take 10) mem =
      .value (Epre, mem) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run, Epre,
      hp, hhigh, hlow, hk, hgHigh, hgLow, hfHigh, hfLow, hrfirst, hrsecond,
      pairVec_unflatten, -Ty.unflatten_vec,
      hshuffle, hcast, bulkVec_concat, bulkVec_add, bulkVec_lo,
      UnOp.compute, GepIndex.inboundsOffset, Operation.load,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]
    rw [bulkVec_concat]
    repeat' first
      | rw [bulkVec_concat]
      | rw [hshuffle]
      | rw [hcast]
      | rw [bulkVec_add]
      | rw [bulkVec_lo]
    rfl
  have hstoreFirst : List.foldlM Instr.run Epre ((program.bb9.body.drop 103).take 1) mem =
      .value (Epre, mem1) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      Epre, mem1, pairStoreState, pairScratchStore, hsp, hfScratch,
      pairVec_flatten, Operation.store, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, throwUBIf]
  have hhighVec : List.foldlM Instr.run Epre ((program.bb9.body.drop 104).take 1) mem1 =
      .value (bulkInitialSlice7Env E data first second k0 k1, mem1) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      Epre, bulkInitialSlice7Env, bulkVec_hi, BinOp.compute, bulkVec, pairVec, Ty.wrap_vec, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect]
  have hstoreSecond : List.foldlM Instr.run (bulkInitialSlice7Env E data first second k0 k1)
      ((program.bb9.body.drop 105).take 1) mem1 =
      .value (bulkInitialSlice7Env E data first second k0 k1,
        bulkInitialPairState mem scratch cache 7
          (readWordBE first 14+k0) (readWordBE first 15+k1) (readWordBE second 14+k0) (readWordBE second 15+k1)) := by
    simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run,
      bulkInitialSlice7Env, bulkInitialPairState, mem1, pairStoreState, pairScratchStore,
      hcp, hfCache, pairVec_flatten, Operation.store, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, throwUBIf]
  have hcut : (program.bb9.body.drop 93).take 13 =
      (program.bb9.body.drop 93).take 10 ++
      (program.bb9.body.drop 103).take 1 ++
      (program.bb9.body.drop 104).take 1 ++
      (program.bb9.body.drop 105).take 1 := by rfl
  rw [hcut]
  simp only [List.foldlM_append, EffectM.bind_eq, hprefix, LeanMLIR.RIR.PoisonOr.value_bind,
    hstoreFirst, hhighVec, hstoreSecond]

theorem bulkInitialSlice7Env_frame (E : Env program.Γ) (data : Pointer)
    (first second : Bytes) (k0 k1 : Word) :
    RegFrame 437 447 E (bulkInitialSlice7Env E data first second k0 k1) := by
  unfold bulkInitialSlice7Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

end Agave.Ed25519.SHA512.Execution.Avx2
