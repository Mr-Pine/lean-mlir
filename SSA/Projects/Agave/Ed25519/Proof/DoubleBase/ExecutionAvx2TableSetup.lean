import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2ContractDefs
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2NAFFrame
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

/-! Execute the original table-construction/identity-entry block. The sole
callee premise is the width-five table constructor's ordinary contract.
All eighty-four inbounds addresses follow from the twenty-one live scratch
objects; the chosen scan index and the exact packed identity are retained. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR
open NAF.Memory (Buffer)
open Reduce64.Execution (SmallRange)
open Conformance.BackendExecution (readPoint)
set_option maxRecDepth 10000

/-- Pointer slots are in the order first used by block 15. -/
abbrev SetupSlots := Fin 21 → Pointer

def tableSetupInput (E : ⟪avx2Kernel.Γ⟫) (slots : SetupSlots)
    (table : Pointer) (pos : Fin 256) : ⟪avx2Kernel.Γ⟫ :=
  E[
    %3 := .value 32#64,
    %20 := .value 64#64,
    %21 := .value 96#64,
    %22 := .value 128#64,
    %24 := Vector.replicate 8 (.value 0#32),
    %25 := #v[.value 0#32, .value 1#32, .value 0#32, .value 0#32,
      .value 1#32, .value 0#32, .value 0#32, .value 0#32],
    %256 := .value (slots 0),
    %255 := .value (slots 1),
    %263 := .value (slots 2),
    %249 := .value (slots 3),
    %247 := .value (slots 4),
    %246 := .value (slots 5),
    %262 := .value (slots 6),
    %254 := .value (slots 7),
    %253 := .value (slots 8),
    %251 := .value (slots 9),
    %250 := .value (slots 10),
    %261 := .value (slots 11),
    %240 := .value (slots 12),
    %238 := .value (slots 13),
    %237 := .value (slots 14),
    %260 := .value (slots 15),
    %245 := .value (slots 16),
    %244 := .value (slots 17),
    %242 := .value (slots 18),
    %241 := .value (slots 19),
    %259 := .value (slots 20),
    %264 := .value table,
    %412 := .value (BitVec.ofNat 64 pos.val)]

def tableSetupResult (E : ⟪avx2Kernel.Γ⟫) (slots : SetupSlots)
    (table : Pointer) (pos : Fin 256) : ⟪avx2Kernel.Γ⟫ :=
  (tableSetupInput E slots table pos)[
    %327 := .value ((slots 0).add 32#64),
    %328 := .value ((slots 0).add 64#64),
    %329 := .value ((slots 0).add 96#64),
    %330 := .value ((slots 0).add 128#64),
    %331 := .value ((slots 1).add 32#64),
    %332 := .value ((slots 1).add 64#64),
    %333 := .value ((slots 1).add 96#64),
    %334 := .value ((slots 1).add 128#64),
    %335 := .value ((slots 2).add 32#64),
    %336 := .value ((slots 2).add 64#64),
    %337 := .value ((slots 2).add 96#64),
    %338 := .value ((slots 2).add 128#64),
    %339 := .value ((slots 3).add 32#64),
    %340 := .value ((slots 3).add 64#64),
    %341 := .value ((slots 3).add 96#64),
    %342 := .value ((slots 3).add 128#64),
    %343 := .value ((slots 4).add 32#64),
    %344 := .value ((slots 4).add 64#64),
    %345 := .value ((slots 4).add 96#64),
    %346 := .value ((slots 4).add 128#64),
    %347 := .value ((slots 5).add 32#64),
    %348 := .value ((slots 5).add 64#64),
    %349 := .value ((slots 5).add 96#64),
    %350 := .value ((slots 5).add 128#64),
    %351 := .value ((slots 6).add 32#64),
    %352 := .value ((slots 6).add 64#64),
    %353 := .value ((slots 6).add 96#64),
    %354 := .value ((slots 6).add 128#64),
    %355 := .value ((slots 7).add 32#64),
    %356 := .value ((slots 7).add 64#64),
    %357 := .value ((slots 7).add 96#64),
    %358 := .value ((slots 7).add 128#64),
    %359 := .value ((slots 8).add 32#64),
    %360 := .value ((slots 8).add 64#64),
    %361 := .value ((slots 8).add 96#64),
    %362 := .value ((slots 8).add 128#64),
    %363 := .value ((slots 9).add 32#64),
    %364 := .value ((slots 9).add 64#64),
    %365 := .value ((slots 9).add 96#64),
    %366 := .value ((slots 9).add 128#64),
    %367 := .value ((slots 10).add 32#64),
    %368 := .value ((slots 10).add 64#64),
    %369 := .value ((slots 10).add 96#64),
    %370 := .value ((slots 10).add 128#64),
    %371 := .value ((slots 11).add 32#64),
    %372 := .value ((slots 11).add 64#64),
    %373 := .value ((slots 11).add 96#64),
    %374 := .value ((slots 11).add 128#64),
    %375 := .value ((slots 12).add 32#64),
    %376 := .value ((slots 12).add 64#64),
    %377 := .value ((slots 12).add 96#64),
    %378 := .value ((slots 12).add 128#64),
    %379 := .value ((slots 13).add 32#64),
    %380 := .value ((slots 13).add 64#64),
    %381 := .value ((slots 13).add 96#64),
    %382 := .value ((slots 13).add 128#64),
    %383 := .value ((slots 14).add 32#64),
    %384 := .value ((slots 14).add 64#64),
    %385 := .value ((slots 14).add 96#64),
    %386 := .value ((slots 14).add 128#64),
    %387 := .value ((slots 15).add 32#64),
    %388 := .value ((slots 15).add 64#64),
    %389 := .value ((slots 15).add 96#64),
    %390 := .value ((slots 15).add 128#64),
    %391 := .value ((slots 16).add 32#64),
    %392 := .value ((slots 16).add 64#64),
    %393 := .value ((slots 16).add 96#64),
    %394 := .value ((slots 16).add 128#64),
    %395 := .value ((slots 17).add 32#64),
    %396 := .value ((slots 17).add 64#64),
    %397 := .value ((slots 17).add 96#64),
    %398 := .value ((slots 17).add 128#64),
    %399 := .value ((slots 18).add 32#64),
    %400 := .value ((slots 18).add 64#64),
    %401 := .value ((slots 18).add 96#64),
    %402 := .value ((slots 18).add 128#64),
    %403 := .value ((slots 19).add 32#64),
    %404 := .value ((slots 19).add 64#64),
    %405 := .value ((slots 19).add 96#64),
    %406 := .value ((slots 19).add 128#64),
    %407 := .value ((slots 20).add 32#64),
    %408 := .value ((slots 20).add 64#64),
    %409 := .value ((slots 20).add 96#64),
    %410 := .value ((slots 20).add 128#64),
    %421 := Vector.replicate 8 (.value 0#32),
    %422 := Vector.replicate 8 (.value 0#32),
    %423 := Vector.replicate 8 (.value 0#32),
    %424 := #v[.value 0#32, .value 1#32, .value 0#32, .value 0#32,
      .value 1#32, .value 0#32, .value 0#32, .value 0#32],
    %425 := Vector.replicate 8 (.value 0#32),
    %426 := .value (BitVec.ofNat 64 pos.val)]

/-- The adapter only restates the concrete live-in register values. -/
def TableSetupReady (E : ⟪avx2Kernel.Γ⟫) (slots : SetupSlots)
    (table : Pointer) (pos : Fin 256) : Prop :=
  E ⊨ [
    %3 := .value 32#64,
    %20 := .value 64#64,
    %21 := .value 96#64,
    %22 := .value 128#64,
    %24 := Vector.replicate 8 (.value 0#32),
    %25 := #v[.value 0#32, .value 1#32, .value 0#32, .value 0#32,
      .value 1#32, .value 0#32, .value 0#32, .value 0#32],
    %256 := .value (slots 0),
    %255 := .value (slots 1),
    %263 := .value (slots 2),
    %249 := .value (slots 3),
    %247 := .value (slots 4),
    %246 := .value (slots 5),
    %262 := .value (slots 6),
    %254 := .value (slots 7),
    %253 := .value (slots 8),
    %251 := .value (slots 9),
    %250 := .value (slots 10),
    %261 := .value (slots 11),
    %240 := .value (slots 12),
    %238 := .value (slots 13),
    %237 := .value (slots 14),
    %260 := .value (slots 15),
    %245 := .value (slots 16),
    %244 := .value (slots 17),
    %242 := .value (slots 18),
    %241 := .value (slots 19),
    %259 := .value (slots 20),
    %264 := .value table,
    %412 := .value (BitVec.ofNat 64 pos.val)]

theorem tableSetupInput_of_ready (E : ⟪avx2Kernel.Γ⟫) (slots : SetupSlots)
    (table : Pointer) (pos : Fin 256) (h : TableSetupReady E slots table pos) :
    tableSetupInput E slots table pos = E := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  unfold tableSetupInput
  rw [Env.write_of_read E (%3) h0,
    Env.write_of_read E (%20) h1,
    Env.write_of_read E (%21) h2,
    Env.write_of_read E (%22) h3,
    Env.write_of_read E (%24) h4,
    Env.write_of_read E (%25) h5,
    Env.write_of_read E (%256) h6,
    Env.write_of_read E (%255) h7,
    Env.write_of_read E (%263) h8,
    Env.write_of_read E (%249) h9,
    Env.write_of_read E (%247) h10,
    Env.write_of_read E (%246) h11,
    Env.write_of_read E (%262) h12,
    Env.write_of_read E (%254) h13,
    Env.write_of_read E (%253) h14,
    Env.write_of_read E (%251) h15,
    Env.write_of_read E (%250) h16,
    Env.write_of_read E (%261) h17,
    Env.write_of_read E (%240) h18,
    Env.write_of_read E (%238) h19,
    Env.write_of_read E (%237) h20,
    Env.write_of_read E (%260) h21,
    Env.write_of_read E (%245) h22,
    Env.write_of_read E (%244) h23,
    Env.write_of_read E (%242) h24,
    Env.write_of_read E (%241) h25,
    Env.write_of_read E (%259) h26,
    Env.write_of_read E (%264) h27,
    Env.write_of_read E (%412) h28]

set_option maxHeartbeats 2000000 in
/-- Local execution before imposing any table-value interpretation. -/
theorem table_setup_block (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (slots : SetupSlots) (table input : Pointer) (pos : Fin 256)
    (s s' : GlobalState) (harg : E.args 2 = .value input)
    (hcall : p.call0 (args2 table input) s = .value (.nil, s'))
    (hslots : ∀ i, Buffer s'.mem (slots i) 160) :
    (avx2Kernel.bb15 p).run avx2Kernel.blockParams (tableSetupInput E slots table pos) s =
      .value ((tableSetupResult E slots table pos, .inr 18), s') := by
  generalize hS : s = S
  symm at hS
  generalize hE : tableSetupInput E slots table pos = E'
  symm at hE
  have hEargs : E'.args = E.args := by
    simp only [hE, tableSetupInput, Env.write_args]
  unfold tableSetupInput at hE
  rw [BasicBlock.run_eq]
  simp only [EffectM.bind_eq]
  step_pure
  step_impure =>
    apply run_call
    simpa [hS, hEargs, harg, args2] using hcall
  have hgep32 (i : Fin 21) := (hslots i).gep 32 (by decide)
  have hgep64 (i : Fin 21) := (hslots i).gep 64 (by decide)
  have hgep96 (i : Fin 21) := (hslots i).gep 96 (by decide)
  have hgep128 (i : Fin 21) := (hslots i).gep 128 (by decide)
  simp only [Int.cast_ofNat_Int, ← hS] at hgep32 hgep64 hgep96 hgep128
  iterate 21
    step_reduce_gep [hgep32, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
      Operation.GepSignedRange]
    step_reduce_gep [hgep64, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
      Operation.GepSignedRange]
    step_reduce_gep [hgep96, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
      Operation.GepSignedRange]
    step_reduce_gep [hgep128, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
      Operation.GepSignedRange]
  rw [BasicBlock.runBodyFrom_done (Nat.le_of_ble_eq_true rfl)]
  simp only [EffectM.pure_eq, PoisonOr.value_bind]
  simp [avx2Kernel.bb15, Exit.run, Jump.run, avx2Kernel.blockParams, hE, hS,
    tableSetupResult, tableSetupInput, mlir_env]

/-- The original successor is reached with the actual cached table and every
caller frame fact provided by the constructor contract. No property of a point
addition, doubling, the ladder, or the full function is assumed here. -/
theorem table_setup_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (htable : TableContract p.call0) (E : ⟪avx2Kernel.Γ⟫)
    (slots : SetupSlots) (table input : Pointer) (pos : Fin 256)
    (s : GlobalState) (hwf : s.WF) (harg : E.args 2 = .value input)
    (hr : SmallRange s.mem table 1280) (ha : SmallRange s.mem input 160)
    (hdisjoint : (Range.of table (1280 * 8)).Disjoint (Range.of input (160 * 8)))
    (hlimbs : serialLimbsBounded s input)
    (hslots : ∀ i, Buffer s.mem (slots i) 160) :
    ∃ s' : GlobalState,
      (avx2Kernel p g).runFrom (tableSetupInput E slots table pos) 15 s =
        (avx2Kernel p g).runFrom (tableSetupResult E slots table pos) 18 s' ∧
      TableFrame s s' table ∧
      ∀ k : Fin 8,
        let point := packedPoint s'.mem (table.add (BitVec.ofNat 64 (160 * k.val)))
        Avx2PointAdd.pointReduced point ∧
        Avx2PointAdd.pointValue point =
          PointArithmetic.avx2Cache (Tables.avx2Width5 (readPoint s input) k) := by
  obtain ⟨s', hcall, hframe, hvalues⟩ :=
    htable table input s hwf hr ha hdisjoint hlimbs
  refine ⟨s', ?_, hframe, hvalues⟩
  have hslots' : ∀ i, Buffer s'.mem (slots i) 160 :=
    fun i => hframe.live (slots i) 160 (hslots i)
  rw [Func.runFrom_eq,
    show (avx2Kernel p g).blocks 15 = avx2Kernel.bb15 p from rfl,
    table_setup_block p E slots table input pos s s' harg hcall hslots']
  rfl

end Agave.Ed25519.DoubleBase.ExecutionAvx2
