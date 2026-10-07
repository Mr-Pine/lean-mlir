import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ConditionalSubtract
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Startup
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Memory

/-! Actual scalar serialization instructions 443–512 and byte packing identity. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def serializedBytes (words : Fin 5 → BitVec 64) : Fin 32 → BitVec 8 :=
  ![(words 0).setWidth 8,
    ((words 0) >>> 8).setWidth 8,
    ((words 0) >>> 16).setWidth 8,
    ((words 0) >>> 24).setWidth 8,
    ((words 0) >>> 32).setWidth 8,
    ((words 0) >>> 40).setWidth 8,
    (((words 1) <<< 4) ||| ((words 0) >>> 48)).setWidth 8,
    ((words 1) >>> 4).setWidth 8,
    ((words 1) >>> 12).setWidth 8,
    ((words 1) >>> 20).setWidth 8,
    ((words 1) >>> 28).setWidth 8,
    ((words 1) >>> 36).setWidth 8,
    ((words 1) >>> 44).setWidth 8,
    (words 2).setWidth 8,
    ((words 2) >>> 8).setWidth 8,
    ((words 2) >>> 16).setWidth 8,
    ((words 2) >>> 24).setWidth 8,
    ((words 2) >>> 32).setWidth 8,
    ((words 2) >>> 40).setWidth 8,
    (((words 3) <<< 4) ||| ((words 2) >>> 48)).setWidth 8,
    ((words 3) >>> 4).setWidth 8,
    ((words 3) >>> 12).setWidth 8,
    ((words 3) >>> 20).setWidth 8,
    ((words 3) >>> 28).setWidth 8,
    ((words 3) >>> 36).setWidth 8,
    ((words 3) >>> 44).setWidth 8,
    (words 4).setWidth 8,
    ((words 4) >>> 8).setWidth 8,
    ((words 4) >>> 16).setWidth 8,
    ((words 4) >>> 24).setWidth 8,
    ((words 4) >>> 32).setWidth 8,
    ((words 4) >>> 40).setWidth 8]

def serializeEnv (E : Env program.Γ) (words : Fin 5 → BitVec 64) : Env program.Γ :=
  let v355 : BitVec 64 := words 0
  let v356 : BitVec 8 := v355.setWidth 8
  let v357 : BitVec 64 := v355 >>> 8
  let v358 : BitVec 8 := v357.setWidth 8
  let v359 : BitVec 64 := v355 >>> 16
  let v360 : BitVec 8 := v359.setWidth 8
  let v361 : BitVec 64 := v355 >>> 24
  let v362 : BitVec 8 := v361.setWidth 8
  let v363 : BitVec 64 := v355 >>> 32
  let v364 : BitVec 8 := v363.setWidth 8
  let v365 : BitVec 64 := v355 >>> 40
  let v366 : BitVec 8 := v365.setWidth 8
  let v367 : BitVec 64 := v355 >>> 48
  let v368 : BitVec 64 := words 1
  let v369 : BitVec 64 := v368 <<< 4
  let v370 : BitVec 64 := v369 ||| v367
  let v371 : BitVec 8 := v370.setWidth 8
  let v372 : BitVec 64 := v368 >>> 4
  let v373 : BitVec 8 := v372.setWidth 8
  let v374 : BitVec 64 := v368 >>> 12
  let v375 : BitVec 8 := v374.setWidth 8
  let v376 : BitVec 64 := v368 >>> 20
  let v377 : BitVec 8 := v376.setWidth 8
  let v378 : BitVec 64 := v368 >>> 28
  let v379 : BitVec 8 := v378.setWidth 8
  let v380 : BitVec 64 := v368 >>> 36
  let v381 : BitVec 8 := v380.setWidth 8
  let v382 : BitVec 64 := v368 >>> 44
  let v383 : BitVec 8 := v382.setWidth 8
  let v384 : BitVec 64 := words 2
  let v385 : BitVec 8 := v384.setWidth 8
  let v386 : BitVec 64 := v384 >>> 8
  let v387 : BitVec 8 := v386.setWidth 8
  let v388 : BitVec 64 := v384 >>> 16
  let v389 : BitVec 8 := v388.setWidth 8
  let v390 : BitVec 64 := v384 >>> 24
  let v391 : BitVec 8 := v390.setWidth 8
  let v392 : BitVec 64 := v384 >>> 32
  let v393 : BitVec 8 := v392.setWidth 8
  let v394 : BitVec 64 := v384 >>> 40
  let v395 : BitVec 8 := v394.setWidth 8
  let v396 : BitVec 64 := v384 >>> 48
  let v397 : BitVec 64 := words 3
  let v398 : BitVec 64 := v397 <<< 4
  let v399 : BitVec 64 := v398 ||| v396
  let v400 : BitVec 8 := v399.setWidth 8
  let v401 : BitVec 64 := v397 >>> 4
  let v402 : BitVec 8 := v401.setWidth 8
  let v403 : BitVec 64 := v397 >>> 12
  let v404 : BitVec 8 := v403.setWidth 8
  let v405 : BitVec 64 := v397 >>> 20
  let v406 : BitVec 8 := v405.setWidth 8
  let v407 : BitVec 64 := v397 >>> 28
  let v408 : BitVec 8 := v407.setWidth 8
  let v409 : BitVec 64 := v397 >>> 36
  let v410 : BitVec 8 := v409.setWidth 8
  let v411 : BitVec 64 := v397 >>> 44
  let v412 : BitVec 8 := v411.setWidth 8
  let v413 : BitVec 64 := words 4
  let v414 : BitVec 8 := v413.setWidth 8
  let v415 : BitVec 64 := v413 >>> 8
  let v416 : BitVec 8 := v415.setWidth 8
  let v417 : BitVec 64 := v413 >>> 16
  let v418 : BitVec 8 := v417.setWidth 8
  let v419 : BitVec 64 := v413 >>> 24
  let v420 : BitVec 8 := v419.setWidth 8
  let v421 : BitVec 64 := v413 >>> 32
  let v422 : BitVec 8 := v421.setWidth 8
  let v423 : BitVec 64 := v413 >>> 40
  let v424 : BitVec 8 := v423.setWidth 8
  E[%355 := .value v355,
    %356 := .value v356,
    %357 := .value v357,
    %358 := .value v358,
    %359 := .value v359,
    %360 := .value v360,
    %361 := .value v361,
    %362 := .value v362,
    %363 := .value v363,
    %364 := .value v364,
    %365 := .value v365,
    %366 := .value v366,
    %367 := .value v367,
    %368 := .value v368,
    %369 := .value v369,
    %370 := .value v370,
    %371 := .value v371,
    %372 := .value v372,
    %373 := .value v373,
    %374 := .value v374,
    %375 := .value v375,
    %376 := .value v376,
    %377 := .value v377,
    %378 := .value v378,
    %379 := .value v379,
    %380 := .value v380,
    %381 := .value v381,
    %382 := .value v382,
    %383 := .value v383,
    %384 := .value v384,
    %385 := .value v385,
    %386 := .value v386,
    %387 := .value v387,
    %388 := .value v388,
    %389 := .value v389,
    %390 := .value v390,
    %391 := .value v391,
    %392 := .value v392,
    %393 := .value v393,
    %394 := .value v394,
    %395 := .value v395,
    %396 := .value v396,
    %397 := .value v397,
    %398 := .value v398,
    %399 := .value v399,
    %400 := .value v400,
    %401 := .value v401,
    %402 := .value v402,
    %403 := .value v403,
    %404 := .value v404,
    %405 := .value v405,
    %406 := .value v406,
    %407 := .value v407,
    %408 := .value v408,
    %409 := .value v409,
    %410 := .value v410,
    %411 := .value v411,
    %412 := .value v412,
    %413 := .value v413,
    %414 := .value v414,
    %415 := .value v415,
    %416 := .value v416,
    %417 := .value v417,
    %418 := .value v418,
    %419 := .value v419,
    %420 := .value v420,
    %421 := .value v421,
    %422 := .value v422,
    %423 := .value v423,
    %424 := .value v424]

theorem serialize_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (words : Fin 5 → BitVec 64) (slots : Fin 5 → Pointer)
    (hlive : ∀ i, Fits state.mem (slots i) 64)
    (hread : ∀ i, state.mem.readAt (slots i) 64 = words i)
    (hs0 : E.read (%84) = .value (slots 0))
    (hs1 : E.read (%85) = .value (slots 1))
    (hs2 : E.read (%86) = .value (slots 2))
    (hs3 : E.read (%87) = .value (slots 3))
    (hs4 : E.read (%88) = .value (slots 4))
    (hc1 : E.read (%1) = .value 4#64)
    (hc2 : E.read (%2) = .value 32#64)
    (hc4 : E.read (%4) = .value 40#64)
    (hc6 : E.read (%6) = .value 48#64)
    (hc9 : E.read (%9) = .value 8#64)
    (hc10 : E.read (%10) = .value 12#64)
    (hc13 : E.read (%13) = .value 16#64)
    (hc16 : E.read (%16) = .value 24#64)
    (hc17 : E.read (%17) = .value 20#64)
    (hc21 : E.read (%21) = .value 28#64)
    (hc25 : E.read (%25) = .value 36#64)
    (hc27 : E.read (%27) = .value 44#64)
    : List.foldlM Instr.run E (((program.entry p g).body.drop 443).take 70) state =
      .value (serializeEnv E words, state) := by
  have hf0 := hlive 0
  have hr0 := hread 0
  have hf1 := hlive 1
  have hr1 := hread 1
  have hf2 := hlive 2
  have hr2 := hread 2
  have hf3 := hlive 3
  have hr3 := hread 3
  have hf4 := hlive 4
  have hr4 := hread 4
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run, serializeEnv,
    Operation.load, Operation.trunc, Operation.shl, Operation.lshr, Operation.or, UnOp.compute, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf,
    hc1, hc2, hc4, hc6, hc9, hc10, hc13, hc16, hc17, hc21, hc25, hc27, hs0, hs1, hs2, hs3, hs4, hf0, hf1, hf2, hf3, hf4, hr0, hr1, hr2, hr3, hr4]

/-- All 32 emitted bytes are the little-endian low 256 bits of radix-52 packing. -/
theorem serializedBytes_packed (x : Fin 5 → BitVec 52) (byte : Fin 32) :
    serializedBytes (fun i => (x i).setWidth 64) byte =
      ((Subtraction.packed (x 0) (x 1) (x 2) (x 3) (x 4)).setWidth 256).extractLsb'
        (8 * byte.val) 8 := by
  fin_cases byte <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  all_goals interval_cases i <;>
    simp [serializedBytes, Subtraction.packed, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_or, BitVec.getLsbD_append]
  all_goals repeat (rw [BitVec.getElem_append]; norm_num)

end Agave.Ed25519.Verifier.Execution.ScalarWide
