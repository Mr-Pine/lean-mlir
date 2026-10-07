import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.MachineArithmetic3
import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.Registers

namespace Firedancer.Common.ScalarArithmetic.MachineArithmetic
open LeanMLIR SLLVM
open InstCombine (LLVM)
open R43x6 (FitsLong)
open IntegerRegisters

set_option maxHeartbeats 2000000

theorem value367 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r367 digest = val (z367 d) := by
  rw [Registers.r367, value361 digest d hd hm, Registers.r3]
  have ha := z361_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z367]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value368 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r368 digest = val (z368 d) := by
  rw [Registers.r368, value362 digest d hd hm, value300 digest d hd hm]
  have ha := z362_fits d hd
  have hb := z300_fits d hd
  have hr := z368_fits d hd
  rw [z368] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value369 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r369 digest = val (z369 d) := by
  rw [Registers.r369, value368 digest d hd hm, value338 digest d hd hm]
  have ha := z368_fits d hd
  have hb := z338_fits d hd
  have hr := z369_fits d hd
  rw [z369] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value370 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r370 digest = val (z370 d) := by
  rw [Registers.r370, value369 digest d hd hm, value367 digest d hd hm]
  have ha := z369_fits d hd
  have hb := z367_fits d hd
  have hr := z370_fits d hd
  rw [z370] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value371 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r371 digest = val (z371 d) := by
  rw [Registers.r371, value361 digest d hd hm, Registers.r2]
  have ha := z361_fits d hd
  have hb : FitsLong (2097151 : Int) := by norm_num [FitsLong]
  rw [z371]
  exact and_mask_ofInt (k := 21) (by decide)

theorem value372 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r372 digest = val (z372 d) := by
  rw [Registers.r372, value370 digest d hd hm, Registers.r3]
  have ha := z370_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z372]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value373 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r373 digest = val (z373 d) := by
  rw [Registers.r373, value307 digest d hd hm, value363 digest d hd hm]
  have ha := z307_fits d hd
  have hb := z363_fits d hd
  have hr := z373_fits d hd
  rw [z373] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value374 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r374 digest = val (z374 d) := by
  rw [Registers.r374, value373 digest d hd hm, value337 digest d hd hm]
  have ha := z373_fits d hd
  have hb := z337_fits d hd
  have hr := z374_fits d hd
  rw [z374] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value375 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r375 digest = val (z375 d) := by
  rw [Registers.r375, value374 digest d hd hm, value372 digest d hd hm]
  have ha := z374_fits d hd
  have hb := z372_fits d hd
  have hr := z375_fits d hd
  rw [z375] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value376 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r376 digest = val (z376 d) := by
  rw [Registers.r376, value370 digest d hd hm, Registers.r2]
  have ha := z370_fits d hd
  have hb : FitsLong (2097151 : Int) := by norm_num [FitsLong]
  rw [z376]
  exact and_mask_ofInt (k := 21) (by decide)

theorem value377 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r377 digest = val (z377 d) := by
  rw [Registers.r377, value375 digest d hd hm, Registers.r3]
  have ha := z375_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z377]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value378 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r378 digest = val (z378 d) := by
  rw [Registers.r378, value305 digest d hd hm, value364 digest d hd hm]
  have ha := z305_fits d hd
  have hb := z364_fits d hd
  have hr := z378_fits d hd
  rw [z378] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value379 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r379 digest = val (z379 d) := by
  rw [Registers.r379, value378 digest d hd hm, value341 digest d hd hm]
  have ha := z378_fits d hd
  have hb := z341_fits d hd
  have hr := z379_fits d hd
  rw [z379] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value380 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r380 digest = val (z380 d) := by
  rw [Registers.r380, value379 digest d hd hm, value377 digest d hd hm]
  have ha := z379_fits d hd
  have hb := z377_fits d hd
  have hr := z380_fits d hd
  rw [z380] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value381 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r381 digest = val (z381 d) := by
  rw [Registers.r381, value375 digest d hd hm, Registers.r2]
  have ha := z375_fits d hd
  have hb : FitsLong (2097151 : Int) := by norm_num [FitsLong]
  rw [z381]
  exact and_mask_ofInt (k := 21) (by decide)

theorem value382 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r382 digest = val (z382 d) := by
  rw [Registers.r382, value380 digest d hd hm, Registers.r3]
  have ha := z380_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z382]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value383 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r383 digest = val (z383 d) := by
  rw [Registers.r383, value312 digest d hd hm, value365 digest d hd hm]
  have ha := z312_fits d hd
  have hb := z365_fits d hd
  have hr := z383_fits d hd
  rw [z383] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value384 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r384 digest = val (z384 d) := by
  rw [Registers.r384, value383 digest d hd hm, value340 digest d hd hm]
  have ha := z383_fits d hd
  have hb := z340_fits d hd
  have hr := z384_fits d hd
  rw [z384] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value385 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r385 digest = val (z385 d) := by
  rw [Registers.r385, value384 digest d hd hm, value382 digest d hd hm]
  have ha := z384_fits d hd
  have hb := z382_fits d hd
  have hr := z385_fits d hd
  rw [z385] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value386 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r386 digest = val (z386 d) := by
  rw [Registers.r386, value380 digest d hd hm, Registers.r2]
  have ha := z380_fits d hd
  have hb : FitsLong (2097151 : Int) := by norm_num [FitsLong]
  rw [z386]
  exact and_mask_ofInt (k := 21) (by decide)

theorem value387 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r387 digest = val (z387 d) := by
  rw [Registers.r387, value385 digest d hd hm, Registers.r3]
  have ha := z385_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z387]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value388 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r388 digest = val (z388 d) := by
  rw [Registers.r388, value310 digest d hd hm, value366 digest d hd hm]
  have ha := z310_fits d hd
  have hb := z366_fits d hd
  have hr := z388_fits d hd
  rw [z388] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value389 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r389 digest = val (z389 d) := by
  rw [Registers.r389, value388 digest d hd hm, value345 digest d hd hm]
  have ha := z388_fits d hd
  have hb := z345_fits d hd
  have hr := z389_fits d hd
  rw [z389] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value390 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r390 digest = val (z390 d) := by
  rw [Registers.r390, value389 digest d hd hm, value387 digest d hd hm]
  have ha := z389_fits d hd
  have hb := z387_fits d hd
  have hr := z390_fits d hd
  rw [z390] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value391 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r391 digest = val (z391 d) := by
  rw [Registers.r391, value385 digest d hd hm, Registers.r2]
  have ha := z385_fits d hd
  have hb : FitsLong (2097151 : Int) := by norm_num [FitsLong]
  rw [z391]
  exact and_mask_ofInt (k := 21) (by decide)

theorem value392 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r392 digest = val (z392 d) := by
  rw [Registers.r392, value390 digest d hd hm, Registers.r3]
  have ha := z390_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z392]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value393 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r393 digest = val (z393 d) := by
  rw [Registers.r393, value344 digest d hd hm, value392 digest d hd hm]
  have ha := z344_fits d hd
  have hb := z392_fits d hd
  have hr := z393_fits d hd
  rw [z393] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value394 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r394 digest = val (z394 d) := by
  rw [Registers.r394, value390 digest d hd hm, Registers.r2]
  have ha := z390_fits d hd
  have hb : FitsLong (2097151 : Int) := by norm_num [FitsLong]
  rw [z394]
  exact and_mask_ofInt (k := 21) (by decide)

theorem value395 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r395 digest = val (z395 d) := by
  rw [Registers.r395, value393 digest d hd hm, Registers.r3]
  have ha := z393_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z395]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value396 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r396 digest = val (z396 d) := by
  rw [Registers.r396, value395 digest d hd hm, value350 digest d hd hm]
  have ha := z395_fits d hd
  have hb := z350_fits d hd
  have hr := z396_fits d hd
  rw [z396] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value397 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r397 digest = val (z397 d) := by
  rw [Registers.r397, value393 digest d hd hm, Registers.r2]
  have ha := z393_fits d hd
  have hb : FitsLong (2097151 : Int) := by norm_num [FitsLong]
  rw [z397]
  exact and_mask_ofInt (k := 21) (by decide)

theorem value398 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r398 digest = val (z398 d) := by
  rw [Registers.r398, value396 digest d hd hm, Registers.r3]
  have ha := z396_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z398]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value399 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r399 digest = val (z399 d) := by
  rw [Registers.r399, value348 digest d hd hm, value398 digest d hd hm]
  have ha := z348_fits d hd
  have hb := z398_fits d hd
  have hr := z399_fits d hd
  rw [z399] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value400 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r400 digest = val (z400 d) := by
  rw [Registers.r400, value396 digest d hd hm, Registers.r2]
  have ha := z396_fits d hd
  have hb : FitsLong (2097151 : Int) := by norm_num [FitsLong]
  rw [z400]
  exact and_mask_ofInt (k := 21) (by decide)

theorem value401 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r401 digest = val (z401 d) := by
  rw [Registers.r401, value399 digest d hd hm, Registers.r3]
  have ha := z399_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z401]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value402 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r402 digest = val (z402 d) := by
  rw [Registers.r402, value401 digest d hd hm, value355 digest d hd hm]
  have ha := z401_fits d hd
  have hb := z355_fits d hd
  have hr := z402_fits d hd
  rw [z402] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value403 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r403 digest = val (z403 d) := by
  rw [Registers.r403, value399 digest d hd hm, Registers.r2]
  have ha := z399_fits d hd
  have hb : FitsLong (2097151 : Int) := by norm_num [FitsLong]
  rw [z403]
  exact and_mask_ofInt (k := 21) (by decide)

theorem value404 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r404 digest = val (z404 d) := by
  rw [Registers.r404, value402 digest d hd hm, Registers.r3]
  have ha := z402_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z404]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value405 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r405 digest = val (z405 d) := by
  rw [Registers.r405, value353 digest d hd hm, value404 digest d hd hm]
  have ha := z353_fits d hd
  have hb := z404_fits d hd
  have hr := z405_fits d hd
  rw [z405] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value406 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r406 digest = val (z406 d) := by
  rw [Registers.r406, value402 digest d hd hm, Registers.r2]
  have ha := z402_fits d hd
  have hb : FitsLong (2097151 : Int) := by norm_num [FitsLong]
  rw [z406]
  exact and_mask_ofInt (k := 21) (by decide)

theorem value407 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r407 digest = val (z407 d) := by
  rw [Registers.r407, value405 digest d hd hm, Registers.r3]
  have ha := z405_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z407]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value408 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r408 digest = val (z408 d) := by
  rw [Registers.r408, value407 digest d hd hm, value359 digest d hd hm]
  have ha := z407_fits d hd
  have hb := z359_fits d hd
  have hr := z408_fits d hd
  rw [z408] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value409 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r409 digest = val (z409 d) := by
  rw [Registers.r409, value405 digest d hd hm, Registers.r2]
  have ha := z405_fits d hd
  have hb : FitsLong (2097151 : Int) := by norm_num [FitsLong]
  rw [z409]
  exact and_mask_ofInt (k := 21) (by decide)

theorem value410 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r410 digest = val (z410 d) := by
  rw [Registers.r410, value408 digest d hd hm, Registers.r3]
  have ha := z408_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z410]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value411 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r411 digest = val (z411 d) := by
  rw [Registers.r411, value408 digest d hd hm, Registers.r2]
  have ha := z408_fits d hd
  have hb : FitsLong (2097151 : Int) := by norm_num [FitsLong]
  rw [z411]
  exact and_mask_ofInt (k := 21) (by decide)

end Firedancer.Common.ScalarArithmetic.MachineArithmetic
