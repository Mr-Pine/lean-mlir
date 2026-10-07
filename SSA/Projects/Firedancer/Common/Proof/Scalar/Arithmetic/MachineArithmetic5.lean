import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.MachineArithmetic4
import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.Registers

namespace Firedancer.Common.ScalarArithmetic.MachineArithmetic
open LeanMLIR SLLVM
open InstCombine (LLVM)
open R43x6 (FitsLong)
open IntegerRegisters

set_option maxHeartbeats 2000000

theorem value412 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r412 digest = val (z412 d) := by
  rw [Registers.r412, value410 digest d hd hm, Registers.r24]
  have ha := z410_fits d hd
  have hb : FitsLong (666643 : Int) := by norm_num [FitsLong]
  have hr := z412_fits d hd
  rw [z412] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value413 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r413 digest = val (z413 d) := by
  rw [Registers.r413, value412 digest d hd hm, value371 digest d hd hm]
  have ha := z412_fits d hd
  have hb := z371_fits d hd
  have hr := z413_fits d hd
  rw [z413] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value414 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r414 digest = val (z414 d) := by
  rw [Registers.r414, value410 digest d hd hm, Registers.r25]
  have ha := z410_fits d hd
  have hb : FitsLong (470296 : Int) := by norm_num [FitsLong]
  have hr := z414_fits d hd
  rw [z414] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value415 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r415 digest = val (z415 d) := by
  rw [Registers.r415, value414 digest d hd hm, value376 digest d hd hm]
  have ha := z414_fits d hd
  have hb := z376_fits d hd
  have hr := z415_fits d hd
  rw [z415] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value416 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r416 digest = val (z416 d) := by
  rw [Registers.r416, value410 digest d hd hm, Registers.r26]
  have ha := z410_fits d hd
  have hb : FitsLong (654183 : Int) := by norm_num [FitsLong]
  have hr := z416_fits d hd
  rw [z416] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value417 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r417 digest = val (z417 d) := by
  rw [Registers.r417, value416 digest d hd hm, value381 digest d hd hm]
  have ha := z416_fits d hd
  have hb := z381_fits d hd
  have hr := z417_fits d hd
  rw [z417] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value418 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r418 digest = val (z418 d) := by
  rw [Registers.r418, value410 digest d hd hm, Registers.r27]
  have ha := z410_fits d hd
  have hb : FitsLong (-997805 : Int) := by norm_num [FitsLong]
  have hr := z418_fits d hd
  rw [z418] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value419 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r419 digest = val (z419 d) := by
  rw [Registers.r419, value418 digest d hd hm, value386 digest d hd hm]
  have ha := z418_fits d hd
  have hb := z386_fits d hd
  have hr := z419_fits d hd
  rw [z419] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value420 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r420 digest = val (z420 d) := by
  rw [Registers.r420, value410 digest d hd hm, Registers.r28]
  have ha := z410_fits d hd
  have hb : FitsLong (136657 : Int) := by norm_num [FitsLong]
  have hr := z420_fits d hd
  rw [z420] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value421 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r421 digest = val (z421 d) := by
  rw [Registers.r421, value420 digest d hd hm, value391 digest d hd hm]
  have ha := z420_fits d hd
  have hb := z391_fits d hd
  have hr := z421_fits d hd
  rw [z421] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value422 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r422 digest = val (z422 d) := by
  rw [Registers.r422, value410 digest d hd hm, Registers.r29]
  have ha := z410_fits d hd
  have hb : FitsLong (-683901 : Int) := by norm_num [FitsLong]
  have hr := z422_fits d hd
  rw [z422] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value423 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r423 digest = val (z423 d) := by
  rw [Registers.r423, value422 digest d hd hm, value394 digest d hd hm]
  have ha := z422_fits d hd
  have hb := z394_fits d hd
  have hr := z423_fits d hd
  rw [z423] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value424 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r424 digest = val (z424 d) := by
  rw [Registers.r424, value413 digest d hd hm, Registers.r3]
  have ha := z413_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z424]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value425 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r425 digest = val (z425 d) := by
  rw [Registers.r425, value415 digest d hd hm, value424 digest d hd hm]
  have ha := z415_fits d hd
  have hb := z424_fits d hd
  have hr := z425_fits d hd
  rw [z425] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value426 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r426 digest = val (z426 d) := by
  rw [Registers.r426, value413 digest d hd hm, Registers.r2]
  have ha := z413_fits d hd
  have hb : FitsLong (2097151 : Int) := by norm_num [FitsLong]
  rw [z426]
  exact and_mask_ofInt (k := 21) (by decide)

theorem value427 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r427 digest = val (z427 d) := by
  rw [Registers.r427, value425 digest d hd hm, Registers.r3]
  have ha := z425_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z427]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value428 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r428 digest = val (z428 d) := by
  rw [Registers.r428, value417 digest d hd hm, value427 digest d hd hm]
  have ha := z417_fits d hd
  have hb := z427_fits d hd
  have hr := z428_fits d hd
  rw [z428] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value429 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r429 digest = val (z429 d) := by
  rw [Registers.r429, value428 digest d hd hm, Registers.r3]
  have ha := z428_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z429]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value430 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r430 digest = val (z430 d) := by
  rw [Registers.r430, value419 digest d hd hm, value429 digest d hd hm]
  have ha := z419_fits d hd
  have hb := z429_fits d hd
  have hr := z430_fits d hd
  rw [z430] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value431 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r431 digest = val (z431 d) := by
  rw [Registers.r431, value430 digest d hd hm, Registers.r3]
  have ha := z430_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z431]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value432 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r432 digest = val (z432 d) := by
  rw [Registers.r432, value421 digest d hd hm, value431 digest d hd hm]
  have ha := z421_fits d hd
  have hb := z431_fits d hd
  have hr := z432_fits d hd
  rw [z432] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value433 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r433 digest = val (z433 d) := by
  rw [Registers.r433, value432 digest d hd hm, Registers.r3]
  have ha := z432_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z433]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value434 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r434 digest = val (z434 d) := by
  rw [Registers.r434, value423 digest d hd hm, value433 digest d hd hm]
  have ha := z423_fits d hd
  have hb := z433_fits d hd
  have hr := z434_fits d hd
  rw [z434] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value435 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r435 digest = val (z435 d) := by
  rw [Registers.r435, value434 digest d hd hm, Registers.r3]
  have ha := z434_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z435]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value436 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r436 digest = val (z436 d) := by
  rw [Registers.r436, value435 digest d hd hm, value397 digest d hd hm]
  have ha := z435_fits d hd
  have hb := z397_fits d hd
  have hr := z436_fits d hd
  rw [z436] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value437 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r437 digest = val (z437 d) := by
  rw [Registers.r437, value436 digest d hd hm, Registers.r3]
  have ha := z436_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z437]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value438 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r438 digest = val (z438 d) := by
  rw [Registers.r438, value437 digest d hd hm, value400 digest d hd hm]
  have ha := z437_fits d hd
  have hb := z400_fits d hd
  have hr := z438_fits d hd
  rw [z438] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value439 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r439 digest = val (z439 d) := by
  rw [Registers.r439, value438 digest d hd hm, Registers.r3]
  have ha := z438_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z439]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value440 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r440 digest = val (z440 d) := by
  rw [Registers.r440, value439 digest d hd hm, value403 digest d hd hm]
  have ha := z439_fits d hd
  have hb := z403_fits d hd
  have hr := z440_fits d hd
  rw [z440] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value441 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r441 digest = val (z441 d) := by
  rw [Registers.r441, value440 digest d hd hm, Registers.r3]
  have ha := z440_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z441]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value442 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r442 digest = val (z442 d) := by
  rw [Registers.r442, value441 digest d hd hm, value406 digest d hd hm]
  have ha := z441_fits d hd
  have hb := z406_fits d hd
  have hr := z442_fits d hd
  rw [z442] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value443 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r443 digest = val (z443 d) := by
  rw [Registers.r443, value442 digest d hd hm, Registers.r3]
  have ha := z442_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z443]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value444 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r444 digest = val (z444 d) := by
  rw [Registers.r444, value443 digest d hd hm, value409 digest d hd hm]
  have ha := z443_fits d hd
  have hb := z409_fits d hd
  have hr := z444_fits d hd
  rw [z444] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value445 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r445 digest = val (z445 d) := by
  rw [Registers.r445, value444 digest d hd hm, Registers.r3]
  have ha := z444_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z445]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value446 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r446 digest = val (z446 d) := by
  rw [Registers.r446, value445 digest d hd hm, value411 digest d hd hm]
  have ha := z445_fits d hd
  have hb := z411_fits d hd
  have hr := z446_fits d hd
  rw [z446] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

end Firedancer.Common.ScalarArithmetic.MachineArithmetic
