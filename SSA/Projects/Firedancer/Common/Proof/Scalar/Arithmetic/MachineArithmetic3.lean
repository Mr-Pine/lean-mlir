import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.MachineArithmetic2
import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.Registers

namespace Firedancer.Common.ScalarArithmetic.MachineArithmetic
open LeanMLIR SLLVM
open InstCombine (LLVM)
open R43x6 (FitsLong)
open IntegerRegisters

set_option maxHeartbeats 2000000

theorem value298 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r298 digest = val (z298 d) := by
  rw [Registers.r298, value287 digest d hd hm, Registers.r30]
  have ha := z287_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z298_fits d hd
  rw [z298] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value299 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r299 digest = val (z299 d) := by
  rw [Registers.r299, value298 digest d hd hm, Registers.r3]
  have ha := z298_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z299]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value300 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r300 digest = val (z300 d) := by
  rw [Registers.r300, value289 digest d hd hm, value299 digest d hd hm]
  have ha := z289_fits d hd
  have hb := z299_fits d hd
  have hr := z300_fits d hd
  rw [z300] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value301 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r301 digest = val (z301 d) := by
  rw [Registers.r301, value298 digest d hd hm, Registers.r32]
  have ha := z298_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z301, m301]
  exact and_high21_ofInt ha

theorem value302 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r302 digest = val (z302 d) := by
  rw [Registers.r302, value287 digest d hd hm, value301 digest d hd hm]
  have ha := z287_fits d hd
  have hb := z301_fits d hd
  have hr := z302_fits d hd
  rw [z302] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value303 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r303 digest = val (z303 d) := by
  rw [Registers.r303, value291 digest d hd hm, Registers.r30]
  have ha := z291_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z303_fits d hd
  rw [z303] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value304 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r304 digest = val (z304 d) := by
  rw [Registers.r304, value303 digest d hd hm, Registers.r3]
  have ha := z303_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z304]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value305 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r305 digest = val (z305 d) := by
  rw [Registers.r305, value293 digest d hd hm, value304 digest d hd hm]
  have ha := z293_fits d hd
  have hb := z304_fits d hd
  have hr := z305_fits d hd
  rw [z305] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value306 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r306 digest = val (z306 d) := by
  rw [Registers.r306, value303 digest d hd hm, Registers.r32]
  have ha := z303_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z306, m306]
  exact and_high21_ofInt ha

theorem value307 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r307 digest = val (z307 d) := by
  rw [Registers.r307, value291 digest d hd hm, value306 digest d hd hm]
  have ha := z291_fits d hd
  have hb := z306_fits d hd
  have hr := z307_fits d hd
  rw [z307] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value308 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r308 digest = val (z308 d) := by
  rw [Registers.r308, value295 digest d hd hm, Registers.r30]
  have ha := z295_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z308_fits d hd
  rw [z308] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value309 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r309 digest = val (z309 d) := by
  rw [Registers.r309, value308 digest d hd hm, Registers.r3]
  have ha := z308_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z309]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value310 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r310 digest = val (z310 d) := by
  rw [Registers.r310, value297 digest d hd hm, value309 digest d hd hm]
  have ha := z297_fits d hd
  have hb := z309_fits d hd
  have hr := z310_fits d hd
  rw [z310] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value311 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r311 digest = val (z311 d) := by
  rw [Registers.r311, value308 digest d hd hm, Registers.r32]
  have ha := z308_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z311, m311]
  exact and_high21_ofInt ha

theorem value312 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r312 digest = val (z312 d) := by
  rw [Registers.r312, value295 digest d hd hm, value311 digest d hd hm]
  have ha := z295_fits d hd
  have hb := z311_fits d hd
  have hr := z312_fits d hd
  rw [z312] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value313 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r313 digest = val (z313 d) := by
  rw [Registers.r313, value285 digest d hd hm, Registers.r30]
  have ha := z285_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z313_fits d hd
  rw [z313] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value314 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r314 digest = val (z314 d) := by
  rw [Registers.r314, value313 digest d hd hm, Registers.r3]
  have ha := z313_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z314]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value315 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r315 digest = val (z315 d) := by
  rw [Registers.r315, value233 digest d hd hm, value169 digest d hd hm]
  have ha := z233_fits d hd
  have hb := z169_fits d hd
  have hr := z315_fits d hd
  rw [z315] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value316 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r316 digest = val (z316 d) := by
  rw [Registers.r316, value315 digest d hd hm, value210 digest d hd hm]
  have ha := z315_fits d hd
  have hb := z210_fits d hd
  have hr := z316_fits d hd
  rw [z316] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value317 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r317 digest = val (z317 d) := by
  rw [Registers.r317, value316 digest d hd hm, value246 digest d hd hm]
  have ha := z316_fits d hd
  have hb := z246_fits d hd
  have hr := z317_fits d hd
  rw [z317] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value318 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r318 digest = val (z318 d) := by
  rw [Registers.r318, value317 digest d hd hm, value257 digest d hd hm]
  have ha := z317_fits d hd
  have hb := z257_fits d hd
  have hr := z318_fits d hd
  rw [z318] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value319 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r319 digest = val (z319 d) := by
  rw [Registers.r319, value318 digest d hd hm, value273 digest d hd hm]
  have ha := z318_fits d hd
  have hb := z273_fits d hd
  have hr := z319_fits d hd
  rw [z319] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value320 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r320 digest = val (z320 d) := by
  rw [Registers.r320, value319 digest d hd hm, value314 digest d hd hm]
  have ha := z319_fits d hd
  have hb := z314_fits d hd
  have hr := z320_fits d hd
  rw [z320] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value321 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r321 digest = val (z321 d) := by
  rw [Registers.r321, value313 digest d hd hm, Registers.r32]
  have ha := z313_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z321, m321]
  exact and_high21_ofInt ha

theorem value322 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r322 digest = val (z322 d) := by
  rw [Registers.r322, value285 digest d hd hm, value321 digest d hd hm]
  have ha := z285_fits d hd
  have hb := z321_fits d hd
  have hr := z322_fits d hd
  rw [z322] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value323 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r323 digest = val (z323 d) := by
  rw [Registers.r323, value262 digest d hd hm, Registers.r30]
  have ha := z262_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z323_fits d hd
  rw [z323] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value324 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r324 digest = val (z324 d) := by
  rw [Registers.r324, value323 digest d hd hm, Registers.r3]
  have ha := z323_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z324]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value325 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r325 digest = val (z325 d) := by
  rw [Registers.r325, value178 digest d hd hm, value235 digest d hd hm]
  have ha := z178_fits d hd
  have hb := z235_fits d hd
  have hr := z325_fits d hd
  rw [z325] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value326 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r326 digest = val (z326 d) := by
  rw [Registers.r326, value325 digest d hd hm, value213 digest d hd hm]
  have ha := z325_fits d hd
  have hb := z213_fits d hd
  have hr := z326_fits d hd
  rw [z326] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value327 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r327 digest = val (z327 d) := by
  rw [Registers.r327, value326 digest d hd hm, value248 digest d hd hm]
  have ha := z326_fits d hd
  have hb := z248_fits d hd
  have hr := z327_fits d hd
  rw [z327] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value328 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r328 digest = val (z328 d) := by
  rw [Registers.r328, value327 digest d hd hm, value324 digest d hd hm]
  have ha := z327_fits d hd
  have hb := z324_fits d hd
  have hr := z328_fits d hd
  rw [z328] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value329 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r329 digest = val (z329 d) := by
  rw [Registers.r329, value323 digest d hd hm, Registers.r32]
  have ha := z323_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z329, m329]
  exact and_high21_ofInt ha

theorem value330 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r330 digest = val (z330 d) := by
  rw [Registers.r330, value262 digest d hd hm, value329 digest d hd hm]
  have ha := z262_fits d hd
  have hb := z329_fits d hd
  have hr := z330_fits d hd
  rw [z330] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value331 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r331 digest = val (z331 d) := by
  rw [Registers.r331, value239 digest d hd hm, Registers.r30]
  have ha := z239_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z331_fits d hd
  rw [z331] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value332 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r332 digest = val (z332 d) := by
  rw [Registers.r332, value331 digest d hd hm, Registers.r3]
  have ha := z331_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z332]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value333 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r333 digest = val (z333 d) := by
  rw [Registers.r333, value332 digest d hd hm, value218 digest d hd hm]
  have ha := z332_fits d hd
  have hb := z218_fits d hd
  have hr := z333_fits d hd
  rw [z333] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value334 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r334 digest = val (z334 d) := by
  rw [Registers.r334, value331 digest d hd hm, Registers.r32]
  have ha := z331_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z334, m334]
  exact and_high21_ofInt ha

theorem value335 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r335 digest = val (z335 d) := by
  rw [Registers.r335, value239 digest d hd hm, value334 digest d hd hm]
  have ha := z239_fits d hd
  have hb := z334_fits d hd
  have hr := z335_fits d hd
  rw [z335] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value336 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r336 digest = val (z336 d) := by
  rw [Registers.r336, value300 digest d hd hm, Registers.r30]
  have ha := z300_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z336_fits d hd
  rw [z336] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value337 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r337 digest = val (z337 d) := by
  rw [Registers.r337, value336 digest d hd hm, Registers.r3]
  have ha := z336_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z337]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value338 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r338 digest = val (z338 d) := by
  rw [Registers.r338, value336 digest d hd hm, Registers.r32]
  have ha := z336_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z338, m338]
  exact and_high21_ofInt ha

theorem value339 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r339 digest = val (z339 d) := by
  rw [Registers.r339, value305 digest d hd hm, Registers.r30]
  have ha := z305_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z339_fits d hd
  rw [z339] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value340 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r340 digest = val (z340 d) := by
  rw [Registers.r340, value339 digest d hd hm, Registers.r3]
  have ha := z339_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z340]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value341 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r341 digest = val (z341 d) := by
  rw [Registers.r341, value339 digest d hd hm, Registers.r32]
  have ha := z339_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z341, m341]
  exact and_high21_ofInt ha

theorem value342 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r342 digest = val (z342 d) := by
  rw [Registers.r342, value310 digest d hd hm, Registers.r30]
  have ha := z310_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z342_fits d hd
  rw [z342] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value343 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r343 digest = val (z343 d) := by
  rw [Registers.r343, value342 digest d hd hm, Registers.r3]
  have ha := z342_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z343]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value344 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r344 digest = val (z344 d) := by
  rw [Registers.r344, value322 digest d hd hm, value343 digest d hd hm]
  have ha := z322_fits d hd
  have hb := z343_fits d hd
  have hr := z344_fits d hd
  rw [z344] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value345 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r345 digest = val (z345 d) := by
  rw [Registers.r345, value342 digest d hd hm, Registers.r32]
  have ha := z342_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z345, m345]
  exact and_high21_ofInt ha

theorem value346 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r346 digest = val (z346 d) := by
  rw [Registers.r346, value320 digest d hd hm, Registers.r30]
  have ha := z320_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z346_fits d hd
  rw [z346] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value347 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r347 digest = val (z347 d) := by
  rw [Registers.r347, value346 digest d hd hm, Registers.r3]
  have ha := z346_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z347]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value348 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r348 digest = val (z348 d) := by
  rw [Registers.r348, value330 digest d hd hm, value347 digest d hd hm]
  have ha := z330_fits d hd
  have hb := z347_fits d hd
  have hr := z348_fits d hd
  rw [z348] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value349 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r349 digest = val (z349 d) := by
  rw [Registers.r349, value346 digest d hd hm, Registers.r32]
  have ha := z346_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z349, m349]
  exact and_high21_ofInt ha

theorem value350 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r350 digest = val (z350 d) := by
  rw [Registers.r350, value320 digest d hd hm, value349 digest d hd hm]
  have ha := z320_fits d hd
  have hb := z349_fits d hd
  have hr := z350_fits d hd
  rw [z350] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value351 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r351 digest = val (z351 d) := by
  rw [Registers.r351, value328 digest d hd hm, Registers.r30]
  have ha := z328_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z351_fits d hd
  rw [z351] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value352 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r352 digest = val (z352 d) := by
  rw [Registers.r352, value351 digest d hd hm, Registers.r3]
  have ha := z351_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z352]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value353 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r353 digest = val (z353 d) := by
  rw [Registers.r353, value335 digest d hd hm, value352 digest d hd hm]
  have ha := z335_fits d hd
  have hb := z352_fits d hd
  have hr := z353_fits d hd
  rw [z353] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value354 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r354 digest = val (z354 d) := by
  rw [Registers.r354, value351 digest d hd hm, Registers.r32]
  have ha := z351_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z354, m354]
  exact and_high21_ofInt ha

theorem value355 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r355 digest = val (z355 d) := by
  rw [Registers.r355, value328 digest d hd hm, value354 digest d hd hm]
  have ha := z328_fits d hd
  have hb := z354_fits d hd
  have hr := z355_fits d hd
  rw [z355] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value356 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r356 digest = val (z356 d) := by
  rw [Registers.r356, value333 digest d hd hm, Registers.r30]
  have ha := z333_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z356_fits d hd
  rw [z356] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value357 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r357 digest = val (z357 d) := by
  rw [Registers.r357, value356 digest d hd hm, Registers.r3]
  have ha := z356_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z357]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value358 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r358 digest = val (z358 d) := by
  rw [Registers.r358, value356 digest d hd hm, Registers.r32]
  have ha := z356_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z358, m358]
  exact and_high21_ofInt ha

theorem value359 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r359 digest = val (z359 d) := by
  rw [Registers.r359, value333 digest d hd hm, value358 digest d hd hm]
  have ha := z333_fits d hd
  have hb := z358_fits d hd
  have hr := z359_fits d hd
  rw [z359] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value360 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r360 digest = val (z360 d) := by
  rw [Registers.r360, value357 digest d hd hm, Registers.r24]
  have ha := z357_fits d hd
  have hb : FitsLong (666643 : Int) := by norm_num [FitsLong]
  have hr := z360_fits d hd
  rw [z360] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value361 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r361 digest = val (z361 d) := by
  rw [Registers.r361, value302 digest d hd hm, value360 digest d hd hm]
  have ha := z302_fits d hd
  have hb := z360_fits d hd
  have hr := z361_fits d hd
  rw [z361] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value362 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r362 digest = val (z362 d) := by
  rw [Registers.r362, value357 digest d hd hm, Registers.r25]
  have ha := z357_fits d hd
  have hb : FitsLong (470296 : Int) := by norm_num [FitsLong]
  have hr := z362_fits d hd
  rw [z362] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value363 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r363 digest = val (z363 d) := by
  rw [Registers.r363, value357 digest d hd hm, Registers.r26]
  have ha := z357_fits d hd
  have hb : FitsLong (654183 : Int) := by norm_num [FitsLong]
  have hr := z363_fits d hd
  rw [z363] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value364 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r364 digest = val (z364 d) := by
  rw [Registers.r364, value357 digest d hd hm, Registers.r27]
  have ha := z357_fits d hd
  have hb : FitsLong (-997805 : Int) := by norm_num [FitsLong]
  have hr := z364_fits d hd
  rw [z364] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value365 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r365 digest = val (z365 d) := by
  rw [Registers.r365, value357 digest d hd hm, Registers.r28]
  have ha := z357_fits d hd
  have hb : FitsLong (136657 : Int) := by norm_num [FitsLong]
  have hr := z365_fits d hd
  rw [z365] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value366 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r366 digest = val (z366 d) := by
  rw [Registers.r366, value357 digest d hd hm, Registers.r29]
  have ha := z357_fits d hd
  have hb : FitsLong (-683901 : Int) := by norm_num [FitsLong]
  have hr := z366_fits d hd
  rw [z366] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

end Firedancer.Common.ScalarArithmetic.MachineArithmetic
