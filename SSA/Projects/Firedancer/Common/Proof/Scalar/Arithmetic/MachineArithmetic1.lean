import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.MachineArithmetic0
import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.Registers

namespace Firedancer.Common.ScalarArithmetic.MachineArithmetic
open LeanMLIR SLLVM
open InstCombine (LLVM)
open R43x6 (FitsLong)
open IntegerRegisters

set_option maxHeartbeats 2000000

theorem value167 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r167 digest = val (z167 d) := by
  rw [Registers.r167, value154 digest d hd hm, Registers.r30]
  have ha := z154_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z167_fits d hd
  rw [z167] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z154_bounds d hd
  constructor <;> omega

theorem value168 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r168 digest = val (z168 d) := by
  rw [Registers.r168, value167 digest d hd hm, Registers.r3]
  have ha := z167_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z168]
  have hab := z167_bounds d hd
  simpa [val, R43x6.shiftRight_eq] using
    (lshr_ofInt ha (by omega) (n := 21) (by decide) (by decide))

theorem value169 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r169 digest = val (z169 d) := by
  rw [Registers.r169, value156 digest d hd hm, value168 digest d hd hm]
  have ha := z156_fits d hd
  have hb := z168_fits d hd
  have hr := z169_fits d hd
  rw [z169] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z156_bounds d hd
  have hbb := z168_bounds d hd
  constructor <;> omega

theorem value170 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r170 digest = val (z170 d) := by
  rw [Registers.r170, value167 digest d hd hm, Registers.r31]
  have ha := z167_fits d hd
  have hb : FitsLong (8796090925056 : Int) := by norm_num [FitsLong]
  rw [z170, m170]
  have hab := z167_bounds d hd
  exact and_finite_high21_ofInt ha (by omega) (by omega)

theorem value171 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r171 digest = val (z171 d) := by
  rw [Registers.r171, value154 digest d hd hm, value170 digest d hd hm]
  have ha := z154_fits d hd
  have hb := z170_fits d hd
  have hr := z171_fits d hd
  rw [z171] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value172 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r172 digest = val (z172 d) := by
  rw [Registers.r172, value158 digest d hd hm, Registers.r30]
  have ha := z158_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z172_fits d hd
  rw [z172] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z158_bounds d hd
  constructor <;> omega

theorem value173 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r173 digest = val (z173 d) := by
  rw [Registers.r173, value172 digest d hd hm, Registers.r3]
  have ha := z172_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z173]
  have hab := z172_bounds d hd
  simpa [val, R43x6.shiftRight_eq] using
    (lshr_ofInt ha (by omega) (n := 21) (by decide) (by decide))

theorem value174 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r174 digest = val (z174 d) := by
  rw [Registers.r174, value136 digest d hd hm, value79 digest d hm]
  have ha := z136_fits d hd
  have hb := z79_fits d hd
  have hr := z174_fits d hd
  rw [z174] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z136_bounds d hd
  have hbb := z79_bounds d hd
  constructor <;> omega

theorem value175 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r175 digest = val (z175 d) := by
  rw [Registers.r175, value174 digest d hd hm, value145 digest d hd hm]
  have ha := z174_fits d hd
  have hb := z145_fits d hd
  have hr := z175_fits d hd
  rw [z175] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z174_bounds d hd
  have hbb := z145_bounds d hd
  constructor <;> omega

theorem value176 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r176 digest = val (z176 d) := by
  rw [Registers.r176, value175 digest d hd hm, value159 digest d hd hm]
  have ha := z175_fits d hd
  have hb := z159_fits d hd
  have hr := z176_fits d hd
  rw [z176] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value177 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r177 digest = val (z177 d) := by
  rw [Registers.r177, value176 digest d hd hm, value127 digest d hd hm]
  have ha := z176_fits d hd
  have hb := z127_fits d hd
  have hr := z177_fits d hd
  rw [z177] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value178 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r178 digest = val (z178 d) := by
  rw [Registers.r178, value177 digest d hd hm, value173 digest d hd hm]
  have ha := z177_fits d hd
  have hb := z173_fits d hd
  have hr := z178_fits d hd
  rw [z178] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value179 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r179 digest = val (z179 d) := by
  rw [Registers.r179, value172 digest d hd hm, Registers.r32]
  have ha := z172_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z179, m179]
  exact and_high21_ofInt ha

theorem value180 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r180 digest = val (z180 d) := by
  rw [Registers.r180, value158 digest d hd hm, value179 digest d hd hm]
  have ha := z158_fits d hd
  have hb := z179_fits d hd
  have hr := z180_fits d hd
  rw [z180] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value181 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r181 digest = val (z181 d) := by
  rw [Registers.r181, value165 digest d hd hm, Registers.r30]
  have ha := z165_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z181_fits d hd
  rw [z181] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value182 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r182 digest = val (z182 d) := by
  rw [Registers.r182, value181 digest d hd hm, Registers.r3]
  have ha := z181_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z182]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value183 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r183 digest = val (z183 d) := by
  rw [Registers.r183, value108 digest d hd hm, value138 digest d hd hm]
  have ha := z108_fits d hd
  have hb := z138_fits d hd
  have hr := z183_fits d hd
  rw [z183] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value184 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r184 digest = val (z184 d) := by
  rw [Registers.r184, value183 digest d hd hm, value147 digest d hd hm]
  have ha := z183_fits d hd
  have hb := z147_fits d hd
  have hr := z184_fits d hd
  rw [z184] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value185 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r185 digest = val (z185 d) := by
  rw [Registers.r185, value184 digest d hd hm, value166 digest d hd hm]
  have ha := z184_fits d hd
  have hb := z166_fits d hd
  have hr := z185_fits d hd
  rw [z185] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value186 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r186 digest = val (z186 d) := by
  rw [Registers.r186, value185 digest d hd hm, value120 digest d hd hm]
  have ha := z185_fits d hd
  have hb := z120_fits d hd
  have hr := z186_fits d hd
  rw [z186] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value187 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r187 digest = val (z187 d) := by
  rw [Registers.r187, value186 digest d hd hm, value129 digest d hd hm]
  have ha := z186_fits d hd
  have hb := z129_fits d hd
  have hr := z187_fits d hd
  rw [z187] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value188 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r188 digest = val (z188 d) := by
  rw [Registers.r188, value187 digest d hd hm, value182 digest d hd hm]
  have ha := z187_fits d hd
  have hb := z182_fits d hd
  have hr := z188_fits d hd
  rw [z188] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value189 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r189 digest = val (z189 d) := by
  rw [Registers.r189, value181 digest d hd hm, Registers.r32]
  have ha := z181_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z189, m189]
  exact and_high21_ofInt ha

theorem value190 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r190 digest = val (z190 d) := by
  rw [Registers.r190, value152 digest d hd hm, Registers.r30]
  have ha := z152_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z190_fits d hd
  rw [z190] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value191 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r191 digest = val (z191 d) := by
  rw [Registers.r191, value190 digest d hd hm, Registers.r3]
  have ha := z190_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z191]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value192 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r192 digest = val (z192 d) := by
  rw [Registers.r192, value112 digest d hd hm, value140 digest d hd hm]
  have ha := z112_fits d hd
  have hb := z140_fits d hd
  have hr := z192_fits d hd
  rw [z192] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value193 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r193 digest = val (z193 d) := by
  rw [Registers.r193, value192 digest d hd hm, value122 digest d hd hm]
  have ha := z192_fits d hd
  have hb := z122_fits d hd
  have hr := z193_fits d hd
  rw [z193] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value194 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r194 digest = val (z194 d) := by
  rw [Registers.r194, value193 digest d hd hm, value131 digest d hd hm]
  have ha := z193_fits d hd
  have hb := z131_fits d hd
  have hr := z194_fits d hd
  rw [z194] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value195 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r195 digest = val (z195 d) := by
  rw [Registers.r195, value194 digest d hd hm, value191 digest d hd hm]
  have ha := z194_fits d hd
  have hb := z191_fits d hd
  have hr := z195_fits d hd
  rw [z195] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value196 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r196 digest = val (z196 d) := by
  rw [Registers.r196, value190 digest d hd hm, Registers.r32]
  have ha := z190_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z196, m196]
  exact and_high21_ofInt ha

theorem value197 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r197 digest = val (z197 d) := by
  rw [Registers.r197, value152 digest d hd hm, value196 digest d hd hm]
  have ha := z152_fits d hd
  have hb := z196_fits d hd
  have hr := z197_fits d hd
  rw [z197] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value198 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r198 digest = val (z198 d) := by
  rw [Registers.r198, value133 digest d hd hm, Registers.r30]
  have ha := z133_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z198_fits d hd
  rw [z198] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value199 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r199 digest = val (z199 d) := by
  rw [Registers.r199, value198 digest d hd hm, Registers.r3]
  have ha := z198_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z199]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value200 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r200 digest = val (z200 d) := by
  rw [Registers.r200, value126 digest d hd hm, value199 digest d hd hm]
  have ha := z126_fits d hd
  have hb := z199_fits d hd
  have hr := z200_fits d hd
  rw [z200] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value201 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r201 digest = val (z201 d) := by
  rw [Registers.r201, value198 digest d hd hm, Registers.r32]
  have ha := z198_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z201, m201]
  exact and_high21_ofInt ha

theorem value202 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r202 digest = val (z202 d) := by
  rw [Registers.r202, value133 digest d hd hm, value201 digest d hd hm]
  have ha := z133_fits d hd
  have hb := z201_fits d hd
  have hr := z202_fits d hd
  rw [z202] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value203 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r203 digest = val (z203 d) := by
  rw [Registers.r203, value118 digest d hd hm, Registers.r30]
  have ha := z118_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z203_fits d hd
  rw [z203] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value204 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r204 digest = val (z204 d) := by
  rw [Registers.r204, value203 digest d hd hm, Registers.r3]
  have ha := z203_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z204]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value205 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r205 digest = val (z205 d) := by
  rw [Registers.r205, value204 digest d hd hm, value95 digest d hm]
  have ha := z204_fits d hd
  have hb := z95_fits d hd
  have hr := z205_fits d hd
  rw [z205] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value206 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r206 digest = val (z206 d) := by
  rw [Registers.r206, value203 digest d hd hm, Registers.r32]
  have ha := z203_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z206, m206]
  exact and_high21_ofInt ha

theorem value207 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r207 digest = val (z207 d) := by
  rw [Registers.r207, value118 digest d hd hm, value206 digest d hd hm]
  have ha := z118_fits d hd
  have hb := z206_fits d hd
  have hr := z207_fits d hd
  rw [z207] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value208 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r208 digest = val (z208 d) := by
  rw [Registers.r208, value169 digest d hd hm, Registers.r30]
  have ha := z169_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z208_fits d hd
  rw [z208] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z169_bounds d hd
  constructor <;> omega

theorem value209 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r209 digest = val (z209 d) := by
  rw [Registers.r209, value208 digest d hd hm, Registers.r3]
  have ha := z208_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z209]
  have hab := z208_bounds d hd
  simpa [val, R43x6.shiftRight_eq] using
    (lshr_ofInt ha (by omega) (n := 21) (by decide) (by decide))

theorem value210 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r210 digest = val (z210 d) := by
  rw [Registers.r210, value208 digest d hd hm, Registers.r32]
  have ha := z208_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z210, m210]
  exact and_high21_ofInt ha

theorem value211 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r211 digest = val (z211 d) := by
  rw [Registers.r211, value178 digest d hd hm, Registers.r30]
  have ha := z178_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z211_fits d hd
  rw [z211] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value212 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r212 digest = val (z212 d) := by
  rw [Registers.r212, value211 digest d hd hm, Registers.r3]
  have ha := z211_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z212]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value213 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r213 digest = val (z213 d) := by
  rw [Registers.r213, value211 digest d hd hm, Registers.r32]
  have ha := z211_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z213, m213]
  exact and_high21_ofInt ha

theorem value214 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r214 digest = val (z214 d) := by
  rw [Registers.r214, value188 digest d hd hm, Registers.r30]
  have ha := z188_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z214_fits d hd
  rw [z214] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value215 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r215 digest = val (z215 d) := by
  rw [Registers.r215, value214 digest d hd hm, Registers.r3]
  have ha := z214_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z215]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value216 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r216 digest = val (z216 d) := by
  rw [Registers.r216, value215 digest d hd hm, value197 digest d hd hm]
  have ha := z215_fits d hd
  have hb := z197_fits d hd
  have hr := z216_fits d hd
  rw [z216] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value217 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r217 digest = val (z217 d) := by
  rw [Registers.r217, value214 digest d hd hm, Registers.r32]
  have ha := z214_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z217, m217]
  exact and_high21_ofInt ha

theorem value218 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r218 digest = val (z218 d) := by
  rw [Registers.r218, value188 digest d hd hm, value217 digest d hd hm]
  have ha := z188_fits d hd
  have hb := z217_fits d hd
  have hr := z218_fits d hd
  rw [z218] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value219 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r219 digest = val (z219 d) := by
  rw [Registers.r219, value195 digest d hd hm, Registers.r30]
  have ha := z195_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z219_fits d hd
  rw [z219] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value220 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r220 digest = val (z220 d) := by
  rw [Registers.r220, value219 digest d hd hm, Registers.r3]
  have ha := z219_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z220]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value221 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r221 digest = val (z221 d) := by
  rw [Registers.r221, value220 digest d hd hm, value202 digest d hd hm]
  have ha := z220_fits d hd
  have hb := z202_fits d hd
  have hr := z221_fits d hd
  rw [z221] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value222 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r222 digest = val (z222 d) := by
  rw [Registers.r222, value219 digest d hd hm, Registers.r32]
  have ha := z219_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z222, m222]
  exact and_high21_ofInt ha

theorem value223 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r223 digest = val (z223 d) := by
  rw [Registers.r223, value195 digest d hd hm, value222 digest d hd hm]
  have ha := z195_fits d hd
  have hb := z222_fits d hd
  have hr := z223_fits d hd
  rw [z223] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value224 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r224 digest = val (z224 d) := by
  rw [Registers.r224, value200 digest d hd hm, Registers.r30]
  have ha := z200_fits d hd
  have hb : FitsLong (1048576 : Int) := by norm_num [FitsLong]
  have hr := z224_fits d hd
  rw [z224] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value225 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r225 digest = val (z225 d) := by
  rw [Registers.r225, value224 digest d hd hm, Registers.r3]
  have ha := z224_fits d hd
  have hb : FitsLong (21 : Int) := by norm_num [FitsLong]
  rw [z225]
  simpa [val, R43x6.shiftRight_eq] using (ashr_ofInt ha (n := 21) (by decide))

theorem value226 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r226 digest = val (z226 d) := by
  rw [Registers.r226, value225 digest d hd hm, value207 digest d hd hm]
  have ha := z225_fits d hd
  have hb := z207_fits d hd
  have hr := z226_fits d hd
  rw [z226] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value227 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r227 digest = val (z227 d) := by
  rw [Registers.r227, value224 digest d hd hm, Registers.r32]
  have ha := z224_fits d hd
  have hb : FitsLong (-2097152 : Int) := by norm_num [FitsLong]
  rw [z227, m227]
  exact and_high21_ofInt ha

theorem value228 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r228 digest = val (z228 d) := by
  rw [Registers.r228, value200 digest d hd hm, value227 digest d hd hm]
  have ha := z200_fits d hd
  have hb := z227_fits d hd
  have hr := z228_fits d hd
  rw [z228] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

end Firedancer.Common.ScalarArithmetic.MachineArithmetic
