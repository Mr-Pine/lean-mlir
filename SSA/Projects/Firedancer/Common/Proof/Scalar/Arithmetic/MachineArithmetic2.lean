import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.MachineArithmetic1
import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.Registers

namespace Firedancer.Common.ScalarArithmetic.MachineArithmetic
open LeanMLIR SLLVM
open InstCombine (LLVM)
open R43x6 (FitsLong)
open IntegerRegisters

set_option maxHeartbeats 2000000

theorem value229 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r229 digest = val (z229 d) := by
  rw [Registers.r229, value205 digest d hd hm, Registers.r24]
  have ha := z205_fits d hd
  have hb : FitsLong (666643 : Int) := by norm_num [FitsLong]
  have hr := z229_fits d hd
  rw [z229] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value230 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r230 digest = val (z230 d) := by
  rw [Registers.r230, value229 digest d hd hm, value71 digest d hm]
  have ha := z229_fits d hd
  have hb := z71_fits d hd
  have hr := z230_fits d hd
  rw [z230] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value231 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r231 digest = val (z231 d) := by
  rw [Registers.r231, value205 digest d hd hm, Registers.r25]
  have ha := z205_fits d hd
  have hb : FitsLong (470296 : Int) := by norm_num [FitsLong]
  have hr := z231_fits d hd
  rw [z231] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value232 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r232 digest = val (z232 d) := by
  rw [Registers.r232, value171 digest d hd hm, value231 digest d hd hm]
  have ha := z171_fits d hd
  have hb := z231_fits d hd
  have hr := z232_fits d hd
  rw [z232] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value233 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r233 digest = val (z233 d) := by
  rw [Registers.r233, value205 digest d hd hm, Registers.r26]
  have ha := z205_fits d hd
  have hb : FitsLong (654183 : Int) := by norm_num [FitsLong]
  have hr := z233_fits d hd
  rw [z233] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value234 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r234 digest = val (z234 d) := by
  rw [Registers.r234, value205 digest d hd hm, Registers.r27]
  have ha := z205_fits d hd
  have hb : FitsLong (-997805 : Int) := by norm_num [FitsLong]
  have hr := z234_fits d hd
  rw [z234] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value235 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r235 digest = val (z235 d) := by
  rw [Registers.r235, value205 digest d hd hm, Registers.r28]
  have ha := z205_fits d hd
  have hb : FitsLong (136657 : Int) := by norm_num [FitsLong]
  have hr := z235_fits d hd
  rw [z235] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value236 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r236 digest = val (z236 d) := by
  rw [Registers.r236, value205 digest d hd hm, Registers.r29]
  have ha := z205_fits d hd
  have hb : FitsLong (-683901 : Int) := by norm_num [FitsLong]
  have hr := z236_fits d hd
  rw [z236] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value237 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r237 digest = val (z237 d) := by
  rw [Registers.r237, value165 digest d hd hm, value236 digest d hd hm]
  have ha := z165_fits d hd
  have hb := z236_fits d hd
  have hr := z237_fits d hd
  rw [z237] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value238 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r238 digest = val (z238 d) := by
  rw [Registers.r238, value237 digest d hd hm, value189 digest d hd hm]
  have ha := z237_fits d hd
  have hb := z189_fits d hd
  have hr := z238_fits d hd
  rw [z238] at hr ⊢
  exact sub_ofInt (by decide) ha hb hr

theorem value239 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r239 digest = val (z239 d) := by
  rw [Registers.r239, value238 digest d hd hm, value212 digest d hd hm]
  have ha := z238_fits d hd
  have hb := z212_fits d hd
  have hr := z239_fits d hd
  rw [z239] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value240 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r240 digest = val (z240 d) := by
  rw [Registers.r240, value226 digest d hd hm, Registers.r24]
  have ha := z226_fits d hd
  have hb : FitsLong (666643 : Int) := by norm_num [FitsLong]
  have hr := z240_fits d hd
  rw [z240] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value241 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r241 digest = val (z241 d) := by
  rw [Registers.r241, value240 digest d hd hm, value69 digest d hm]
  have ha := z240_fits d hd
  have hb := z69_fits d hd
  have hr := z241_fits d hd
  rw [z241] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value242 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r242 digest = val (z242 d) := by
  rw [Registers.r242, value226 digest d hd hm, Registers.r25]
  have ha := z226_fits d hd
  have hb : FitsLong (470296 : Int) := by norm_num [FitsLong]
  have hr := z242_fits d hd
  rw [z242] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value243 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r243 digest = val (z243 d) := by
  rw [Registers.r243, value230 digest d hd hm, value242 digest d hd hm]
  have ha := z230_fits d hd
  have hb := z242_fits d hd
  have hr := z243_fits d hd
  rw [z243] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value244 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r244 digest = val (z244 d) := by
  rw [Registers.r244, value226 digest d hd hm, Registers.r26]
  have ha := z226_fits d hd
  have hb : FitsLong (654183 : Int) := by norm_num [FitsLong]
  have hr := z244_fits d hd
  rw [z244] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value245 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r245 digest = val (z245 d) := by
  rw [Registers.r245, value232 digest d hd hm, value244 digest d hd hm]
  have ha := z232_fits d hd
  have hb := z244_fits d hd
  have hr := z245_fits d hd
  rw [z245] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value246 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r246 digest = val (z246 d) := by
  rw [Registers.r246, value226 digest d hd hm, Registers.r27]
  have ha := z226_fits d hd
  have hb : FitsLong (-997805 : Int) := by norm_num [FitsLong]
  have hr := z246_fits d hd
  rw [z246] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value247 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r247 digest = val (z247 d) := by
  rw [Registers.r247, value226 digest d hd hm, Registers.r28]
  have ha := z226_fits d hd
  have hb : FitsLong (136657 : Int) := by norm_num [FitsLong]
  have hr := z247_fits d hd
  rw [z247] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value248 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r248 digest = val (z248 d) := by
  rw [Registers.r248, value226 digest d hd hm, Registers.r29]
  have ha := z226_fits d hd
  have hb : FitsLong (-683901 : Int) := by norm_num [FitsLong]
  have hr := z248_fits d hd
  rw [z248] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value249 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r249 digest = val (z249 d) := by
  rw [Registers.r249, value228 digest d hd hm, Registers.r24]
  have ha := z228_fits d hd
  have hb : FitsLong (666643 : Int) := by norm_num [FitsLong]
  have hr := z249_fits d hd
  rw [z249] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value250 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r250 digest = val (z250 d) := by
  rw [Registers.r250, value249 digest d hd hm, value67 digest d hm]
  have ha := z249_fits d hd
  have hb := z67_fits d hd
  have hr := z250_fits d hd
  rw [z250] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value251 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r251 digest = val (z251 d) := by
  rw [Registers.r251, value228 digest d hd hm, Registers.r25]
  have ha := z228_fits d hd
  have hb : FitsLong (470296 : Int) := by norm_num [FitsLong]
  have hr := z251_fits d hd
  rw [z251] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value252 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r252 digest = val (z252 d) := by
  rw [Registers.r252, value241 digest d hd hm, value251 digest d hd hm]
  have ha := z241_fits d hd
  have hb := z251_fits d hd
  have hr := z252_fits d hd
  rw [z252] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value253 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r253 digest = val (z253 d) := by
  rw [Registers.r253, value228 digest d hd hm, Registers.r26]
  have ha := z228_fits d hd
  have hb : FitsLong (654183 : Int) := by norm_num [FitsLong]
  have hr := z253_fits d hd
  rw [z253] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value254 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r254 digest = val (z254 d) := by
  rw [Registers.r254, value243 digest d hd hm, value253 digest d hd hm]
  have ha := z243_fits d hd
  have hb := z253_fits d hd
  have hr := z254_fits d hd
  rw [z254] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value255 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r255 digest = val (z255 d) := by
  rw [Registers.r255, value228 digest d hd hm, Registers.r27]
  have ha := z228_fits d hd
  have hb : FitsLong (-997805 : Int) := by norm_num [FitsLong]
  have hr := z255_fits d hd
  rw [z255] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value256 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r256 digest = val (z256 d) := by
  rw [Registers.r256, value245 digest d hd hm, value255 digest d hd hm]
  have ha := z245_fits d hd
  have hb := z255_fits d hd
  have hr := z256_fits d hd
  rw [z256] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value257 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r257 digest = val (z257 d) := by
  rw [Registers.r257, value228 digest d hd hm, Registers.r28]
  have ha := z228_fits d hd
  have hb : FitsLong (136657 : Int) := by norm_num [FitsLong]
  have hr := z257_fits d hd
  rw [z257] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value258 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r258 digest = val (z258 d) := by
  rw [Registers.r258, value228 digest d hd hm, Registers.r29]
  have ha := z228_fits d hd
  have hb : FitsLong (-683901 : Int) := by norm_num [FitsLong]
  have hr := z258_fits d hd
  rw [z258] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value259 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r259 digest = val (z259 d) := by
  rw [Registers.r259, value180 digest d hd hm, value234 digest d hd hm]
  have ha := z180_fits d hd
  have hb := z234_fits d hd
  have hr := z259_fits d hd
  rw [z259] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value260 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r260 digest = val (z260 d) := by
  rw [Registers.r260, value259 digest d hd hm, value209 digest d hd hm]
  have ha := z259_fits d hd
  have hb := z209_fits d hd
  have hr := z260_fits d hd
  rw [z260] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value261 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r261 digest = val (z261 d) := by
  rw [Registers.r261, value260 digest d hd hm, value247 digest d hd hm]
  have ha := z260_fits d hd
  have hb := z247_fits d hd
  have hr := z261_fits d hd
  rw [z261] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value262 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r262 digest = val (z262 d) := by
  rw [Registers.r262, value261 digest d hd hm, value258 digest d hd hm]
  have ha := z261_fits d hd
  have hb := z258_fits d hd
  have hr := z262_fits d hd
  rw [z262] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value263 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r263 digest = val (z263 d) := by
  rw [Registers.r263, value221 digest d hd hm, Registers.r24]
  have ha := z221_fits d hd
  have hb : FitsLong (666643 : Int) := by norm_num [FitsLong]
  have hr := z263_fits d hd
  rw [z263] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value264 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r264 digest = val (z264 d) := by
  rw [Registers.r264, value263 digest d hd hm, value65 digest d hm]
  have ha := z263_fits d hd
  have hb := z65_fits d hd
  have hr := z264_fits d hd
  rw [z264] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value265 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r265 digest = val (z265 d) := by
  rw [Registers.r265, value221 digest d hd hm, Registers.r25]
  have ha := z221_fits d hd
  have hb : FitsLong (470296 : Int) := by norm_num [FitsLong]
  have hr := z265_fits d hd
  rw [z265] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value266 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r266 digest = val (z266 d) := by
  rw [Registers.r266, value250 digest d hd hm, value265 digest d hd hm]
  have ha := z250_fits d hd
  have hb := z265_fits d hd
  have hr := z266_fits d hd
  rw [z266] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value267 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r267 digest = val (z267 d) := by
  rw [Registers.r267, value221 digest d hd hm, Registers.r26]
  have ha := z221_fits d hd
  have hb : FitsLong (654183 : Int) := by norm_num [FitsLong]
  have hr := z267_fits d hd
  rw [z267] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value268 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r268 digest = val (z268 d) := by
  rw [Registers.r268, value252 digest d hd hm, value267 digest d hd hm]
  have ha := z252_fits d hd
  have hb := z267_fits d hd
  have hr := z268_fits d hd
  rw [z268] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value269 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r269 digest = val (z269 d) := by
  rw [Registers.r269, value221 digest d hd hm, Registers.r27]
  have ha := z221_fits d hd
  have hb : FitsLong (-997805 : Int) := by norm_num [FitsLong]
  have hr := z269_fits d hd
  rw [z269] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value270 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r270 digest = val (z270 d) := by
  rw [Registers.r270, value254 digest d hd hm, value269 digest d hd hm]
  have ha := z254_fits d hd
  have hb := z269_fits d hd
  have hr := z270_fits d hd
  rw [z270] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value271 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r271 digest = val (z271 d) := by
  rw [Registers.r271, value221 digest d hd hm, Registers.r28]
  have ha := z221_fits d hd
  have hb : FitsLong (136657 : Int) := by norm_num [FitsLong]
  have hr := z271_fits d hd
  rw [z271] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value272 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r272 digest = val (z272 d) := by
  rw [Registers.r272, value256 digest d hd hm, value271 digest d hd hm]
  have ha := z256_fits d hd
  have hb := z271_fits d hd
  have hr := z272_fits d hd
  rw [z272] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value273 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r273 digest = val (z273 d) := by
  rw [Registers.r273, value221 digest d hd hm, Registers.r29]
  have ha := z221_fits d hd
  have hb : FitsLong (-683901 : Int) := by norm_num [FitsLong]
  have hr := z273_fits d hd
  rw [z273] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value274 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r274 digest = val (z274 d) := by
  rw [Registers.r274, value223 digest d hd hm, Registers.r24]
  have ha := z223_fits d hd
  have hb : FitsLong (666643 : Int) := by norm_num [FitsLong]
  have hr := z274_fits d hd
  rw [z274] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value275 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r275 digest = val (z275 d) := by
  rw [Registers.r275, value274 digest d hd hm, value63 digest d hm]
  have ha := z274_fits d hd
  have hb := z63_fits d hd
  have hr := z275_fits d hd
  rw [z275] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value276 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r276 digest = val (z276 d) := by
  rw [Registers.r276, value223 digest d hd hm, Registers.r25]
  have ha := z223_fits d hd
  have hb : FitsLong (470296 : Int) := by norm_num [FitsLong]
  have hr := z276_fits d hd
  rw [z276] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value277 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r277 digest = val (z277 d) := by
  rw [Registers.r277, value264 digest d hd hm, value276 digest d hd hm]
  have ha := z264_fits d hd
  have hb := z276_fits d hd
  have hr := z277_fits d hd
  rw [z277] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value278 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r278 digest = val (z278 d) := by
  rw [Registers.r278, value223 digest d hd hm, Registers.r26]
  have ha := z223_fits d hd
  have hb : FitsLong (654183 : Int) := by norm_num [FitsLong]
  have hr := z278_fits d hd
  rw [z278] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value279 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r279 digest = val (z279 d) := by
  rw [Registers.r279, value266 digest d hd hm, value278 digest d hd hm]
  have ha := z266_fits d hd
  have hb := z278_fits d hd
  have hr := z279_fits d hd
  rw [z279] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value280 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r280 digest = val (z280 d) := by
  rw [Registers.r280, value223 digest d hd hm, Registers.r27]
  have ha := z223_fits d hd
  have hb : FitsLong (-997805 : Int) := by norm_num [FitsLong]
  have hr := z280_fits d hd
  rw [z280] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value281 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r281 digest = val (z281 d) := by
  rw [Registers.r281, value268 digest d hd hm, value280 digest d hd hm]
  have ha := z268_fits d hd
  have hb := z280_fits d hd
  have hr := z281_fits d hd
  rw [z281] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value282 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r282 digest = val (z282 d) := by
  rw [Registers.r282, value223 digest d hd hm, Registers.r28]
  have ha := z223_fits d hd
  have hb : FitsLong (136657 : Int) := by norm_num [FitsLong]
  have hr := z282_fits d hd
  rw [z282] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value283 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r283 digest = val (z283 d) := by
  rw [Registers.r283, value270 digest d hd hm, value282 digest d hd hm]
  have ha := z270_fits d hd
  have hb := z282_fits d hd
  have hr := z283_fits d hd
  rw [z283] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value284 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r284 digest = val (z284 d) := by
  rw [Registers.r284, value223 digest d hd hm, Registers.r29]
  have ha := z223_fits d hd
  have hb : FitsLong (-683901 : Int) := by norm_num [FitsLong]
  have hr := z284_fits d hd
  rw [z284] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value285 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r285 digest = val (z285 d) := by
  rw [Registers.r285, value272 digest d hd hm, value284 digest d hd hm]
  have ha := z272_fits d hd
  have hb := z284_fits d hd
  have hr := z285_fits d hd
  rw [z285] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value286 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r286 digest = val (z286 d) := by
  rw [Registers.r286, value216 digest d hd hm, Registers.r24]
  have ha := z216_fits d hd
  have hb : FitsLong (666643 : Int) := by norm_num [FitsLong]
  have hr := z286_fits d hd
  rw [z286] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value287 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r287 digest = val (z287 d) := by
  rw [Registers.r287, value286 digest d hd hm, value61 digest d hm]
  have ha := z286_fits d hd
  have hb := z61_fits d hd
  have hr := z287_fits d hd
  rw [z287] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value288 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r288 digest = val (z288 d) := by
  rw [Registers.r288, value216 digest d hd hm, Registers.r25]
  have ha := z216_fits d hd
  have hb : FitsLong (470296 : Int) := by norm_num [FitsLong]
  have hr := z288_fits d hd
  rw [z288] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value289 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r289 digest = val (z289 d) := by
  rw [Registers.r289, value275 digest d hd hm, value288 digest d hd hm]
  have ha := z275_fits d hd
  have hb := z288_fits d hd
  have hr := z289_fits d hd
  rw [z289] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value290 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r290 digest = val (z290 d) := by
  rw [Registers.r290, value216 digest d hd hm, Registers.r26]
  have ha := z216_fits d hd
  have hb : FitsLong (654183 : Int) := by norm_num [FitsLong]
  have hr := z290_fits d hd
  rw [z290] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value291 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r291 digest = val (z291 d) := by
  rw [Registers.r291, value277 digest d hd hm, value290 digest d hd hm]
  have ha := z277_fits d hd
  have hb := z290_fits d hd
  have hr := z291_fits d hd
  rw [z291] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value292 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r292 digest = val (z292 d) := by
  rw [Registers.r292, value216 digest d hd hm, Registers.r27]
  have ha := z216_fits d hd
  have hb : FitsLong (-997805 : Int) := by norm_num [FitsLong]
  have hr := z292_fits d hd
  rw [z292] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value293 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r293 digest = val (z293 d) := by
  rw [Registers.r293, value279 digest d hd hm, value292 digest d hd hm]
  have ha := z279_fits d hd
  have hb := z292_fits d hd
  have hr := z293_fits d hd
  rw [z293] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value294 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r294 digest = val (z294 d) := by
  rw [Registers.r294, value216 digest d hd hm, Registers.r28]
  have ha := z216_fits d hd
  have hb : FitsLong (136657 : Int) := by norm_num [FitsLong]
  have hr := z294_fits d hd
  rw [z294] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value295 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r295 digest = val (z295 d) := by
  rw [Registers.r295, value281 digest d hd hm, value294 digest d hd hm]
  have ha := z281_fits d hd
  have hb := z294_fits d hd
  have hr := z295_fits d hd
  rw [z295] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value296 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r296 digest = val (z296 d) := by
  rw [Registers.r296, value216 digest d hd hm, Registers.r29]
  have ha := z216_fits d hd
  have hb : FitsLong (-683901 : Int) := by norm_num [FitsLong]
  have hr := z296_fits d hd
  rw [z296] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value297 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r297 digest = val (z297 d) := by
  rw [Registers.r297, value283 digest d hd hm, value296 digest d hd hm]
  have ha := z283_fits d hd
  have hb := z296_fits d hd
  have hr := z297_fits d hd
  rw [z297] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

end Firedancer.Common.ScalarArithmetic.MachineArithmetic
