import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.IntegerFits
import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.Registers

namespace Firedancer.Common.ScalarArithmetic.MachineArithmetic
open LeanMLIR SLLVM
open InstCombine (LLVM)
open R43x6 (FitsLong)
open IntegerRegisters

set_option maxHeartbeats 2000000

/-- The 24 decoded source digits, before any arithmetic fold. -/
structure InputMatches (digest : BitVec 512) (d : Digits) : Prop where
  r61 : Registers.r61 digest = val (d 0)
  r63 : Registers.r63 digest = val (d 1)
  r65 : Registers.r65 digest = val (d 2)
  r67 : Registers.r67 digest = val (d 3)
  r69 : Registers.r69 digest = val (d 4)
  r71 : Registers.r71 digest = val (d 5)
  r73 : Registers.r73 digest = val (d 6)
  r75 : Registers.r75 digest = val (d 7)
  r77 : Registers.r77 digest = val (d 8)
  r79 : Registers.r79 digest = val (d 9)
  r81 : Registers.r81 digest = val (d 10)
  r83 : Registers.r83 digest = val (d 11)
  r85 : Registers.r85 digest = val (d 12)
  r87 : Registers.r87 digest = val (d 13)
  r89 : Registers.r89 digest = val (d 14)
  r91 : Registers.r91 digest = val (d 15)
  r93 : Registers.r93 digest = val (d 16)
  r95 : Registers.r95 digest = val (d 17)
  r97 : Registers.r97 digest = val (d 18)
  r99 : Registers.r99 digest = val (d 19)
  r101 : Registers.r101 digest = val (d 20)
  r103 : Registers.r103 digest = val (d 21)
  r105 : Registers.r105 digest = val (d 22)
  r106 : Registers.r106 digest = val (d 23)

theorem value61 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r61 digest = val (z61 d) := hm.r61

theorem value63 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r63 digest = val (z63 d) := hm.r63

theorem value65 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r65 digest = val (z65 d) := hm.r65

theorem value67 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r67 digest = val (z67 d) := hm.r67

theorem value69 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r69 digest = val (z69 d) := hm.r69

theorem value71 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r71 digest = val (z71 d) := hm.r71

theorem value73 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r73 digest = val (z73 d) := hm.r73

theorem value75 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r75 digest = val (z75 d) := hm.r75

theorem value77 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r77 digest = val (z77 d) := hm.r77

theorem value79 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r79 digest = val (z79 d) := hm.r79

theorem value81 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r81 digest = val (z81 d) := hm.r81

theorem value83 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r83 digest = val (z83 d) := hm.r83

theorem value85 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r85 digest = val (z85 d) := hm.r85

theorem value87 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r87 digest = val (z87 d) := hm.r87

theorem value89 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r89 digest = val (z89 d) := hm.r89

theorem value91 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r91 digest = val (z91 d) := hm.r91

theorem value93 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r93 digest = val (z93 d) := hm.r93

theorem value95 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r95 digest = val (z95 d) := hm.r95

theorem value97 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r97 digest = val (z97 d) := hm.r97

theorem value99 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r99 digest = val (z99 d) := hm.r99

theorem value101 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r101 digest = val (z101 d) := hm.r101

theorem value103 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r103 digest = val (z103 d) := hm.r103

theorem value105 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r105 digest = val (z105 d) := hm.r105

theorem value106 (digest : BitVec 512) (d : Digits) (hm : InputMatches digest d) :
    Registers.r106 digest = val (z106 d) := hm.r106

theorem value107 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r107 digest = val (z107 d) := by
  rw [Registers.r107, value106 digest d hm, Registers.r24]
  have ha := z106_fits d hd
  have hb : FitsLong (666643 : Int) := by norm_num [FitsLong]
  have hr := z107_fits d hd
  rw [z107] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z106_bounds d hd
  constructor <;> omega

theorem value108 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r108 digest = val (z108 d) := by
  rw [Registers.r108, value107 digest d hd hm, value83 digest d hm]
  have ha := z107_fits d hd
  have hb := z83_fits d hd
  have hr := z108_fits d hd
  rw [z108] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z107_bounds d hd
  have hbb := z83_bounds d hd
  constructor <;> omega

theorem value109 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r109 digest = val (z109 d) := by
  rw [Registers.r109, value106 digest d hm, Registers.r25]
  have ha := z106_fits d hd
  have hb : FitsLong (470296 : Int) := by norm_num [FitsLong]
  have hr := z109_fits d hd
  rw [z109] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z106_bounds d hd
  constructor <;> omega

theorem value110 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r110 digest = val (z110 d) := by
  rw [Registers.r110, value109 digest d hd hm, value85 digest d hm]
  have ha := z109_fits d hd
  have hb := z85_fits d hd
  have hr := z110_fits d hd
  rw [z110] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z109_bounds d hd
  have hbb := z85_bounds d hd
  constructor <;> omega

theorem value111 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r111 digest = val (z111 d) := by
  rw [Registers.r111, value106 digest d hm, Registers.r26]
  have ha := z106_fits d hd
  have hb : FitsLong (654183 : Int) := by norm_num [FitsLong]
  have hr := z111_fits d hd
  rw [z111] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z106_bounds d hd
  constructor <;> omega

theorem value112 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r112 digest = val (z112 d) := by
  rw [Registers.r112, value111 digest d hd hm, value87 digest d hm]
  have ha := z111_fits d hd
  have hb := z87_fits d hd
  have hr := z112_fits d hd
  rw [z112] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z111_bounds d hd
  have hbb := z87_bounds d hd
  constructor <;> omega

theorem value113 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r113 digest = val (z113 d) := by
  rw [Registers.r113, value106 digest d hm, Registers.r27]
  have ha := z106_fits d hd
  have hb : FitsLong (-997805 : Int) := by norm_num [FitsLong]
  have hr := z113_fits d hd
  rw [z113] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value114 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r114 digest = val (z114 d) := by
  rw [Registers.r114, value113 digest d hd hm, value89 digest d hm]
  have ha := z113_fits d hd
  have hb := z89_fits d hd
  have hr := z114_fits d hd
  rw [z114] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value115 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r115 digest = val (z115 d) := by
  rw [Registers.r115, value106 digest d hm, Registers.r28]
  have ha := z106_fits d hd
  have hb : FitsLong (136657 : Int) := by norm_num [FitsLong]
  have hr := z115_fits d hd
  rw [z115] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z106_bounds d hd
  constructor <;> omega

theorem value116 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r116 digest = val (z116 d) := by
  rw [Registers.r116, value115 digest d hd hm, value91 digest d hm]
  have ha := z115_fits d hd
  have hb := z91_fits d hd
  have hr := z116_fits d hd
  rw [z116] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z115_bounds d hd
  have hbb := z91_bounds d hd
  constructor <;> omega

theorem value117 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r117 digest = val (z117 d) := by
  rw [Registers.r117, value106 digest d hm, Registers.r29]
  have ha := z106_fits d hd
  have hb : FitsLong (-683901 : Int) := by norm_num [FitsLong]
  have hr := z117_fits d hd
  rw [z117] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value118 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r118 digest = val (z118 d) := by
  rw [Registers.r118, value117 digest d hd hm, value93 digest d hm]
  have ha := z117_fits d hd
  have hb := z93_fits d hd
  have hr := z118_fits d hd
  rw [z118] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value119 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r119 digest = val (z119 d) := by
  rw [Registers.r119, value105 digest d hm, Registers.r24]
  have ha := z105_fits d hd
  have hb : FitsLong (666643 : Int) := by norm_num [FitsLong]
  have hr := z119_fits d hd
  rw [z119] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z105_bounds d hd
  constructor <;> omega

theorem value120 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r120 digest = val (z120 d) := by
  rw [Registers.r120, value105 digest d hm, Registers.r25]
  have ha := z105_fits d hd
  have hb : FitsLong (470296 : Int) := by norm_num [FitsLong]
  have hr := z120_fits d hd
  rw [z120] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z105_bounds d hd
  constructor <;> omega

theorem value121 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r121 digest = val (z121 d) := by
  rw [Registers.r121, value105 digest d hm, Registers.r26]
  have ha := z105_fits d hd
  have hb : FitsLong (654183 : Int) := by norm_num [FitsLong]
  have hr := z121_fits d hd
  rw [z121] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z105_bounds d hd
  constructor <;> omega

theorem value122 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r122 digest = val (z122 d) := by
  rw [Registers.r122, value105 digest d hm, Registers.r27]
  have ha := z105_fits d hd
  have hb : FitsLong (-997805 : Int) := by norm_num [FitsLong]
  have hr := z122_fits d hd
  rw [z122] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value123 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r123 digest = val (z123 d) := by
  rw [Registers.r123, value105 digest d hm, Registers.r28]
  have ha := z105_fits d hd
  have hb : FitsLong (136657 : Int) := by norm_num [FitsLong]
  have hr := z123_fits d hd
  rw [z123] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z105_bounds d hd
  constructor <;> omega

theorem value124 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r124 digest = val (z124 d) := by
  rw [Registers.r124, value114 digest d hd hm, value123 digest d hd hm]
  have ha := z114_fits d hd
  have hb := z123_fits d hd
  have hr := z124_fits d hd
  rw [z124] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value125 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r125 digest = val (z125 d) := by
  rw [Registers.r125, value105 digest d hm, Registers.r29]
  have ha := z105_fits d hd
  have hb : FitsLong (-683901 : Int) := by norm_num [FitsLong]
  have hr := z125_fits d hd
  rw [z125] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value126 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r126 digest = val (z126 d) := by
  rw [Registers.r126, value116 digest d hd hm, value125 digest d hd hm]
  have ha := z116_fits d hd
  have hb := z125_fits d hd
  have hr := z126_fits d hd
  rw [z126] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value127 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r127 digest = val (z127 d) := by
  rw [Registers.r127, value103 digest d hm, Registers.r24]
  have ha := z103_fits d hd
  have hb : FitsLong (666643 : Int) := by norm_num [FitsLong]
  have hr := z127_fits d hd
  rw [z127] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z103_bounds d hd
  constructor <;> omega

theorem value128 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r128 digest = val (z128 d) := by
  rw [Registers.r128, value103 digest d hm, Registers.r25]
  have ha := z103_fits d hd
  have hb : FitsLong (470296 : Int) := by norm_num [FitsLong]
  have hr := z128_fits d hd
  rw [z128] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z103_bounds d hd
  constructor <;> omega

theorem value129 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r129 digest = val (z129 d) := by
  rw [Registers.r129, value103 digest d hm, Registers.r26]
  have ha := z103_fits d hd
  have hb : FitsLong (654183 : Int) := by norm_num [FitsLong]
  have hr := z129_fits d hd
  rw [z129] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z103_bounds d hd
  constructor <;> omega

theorem value130 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r130 digest = val (z130 d) := by
  rw [Registers.r130, value103 digest d hm, Registers.r27]
  have ha := z103_fits d hd
  have hb : FitsLong (-997805 : Int) := by norm_num [FitsLong]
  have hr := z130_fits d hd
  rw [z130] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value131 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r131 digest = val (z131 d) := by
  rw [Registers.r131, value103 digest d hm, Registers.r28]
  have ha := z103_fits d hd
  have hb : FitsLong (136657 : Int) := by norm_num [FitsLong]
  have hr := z131_fits d hd
  rw [z131] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z103_bounds d hd
  constructor <;> omega

theorem value132 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r132 digest = val (z132 d) := by
  rw [Registers.r132, value103 digest d hm, Registers.r29]
  have ha := z103_fits d hd
  have hb : FitsLong (-683901 : Int) := by norm_num [FitsLong]
  have hr := z132_fits d hd
  rw [z132] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value133 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r133 digest = val (z133 d) := by
  rw [Registers.r133, value124 digest d hd hm, value132 digest d hd hm]
  have ha := z124_fits d hd
  have hb := z132_fits d hd
  have hr := z133_fits d hd
  rw [z133] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value134 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r134 digest = val (z134 d) := by
  rw [Registers.r134, value101 digest d hm, Registers.r24]
  have ha := z101_fits d hd
  have hb : FitsLong (666643 : Int) := by norm_num [FitsLong]
  have hr := z134_fits d hd
  rw [z134] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z101_bounds d hd
  constructor <;> omega

theorem value135 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r135 digest = val (z135 d) := by
  rw [Registers.r135, value134 digest d hd hm, value77 digest d hm]
  have ha := z134_fits d hd
  have hb := z77_fits d hd
  have hr := z135_fits d hd
  rw [z135] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z134_bounds d hd
  have hbb := z77_bounds d hd
  constructor <;> omega

theorem value136 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r136 digest = val (z136 d) := by
  rw [Registers.r136, value101 digest d hm, Registers.r25]
  have ha := z101_fits d hd
  have hb : FitsLong (470296 : Int) := by norm_num [FitsLong]
  have hr := z136_fits d hd
  rw [z136] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z101_bounds d hd
  constructor <;> omega

theorem value137 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r137 digest = val (z137 d) := by
  rw [Registers.r137, value101 digest d hm, Registers.r26]
  have ha := z101_fits d hd
  have hb : FitsLong (654183 : Int) := by norm_num [FitsLong]
  have hr := z137_fits d hd
  rw [z137] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z101_bounds d hd
  constructor <;> omega

theorem value138 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r138 digest = val (z138 d) := by
  rw [Registers.r138, value101 digest d hm, Registers.r27]
  have ha := z101_fits d hd
  have hb : FitsLong (-997805 : Int) := by norm_num [FitsLong]
  have hr := z138_fits d hd
  rw [z138] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value139 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r139 digest = val (z139 d) := by
  rw [Registers.r139, value101 digest d hm, Registers.r28]
  have ha := z101_fits d hd
  have hb : FitsLong (136657 : Int) := by norm_num [FitsLong]
  have hr := z139_fits d hd
  rw [z139] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z101_bounds d hd
  constructor <;> omega

theorem value140 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r140 digest = val (z140 d) := by
  rw [Registers.r140, value101 digest d hm, Registers.r29]
  have ha := z101_fits d hd
  have hb : FitsLong (-683901 : Int) := by norm_num [FitsLong]
  have hr := z140_fits d hd
  rw [z140] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value141 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r141 digest = val (z141 d) := by
  rw [Registers.r141, value99 digest d hm, Registers.r24]
  have ha := z99_fits d hd
  have hb : FitsLong (666643 : Int) := by norm_num [FitsLong]
  have hr := z141_fits d hd
  rw [z141] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z99_bounds d hd
  constructor <;> omega

theorem value142 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r142 digest = val (z142 d) := by
  rw [Registers.r142, value141 digest d hd hm, value75 digest d hm]
  have ha := z141_fits d hd
  have hb := z75_fits d hd
  have hr := z142_fits d hd
  rw [z142] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z141_bounds d hd
  have hbb := z75_bounds d hd
  constructor <;> omega

theorem value143 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r143 digest = val (z143 d) := by
  rw [Registers.r143, value99 digest d hm, Registers.r25]
  have ha := z99_fits d hd
  have hb : FitsLong (470296 : Int) := by norm_num [FitsLong]
  have hr := z143_fits d hd
  rw [z143] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z99_bounds d hd
  constructor <;> omega

theorem value144 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r144 digest = val (z144 d) := by
  rw [Registers.r144, value135 digest d hd hm, value143 digest d hd hm]
  have ha := z135_fits d hd
  have hb := z143_fits d hd
  have hr := z144_fits d hd
  rw [z144] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z135_bounds d hd
  have hbb := z143_bounds d hd
  constructor <;> omega

theorem value145 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r145 digest = val (z145 d) := by
  rw [Registers.r145, value99 digest d hm, Registers.r26]
  have ha := z99_fits d hd
  have hb : FitsLong (654183 : Int) := by norm_num [FitsLong]
  have hr := z145_fits d hd
  rw [z145] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z99_bounds d hd
  constructor <;> omega

theorem value146 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r146 digest = val (z146 d) := by
  rw [Registers.r146, value99 digest d hm, Registers.r27]
  have ha := z99_fits d hd
  have hb : FitsLong (-997805 : Int) := by norm_num [FitsLong]
  have hr := z146_fits d hd
  rw [z146] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value147 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r147 digest = val (z147 d) := by
  rw [Registers.r147, value99 digest d hm, Registers.r28]
  have ha := z99_fits d hd
  have hb : FitsLong (136657 : Int) := by norm_num [FitsLong]
  have hr := z147_fits d hd
  rw [z147] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z99_bounds d hd
  constructor <;> omega

theorem value148 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r148 digest = val (z148 d) := by
  rw [Registers.r148, value99 digest d hm, Registers.r29]
  have ha := z99_fits d hd
  have hb : FitsLong (-683901 : Int) := by norm_num [FitsLong]
  have hr := z148_fits d hd
  rw [z148] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value149 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r149 digest = val (z149 d) := by
  rw [Registers.r149, value110 digest d hd hm, value139 digest d hd hm]
  have ha := z110_fits d hd
  have hb := z139_fits d hd
  have hr := z149_fits d hd
  rw [z149] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z110_bounds d hd
  have hbb := z139_bounds d hd
  constructor <;> omega

theorem value150 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r150 digest = val (z150 d) := by
  rw [Registers.r150, value149 digest d hd hm, value148 digest d hd hm]
  have ha := z149_fits d hd
  have hb := z148_fits d hd
  have hr := z150_fits d hd
  rw [z150] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value151 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r151 digest = val (z151 d) := by
  rw [Registers.r151, value150 digest d hd hm, value121 digest d hd hm]
  have ha := z150_fits d hd
  have hb := z121_fits d hd
  have hr := z151_fits d hd
  rw [z151] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value152 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r152 digest = val (z152 d) := by
  rw [Registers.r152, value151 digest d hd hm, value130 digest d hd hm]
  have ha := z151_fits d hd
  have hb := z130_fits d hd
  have hr := z152_fits d hd
  rw [z152] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value153 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r153 digest = val (z153 d) := by
  rw [Registers.r153, value97 digest d hm, Registers.r24]
  have ha := z97_fits d hd
  have hb : FitsLong (666643 : Int) := by norm_num [FitsLong]
  have hr := z153_fits d hd
  rw [z153] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z97_bounds d hd
  constructor <;> omega

theorem value154 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r154 digest = val (z154 d) := by
  rw [Registers.r154, value153 digest d hd hm, value73 digest d hm]
  have ha := z153_fits d hd
  have hb := z73_fits d hd
  have hr := z154_fits d hd
  rw [z154] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z153_bounds d hd
  have hbb := z73_bounds d hd
  constructor <;> omega

theorem value155 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r155 digest = val (z155 d) := by
  rw [Registers.r155, value97 digest d hm, Registers.r25]
  have ha := z97_fits d hd
  have hb : FitsLong (470296 : Int) := by norm_num [FitsLong]
  have hr := z155_fits d hd
  rw [z155] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z97_bounds d hd
  constructor <;> omega

theorem value156 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r156 digest = val (z156 d) := by
  rw [Registers.r156, value142 digest d hd hm, value155 digest d hd hm]
  have ha := z142_fits d hd
  have hb := z155_fits d hd
  have hr := z156_fits d hd
  rw [z156] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z142_bounds d hd
  have hbb := z155_bounds d hd
  constructor <;> omega

theorem value157 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r157 digest = val (z157 d) := by
  rw [Registers.r157, value97 digest d hm, Registers.r26]
  have ha := z97_fits d hd
  have hb : FitsLong (654183 : Int) := by norm_num [FitsLong]
  have hr := z157_fits d hd
  rw [z157] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z97_bounds d hd
  constructor <;> omega

theorem value158 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r158 digest = val (z158 d) := by
  rw [Registers.r158, value144 digest d hd hm, value157 digest d hd hm]
  have ha := z144_fits d hd
  have hb := z157_fits d hd
  have hr := z158_fits d hd
  rw [z158] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z144_bounds d hd
  have hbb := z157_bounds d hd
  constructor <;> omega

theorem value159 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r159 digest = val (z159 d) := by
  rw [Registers.r159, value97 digest d hm, Registers.r27]
  have ha := z97_fits d hd
  have hb : FitsLong (-997805 : Int) := by norm_num [FitsLong]
  have hr := z159_fits d hd
  rw [z159] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value160 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r160 digest = val (z160 d) := by
  rw [Registers.r160, value97 digest d hm, Registers.r28]
  have ha := z97_fits d hd
  have hb : FitsLong (136657 : Int) := by norm_num [FitsLong]
  have hr := z160_fits d hd
  rw [z160] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  have hab := z97_bounds d hd
  constructor <;> omega

theorem value161 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r161 digest = val (z161 d) := by
  rw [Registers.r161, value137 digest d hd hm, value81 digest d hm]
  have ha := z137_fits d hd
  have hb := z81_fits d hd
  have hr := z161_fits d hd
  rw [z161] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  have hab := z137_bounds d hd
  have hbb := z81_bounds d hd
  constructor <;> omega

theorem value162 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r162 digest = val (z162 d) := by
  rw [Registers.r162, value161 digest d hd hm, value146 digest d hd hm]
  have ha := z161_fits d hd
  have hb := z146_fits d hd
  have hr := z162_fits d hd
  rw [z162] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value163 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r163 digest = val (z163 d) := by
  rw [Registers.r163, value162 digest d hd hm, value160 digest d hd hm]
  have ha := z162_fits d hd
  have hb := z160_fits d hd
  have hr := z163_fits d hd
  rw [z163] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value164 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r164 digest = val (z164 d) := by
  rw [Registers.r164, value163 digest d hd hm, value119 digest d hd hm]
  have ha := z163_fits d hd
  have hb := z119_fits d hd
  have hr := z164_fits d hd
  rw [z164] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value165 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r165 digest = val (z165 d) := by
  rw [Registers.r165, value164 digest d hd hm, value128 digest d hd hm]
  have ha := z164_fits d hd
  have hb := z128_fits d hd
  have hr := z165_fits d hd
  rw [z165] at hr ⊢
  apply add_ofInt ha hb hr
  intro hflag
  cases hflag

theorem value166 (digest : BitVec 512) (d : Digits) (hd : Bounded d)
    (hm : InputMatches digest d) : Registers.r166 digest = val (z166 d) := by
  rw [Registers.r166, value97 digest d hm, Registers.r29]
  have ha := z97_fits d hd
  have hb : FitsLong (-683901 : Int) := by norm_num [FitsLong]
  have hr := z166_fits d hd
  rw [z166] at hr ⊢
  apply mul_flags_ofInt ha hb hr
  intro hflag
  cases hflag

end Firedancer.Common.ScalarArithmetic.MachineArithmetic
