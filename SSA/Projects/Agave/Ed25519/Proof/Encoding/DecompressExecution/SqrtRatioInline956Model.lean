import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioExecutionComposition
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtWords
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixOperations

/-! The exact final sqrt-ratio inline tail. The only incoming facts concern
registers, live memory and the two candidate limb arrays at pc956. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline956
open LeanMLIR.RIR SerialFieldMul SerialPoint.Execution
open Reduce64.Execution (SmallRange)
open Decode.InlinePrefix (vector_two carry_operation carry_vector_operation fold_operation)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def byte (b : Bool) : BitVec 8 := if b then 1#8 else 0#8

def choose (b : BitVec 8) (x y : BitVec 64) : BitVec 64 :=
  ((y ^^^ x) &&& (0#64 - b.setWidth 64)) ^^^ x

theorem choose_byte (b : Bool) (x y : BitVec 64) :
    choose (byte b) x y = if b then y else x := by
  cases b
  · simp [choose, byte]
  · change ((y ^^^ x) &&& BitVec.allOnes 64) ^^^ x = y
    rw [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem mask_safe (b : BitVec 8) :
    Operation.sub {nsw := true} (.value 0#64) (.value (b.setWidth 64)) =
      .value (0#64 - b.setWidth 64) := by
  have hb := b.isLt
  have hi : (b.setWidth 64).toInt = ((b.setWidth 64).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by simp; omega)
  have h : (0#64).ssubOverflow (b.setWidth 64) = false := by
    simp [BitVec.ssubOverflow, hi, BitVec.toNat_setWidth] <;> omega
  simp [Operation.sub, h]

structure Registers (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) : Prop where
  e3 : E.read (%3) = .value (8#64)
  e5 : E.read (%5) = .value (24#64)
  e7 : E.read (%7) = .value (51#64)
  e8 : E.read (%8) = .value (2251799813685247#64)
  e9 : E.read (%9) = .value (19#64)
  e10 : E.read (%10) = .value (1#64)
  e50 : E.read (%50) = .value (0#64)
  e53 : E.read (%53) = Ty.poisoned (.vec 2 64)
  e54 : E.read (%54) = .value (2251799813684944#64)
  e55 : E.read (%55) = Ty.wrap (#v[36028797018963664#64, 36028797018963952#64])
  e56 : E.read (%56) = Ty.wrap (#v[2251799813685232#64, 2251799813685232#64])
  e57 : E.read (%57) = Ty.wrap (#v[51#64, 51#64])
  e58 : E.read (%58) = Ty.wrap (#v[2251799813685247#64, 2251799813685247#64])
  e59 : E.read (%59) = .value (36028797018963952#64)
  e60 : E.read (%60) = Ty.wrap (#v[36028797018963952#64, 36028797018963952#64])
  e61 : E.read (%61) = .value (1#8)
  e71 : E.read (%71) = .value (t)
  e79 : E.read (%79) = .value (r)
  e733 : E.read (%733) = .value (b)

def v734 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  b.setWidth 64

def v735 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  0#64 - (v734 r t b x y)

def v736 (r t : Pointer) (b : BitVec 8) (x y : Words) : Pointer :=
  r.add (8#64)

def v737 (r t : Pointer) (b : BitVec 8) (x y : Words) : Pointer :=
  t.add (8#64)

def v738 (r t : Pointer) (b : BitVec 8) (x y : Words) : Pointer :=
  r.add (24#64)

def v739 (r t : Pointer) (b : BitVec 8) (x y : Words) : Pointer :=
  t.add (24#64)

def v740 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[x 0, x 1]

def v741 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[y 0, y 1]

def v742 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[x 1, x 2]

def v743 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[y 1, y 2]

def v744 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v741 r t b x y)[0] ^^^ (v740 r t b x y)[0], (v741 r t b x y)[1] ^^^ (v740 r t b x y)[1]]

def v745 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v743 r t b x y)[0] ^^^ (v742 r t b x y)[0], (v743 r t b x y)[1] ^^^ (v742 r t b x y)[1]]

def v746 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (PoisonOr (BitVec 64)) 2 :=
  #v[.value (v735 r t b x y), .poison]

def v747 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v735 r t b x y), (v735 r t b x y)]

def v748 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v744 r t b x y)[0] &&& (v747 r t b x y)[0], (v744 r t b x y)[1] &&& (v747 r t b x y)[1]]

def v749 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v745 r t b x y)[0] &&& (v747 r t b x y)[0], (v745 r t b x y)[1] &&& (v747 r t b x y)[1]]

def v750 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v748 r t b x y)[0] ^^^ (v740 r t b x y)[0], (v748 r t b x y)[1] ^^^ (v740 r t b x y)[1]]

def v751 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v750 r t b x y)[0]

def v752 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v749 r t b x y)[0] ^^^ (v742 r t b x y)[0], (v749 r t b x y)[1] ^^^ (v742 r t b x y)[1]]

def v753 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v752 r t b x y)[1]

def v754 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v751 r t b x y) >>> 51

def v755 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v752 r t b x y)[0]

def v756 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v755 r t b x y) >>> 51

def v757 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v753 r t b x y) >>> 51

def v758 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v751 r t b x y) &&& 2251799813685247#64

def v759 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v755 r t b x y) &&& 2251799813685247#64

def v760 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v753 r t b x y) &&& 2251799813685247#64

def v761 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v759 r t b x y) + (v754 r t b x y)

def v762 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v760 r t b x y) + (v756 r t b x y)

def v763 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  2251799813684944#64 - (v751 r t b x y)

def v764 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[36028797018963664#64 - (v750 r t b x y)[0], 36028797018963952#64 - (v750 r t b x y)[1]]

def v765 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[2251799813685232#64 - (v752 r t b x y)[0], 2251799813685232#64 - (v752 r t b x y)[1]]

def v766 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v764 r t b x y)[0] >>> 51, (v764 r t b x y)[1] >>> 51]

def v767 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v763 r t b x y) &&& 2251799813685247#64

def v768 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v765 r t b x y)[0] &&& 2251799813685247#64, (v765 r t b x y)[1] &&& 2251799813685247#64]

def v769 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v768 r t b x y)[0] + (v766 r t b x y)[0], (v768 r t b x y)[1] + (v766 r t b x y)[1]]

def v770 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v769 r t b x y)[0] ^^^ (v752 r t b x y)[0], (v769 r t b x y)[1] ^^^ (v752 r t b x y)[1]]

def v771 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[x 3, x 4]

def v772 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[y 3, y 4]

def v773 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v772 r t b x y)[0] ^^^ (v771 r t b x y)[0], (v772 r t b x y)[1] ^^^ (v771 r t b x y)[1]]

def v774 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v773 r t b x y)[0] &&& (v747 r t b x y)[0], (v773 r t b x y)[1] &&& (v747 r t b x y)[1]]

def v775 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v774 r t b x y)[0] ^^^ (v771 r t b x y)[0], (v774 r t b x y)[1] ^^^ (v771 r t b x y)[1]]

def v776 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v775 r t b x y)[1]

def v777 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v775 r t b x y)[0]

def v778 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v777 r t b x y) >>> 51

def v779 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v776 r t b x y) >>> 51

def v780 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v777 r t b x y) &&& 2251799813685247#64

def v781 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v776 r t b x y) &&& 2251799813685247#64

def v782 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v779 r t b x y) * 19#64

def v783 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v781 r t b x y) + (v778 r t b x y)

def v784 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  36028797018963952#64 - (v776 r t b x y)

def v785 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[2251799813685232#64 - (v775 r t b x y)[0], 2251799813685232#64 - (v775 r t b x y)[1]]

def v786 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v784 r t b x y) >>> 51

def v787 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v752 r t b x y)[1], (v775 r t b x y)[0]]

def v788 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[36028797018963952#64 - (v787 r t b x y)[0], 36028797018963952#64 - (v787 r t b x y)[1]]

def v789 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v785 r t b x y)[0] &&& 2251799813685247#64, (v785 r t b x y)[1] &&& 2251799813685247#64]

def v790 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v786 r t b x y) * 19#64

def v791 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v782 r t b x y) + (v758 r t b x y)

def v792 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v780 r t b x y) + (v757 r t b x y)

def v793 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v791 r t b x y) + 19#64

def v794 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v793 r t b x y) >>> 51

def v795 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v761 r t b x y) + (v794 r t b x y)

def v796 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v795 r t b x y) >>> 51

def v797 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v762 r t b x y) + (v796 r t b x y)

def v798 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v797 r t b x y) >>> 51

def v799 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v792 r t b x y) + (v798 r t b x y)

def v800 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v799 r t b x y) >>> 51

def v801 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v783 r t b x y) + (v800 r t b x y)

def v802 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v801 r t b x y) >>> 51

def v803 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v802 r t b x y) + (v791 r t b x y)

def v804 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 8 :=
  (v803 r t b x y).setWidth 8

def v805 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 8 :=
  (v804 r t b x y) &&& 1#8

def v806 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 8 :=
  (v805 r t b x y)

def v807 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v788 r t b x y)[0] >>> 51, (v788 r t b x y)[1] >>> 51]

def v808 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v790 r t b x y) + (v767 r t b x y)

def v809 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v789 r t b x y)[0] + (v807 r t b x y)[0], (v789 r t b x y)[1] + (v807 r t b x y)[1]]

def v810 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v806 r t b x y).setWidth 64

def v811 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  0#64 - (v810 r t b x y)

def v812 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v808 r t b x y) ^^^ (v751 r t b x y)

def v813 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v812 r t b x y) &&& (v811 r t b x y)

def v814 (r t : Pointer) (b : BitVec 8) (x y : Words) : BitVec 64 :=
  (v813 r t b x y) ^^^ (v751 r t b x y)

def v815 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (PoisonOr (BitVec 64)) 2 :=
  #v[.value (v811 r t b x y), .poison]

def v816 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v811 r t b x y), (v811 r t b x y)]

def v817 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v770 r t b x y)[0] &&& (v816 r t b x y)[0], (v770 r t b x y)[1] &&& (v816 r t b x y)[1]]

def v818 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v817 r t b x y)[0] ^^^ (v752 r t b x y)[0], (v817 r t b x y)[1] ^^^ (v752 r t b x y)[1]]

def v819 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v809 r t b x y)[0] ^^^ (v775 r t b x y)[0], (v809 r t b x y)[1] ^^^ (v775 r t b x y)[1]]

def v820 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v819 r t b x y)[0] &&& (v816 r t b x y)[0], (v819 r t b x y)[1] &&& (v816 r t b x y)[1]]

def v821 (r t : Pointer) (b : BitVec 8) (x y : Words) : Vector (BitVec 64) 2 :=
  #v[(v820 r t b x y)[0] ^^^ (v775 r t b x y)[0], (v820 r t b x y)[1] ^^^ (v775 r t b x y)[1]]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline956
