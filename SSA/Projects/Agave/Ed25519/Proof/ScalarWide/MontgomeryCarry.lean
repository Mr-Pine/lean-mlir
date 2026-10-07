import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MaskedFlags
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WordSchedule

/-! Actual 86-instruction carry/repacking window, with every value nonpoison.
Wrapping additions/truncations remain word operations. Natural congruence
and the quotient-limb bound are separate arithmetic refinement obligations. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR

/-- Source register values are named independently to retain sharing during kernel reduction. -/
private def carryValue102 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (z 0).setWidth 64

private def carryValue103 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue102 z) * 1439961107955227#64

private def carryValue104 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue103 z) &&& 4503599627370495#64

private def carryValue105 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue104 z).setWidth 128

private def carryValue106 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue105 z) * 671914833335277#128

private def carryValue107 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue106 z) + (z 0)

private def carryValue108 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue107 z) >>> (52 : Nat)

private def carryValue109 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue105 z) * 3916664325105025#128

private def carryValue110 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue109 z) + (z 1)

private def carryValue111 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue110 z) + (carryValue108 z)

private def carryValue112 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue111 z).setWidth 64

private def carryValue113 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue112 z) * 1439961107955227#64

private def carryValue114 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue113 z) &&& 4503599627370495#64

private def carryValue115 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue114 z).setWidth 128

private def carryValue116 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue115 z) * 671914833335277#128

private def carryValue117 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue116 z) + (carryValue111 z)

private def carryValue118 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue117 z) >>> (52 : Nat)

private def carryValue119 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue105 z) * 1367801#128

private def carryValue120 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue115 z) * 3916664325105025#128

private def carryValue121 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (z 2) + (carryValue119 z)

private def carryValue122 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue121 z) + (carryValue120 z)

private def carryValue123 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue122 z) + (carryValue118 z)

private def carryValue124 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue123 z).setWidth 64

private def carryValue125 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue124 z) * 1439961107955227#64

private def carryValue126 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue125 z) &&& 4503599627370495#64

private def carryValue127 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue126 z).setWidth 128

private def carryValue128 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue127 z) * 671914833335277#128

private def carryValue129 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue128 z) + (carryValue123 z)

private def carryValue130 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue129 z) >>> (52 : Nat)

private def carryValue131 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue115 z) * 1367801#128

private def carryValue132 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue127 z) * 3916664325105025#128

private def carryValue133 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue131 z) + (z 3)

private def carryValue134 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue133 z) + (carryValue132 z)

private def carryValue135 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue134 z) + (carryValue130 z)

private def carryValue136 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue135 z).setWidth 64

private def carryValue137 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue136 z) * 1439961107955227#64

private def carryValue138 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue137 z) &&& 4503599627370495#64

private def carryValue139 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue138 z).setWidth 128

private def carryValue140 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue139 z) * 671914833335277#128

private def carryValue141 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue140 z) + (carryValue135 z)

private def carryValue142 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue141 z) >>> (52 : Nat)

private def carryValue143 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue105 z) <<< (44 : Nat)

private def carryValue144 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue127 z) * 1367801#128

private def carryValue145 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue139 z) * 3916664325105025#128

private def carryValue146 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (z 4) + (carryValue143 z)

private def carryValue147 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue146 z) + (carryValue144 z)

private def carryValue148 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue147 z) + (carryValue145 z)

private def carryValue149 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue148 z) + (carryValue142 z)

private def carryValue150 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue149 z).setWidth 64

private def carryValue151 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue150 z) * 1439961107955227#64

private def carryValue152 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue151 z) &&& 4503599627370495#64

private def carryValue153 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue152 z).setWidth 128

private def carryValue154 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue153 z) * 671914833335277#128

private def carryValue155 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue154 z) + (carryValue149 z)

private def carryValue156 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue155 z) >>> (52 : Nat)

private def carryValue157 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue115 z) <<< (44 : Nat)

private def carryValue158 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue139 z) * 1367801#128

private def carryValue159 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue153 z) * 3916664325105025#128

private def carryValue160 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue157 z) + (z 5)

private def carryValue161 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue160 z) + (carryValue158 z)

private def carryValue162 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue161 z) + (carryValue159 z)

private def carryValue163 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue162 z) + (carryValue156 z)

private def carryValue164 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue163 z).setWidth 64

private def carryValue165 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue164 z) &&& 4503599627370495#64

private def carryValue166 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue163 z) >>> (52 : Nat)

private def carryValue167 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue127 z) <<< (44 : Nat)

private def carryValue168 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue153 z) * 1367801#128

private def carryValue169 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue167 z) + (z 6)

private def carryValue170 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue169 z) + (carryValue168 z)

private def carryValue171 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue170 z) + (carryValue166 z)

private def carryValue172 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue171 z).setWidth 64

private def carryValue173 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue172 z) &&& 4503599627370495#64

private def carryValue174 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue171 z) >>> (52 : Nat)

private def carryValue175 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue139 z) <<< (44 : Nat)

private def carryValue176 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue175 z) + (z 7)

private def carryValue177 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue176 z) + (carryValue174 z)

private def carryValue178 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue177 z).setWidth 64

private def carryValue179 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue178 z) &&& 4503599627370495#64

private def carryValue180 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue177 z) >>> (52 : Nat)

private def carryValue181 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue153 z) <<< (44 : Nat)

private def carryValue182 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue181 z) + (z 8)

private def carryValue183 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue182 z) + (carryValue180 z)

private def carryValue184 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue183 z).setWidth 64

private def carryValue185 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue184 z) &&& 4503599627370495#64

private def carryValue186 (z : Fin 9 → BitVec 128) : BitVec 128 :=
  (carryValue183 z) >>> (52 : Nat)

private def carryValue187 (z : Fin 9 → BitVec 128) : BitVec 64 :=
  (carryValue186 z).setWidth 64

private theorem carryOp102 (z : Fin 9 → BitVec 128) :
    Operation.trunc {} (.value (z 0)) = .value (carryValue102 z) := by
  simp [carryValue102, Operation.trunc]

private theorem carryOp103 (z : Fin 9 → BitVec 128) :
    Operation.mul {} (.value (carryValue102 z)) (.value 1439961107955227#64) = .value (carryValue103 z) := by
  simp [carryValue103, Operation.mul]

private theorem carryOp104 (z : Fin 9 → BitVec 128) :
    Operation.and (.value (carryValue103 z)) (.value 4503599627370495#64) = .value (carryValue104 z) := by
  simp [carryValue104, Operation.and]

private theorem carryOp105 (z : Fin 9 → BitVec 128) :
    Operation.zext true (.value (carryValue104 z)) = .value (carryValue105 z) := by
  simpa only [carryValue105, carryValue104] using masked52_zext (carryValue103 z)

private theorem carryOp106 (z : Fin 9 → BitVec 128) :
    Operation.mul { nsw := true, nuw := true } (.value (carryValue105 z)) (.value 671914833335277#128) = .value (carryValue106 z) := by
  simpa only [carryValue106, carryValue105, carryValue104] using
    masked52_mul0 (carryValue103 z)

private theorem carryOp107 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue106 z)) (.value (z 0)) = .value (carryValue107 z) := by
  simp [carryValue107, Operation.add]

private theorem carryOp108 (z : Fin 9 → BitVec 128) :
    Operation.lshr false (.value (carryValue107 z)) (.value 52#128) = .value (carryValue108 z) := by
  simp [carryValue108, Operation.lshr]

private theorem carryOp109 (z : Fin 9 → BitVec 128) :
    Operation.mul { nsw := true, nuw := true } (.value (carryValue105 z)) (.value 3916664325105025#128) = .value (carryValue109 z) := by
  simpa only [carryValue109, carryValue105, carryValue104] using
    masked52_mul1 (carryValue103 z)

private theorem carryOp110 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue109 z)) (.value (z 1)) = .value (carryValue110 z) := by
  simp [carryValue110, Operation.add]

private theorem carryOp111 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue110 z)) (.value (carryValue108 z)) = .value (carryValue111 z) := by
  simp [carryValue111, Operation.add]

private theorem carryOp112 (z : Fin 9 → BitVec 128) :
    Operation.trunc {} (.value (carryValue111 z)) = .value (carryValue112 z) := by
  simp [carryValue112, Operation.trunc]

private theorem carryOp113 (z : Fin 9 → BitVec 128) :
    Operation.mul {} (.value (carryValue112 z)) (.value 1439961107955227#64) = .value (carryValue113 z) := by
  simp [carryValue113, Operation.mul]

private theorem carryOp114 (z : Fin 9 → BitVec 128) :
    Operation.and (.value (carryValue113 z)) (.value 4503599627370495#64) = .value (carryValue114 z) := by
  simp [carryValue114, Operation.and]

private theorem carryOp115 (z : Fin 9 → BitVec 128) :
    Operation.zext true (.value (carryValue114 z)) = .value (carryValue115 z) := by
  simpa only [carryValue115, carryValue114] using masked52_zext (carryValue113 z)

private theorem carryOp116 (z : Fin 9 → BitVec 128) :
    Operation.mul { nsw := true, nuw := true } (.value (carryValue115 z)) (.value 671914833335277#128) = .value (carryValue116 z) := by
  simpa only [carryValue116, carryValue115, carryValue114] using
    masked52_mul0 (carryValue113 z)

private theorem carryOp117 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue116 z)) (.value (carryValue111 z)) = .value (carryValue117 z) := by
  simp [carryValue117, Operation.add]

private theorem carryOp118 (z : Fin 9 → BitVec 128) :
    Operation.lshr false (.value (carryValue117 z)) (.value 52#128) = .value (carryValue118 z) := by
  simp [carryValue118, Operation.lshr]

private theorem carryOp119 (z : Fin 9 → BitVec 128) :
    Operation.mul { nsw := true, nuw := true } (.value (carryValue105 z)) (.value 1367801#128) = .value (carryValue119 z) := by
  simpa only [carryValue119, carryValue105, carryValue104] using
    masked52_mul2 (carryValue103 z)

private theorem carryOp120 (z : Fin 9 → BitVec 128) :
    Operation.mul { nsw := true, nuw := true } (.value (carryValue115 z)) (.value 3916664325105025#128) = .value (carryValue120 z) := by
  simpa only [carryValue120, carryValue115, carryValue114] using
    masked52_mul1 (carryValue113 z)

private theorem carryOp121 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (z 2)) (.value (carryValue119 z)) = .value (carryValue121 z) := by
  simp [carryValue121, Operation.add]

private theorem carryOp122 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue121 z)) (.value (carryValue120 z)) = .value (carryValue122 z) := by
  simp [carryValue122, Operation.add]

private theorem carryOp123 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue122 z)) (.value (carryValue118 z)) = .value (carryValue123 z) := by
  simp [carryValue123, Operation.add]

private theorem carryOp124 (z : Fin 9 → BitVec 128) :
    Operation.trunc {} (.value (carryValue123 z)) = .value (carryValue124 z) := by
  simp [carryValue124, Operation.trunc]

private theorem carryOp125 (z : Fin 9 → BitVec 128) :
    Operation.mul {} (.value (carryValue124 z)) (.value 1439961107955227#64) = .value (carryValue125 z) := by
  simp [carryValue125, Operation.mul]

private theorem carryOp126 (z : Fin 9 → BitVec 128) :
    Operation.and (.value (carryValue125 z)) (.value 4503599627370495#64) = .value (carryValue126 z) := by
  simp [carryValue126, Operation.and]

private theorem carryOp127 (z : Fin 9 → BitVec 128) :
    Operation.zext true (.value (carryValue126 z)) = .value (carryValue127 z) := by
  simpa only [carryValue127, carryValue126] using masked52_zext (carryValue125 z)

private theorem carryOp128 (z : Fin 9 → BitVec 128) :
    Operation.mul { nsw := true, nuw := true } (.value (carryValue127 z)) (.value 671914833335277#128) = .value (carryValue128 z) := by
  simpa only [carryValue128, carryValue127, carryValue126] using
    masked52_mul0 (carryValue125 z)

private theorem carryOp129 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue128 z)) (.value (carryValue123 z)) = .value (carryValue129 z) := by
  simp [carryValue129, Operation.add]

private theorem carryOp130 (z : Fin 9 → BitVec 128) :
    Operation.lshr false (.value (carryValue129 z)) (.value 52#128) = .value (carryValue130 z) := by
  simp [carryValue130, Operation.lshr]

private theorem carryOp131 (z : Fin 9 → BitVec 128) :
    Operation.mul { nsw := true, nuw := true } (.value (carryValue115 z)) (.value 1367801#128) = .value (carryValue131 z) := by
  simpa only [carryValue131, carryValue115, carryValue114] using
    masked52_mul2 (carryValue113 z)

private theorem carryOp132 (z : Fin 9 → BitVec 128) :
    Operation.mul { nsw := true, nuw := true } (.value (carryValue127 z)) (.value 3916664325105025#128) = .value (carryValue132 z) := by
  simpa only [carryValue132, carryValue127, carryValue126] using
    masked52_mul1 (carryValue125 z)

private theorem carryOp133 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue131 z)) (.value (z 3)) = .value (carryValue133 z) := by
  simp [carryValue133, Operation.add]

private theorem carryOp134 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue133 z)) (.value (carryValue132 z)) = .value (carryValue134 z) := by
  simp [carryValue134, Operation.add]

private theorem carryOp135 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue134 z)) (.value (carryValue130 z)) = .value (carryValue135 z) := by
  simp [carryValue135, Operation.add]

private theorem carryOp136 (z : Fin 9 → BitVec 128) :
    Operation.trunc {} (.value (carryValue135 z)) = .value (carryValue136 z) := by
  simp [carryValue136, Operation.trunc]

private theorem carryOp137 (z : Fin 9 → BitVec 128) :
    Operation.mul {} (.value (carryValue136 z)) (.value 1439961107955227#64) = .value (carryValue137 z) := by
  simp [carryValue137, Operation.mul]

private theorem carryOp138 (z : Fin 9 → BitVec 128) :
    Operation.and (.value (carryValue137 z)) (.value 4503599627370495#64) = .value (carryValue138 z) := by
  simp [carryValue138, Operation.and]

private theorem carryOp139 (z : Fin 9 → BitVec 128) :
    Operation.zext true (.value (carryValue138 z)) = .value (carryValue139 z) := by
  simpa only [carryValue139, carryValue138] using masked52_zext (carryValue137 z)

private theorem carryOp140 (z : Fin 9 → BitVec 128) :
    Operation.mul { nsw := true, nuw := true } (.value (carryValue139 z)) (.value 671914833335277#128) = .value (carryValue140 z) := by
  simpa only [carryValue140, carryValue139, carryValue138] using
    masked52_mul0 (carryValue137 z)

private theorem carryOp141 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue140 z)) (.value (carryValue135 z)) = .value (carryValue141 z) := by
  simp [carryValue141, Operation.add]

private theorem carryOp142 (z : Fin 9 → BitVec 128) :
    Operation.lshr false (.value (carryValue141 z)) (.value 52#128) = .value (carryValue142 z) := by
  simp [carryValue142, Operation.lshr]

private theorem carryOp143 (z : Fin 9 → BitVec 128) :
    Operation.shl { nsw := true, nuw := true } (.value (carryValue105 z)) (.value 44#128) = .value (carryValue143 z) := by
  simpa only [carryValue143, carryValue105, carryValue104] using
    masked52_shl44 (carryValue103 z)

private theorem carryOp144 (z : Fin 9 → BitVec 128) :
    Operation.mul { nsw := true, nuw := true } (.value (carryValue127 z)) (.value 1367801#128) = .value (carryValue144 z) := by
  simpa only [carryValue144, carryValue127, carryValue126] using
    masked52_mul2 (carryValue125 z)

private theorem carryOp145 (z : Fin 9 → BitVec 128) :
    Operation.mul { nsw := true, nuw := true } (.value (carryValue139 z)) (.value 3916664325105025#128) = .value (carryValue145 z) := by
  simpa only [carryValue145, carryValue139, carryValue138] using
    masked52_mul1 (carryValue137 z)

private theorem carryOp146 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (z 4)) (.value (carryValue143 z)) = .value (carryValue146 z) := by
  simp [carryValue146, Operation.add]

private theorem carryOp147 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue146 z)) (.value (carryValue144 z)) = .value (carryValue147 z) := by
  simp [carryValue147, Operation.add]

private theorem carryOp148 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue147 z)) (.value (carryValue145 z)) = .value (carryValue148 z) := by
  simp [carryValue148, Operation.add]

private theorem carryOp149 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue148 z)) (.value (carryValue142 z)) = .value (carryValue149 z) := by
  simp [carryValue149, Operation.add]

private theorem carryOp150 (z : Fin 9 → BitVec 128) :
    Operation.trunc {} (.value (carryValue149 z)) = .value (carryValue150 z) := by
  simp [carryValue150, Operation.trunc]

private theorem carryOp151 (z : Fin 9 → BitVec 128) :
    Operation.mul {} (.value (carryValue150 z)) (.value 1439961107955227#64) = .value (carryValue151 z) := by
  simp [carryValue151, Operation.mul]

private theorem carryOp152 (z : Fin 9 → BitVec 128) :
    Operation.and (.value (carryValue151 z)) (.value 4503599627370495#64) = .value (carryValue152 z) := by
  simp [carryValue152, Operation.and]

private theorem carryOp153 (z : Fin 9 → BitVec 128) :
    Operation.zext true (.value (carryValue152 z)) = .value (carryValue153 z) := by
  simpa only [carryValue153, carryValue152] using masked52_zext (carryValue151 z)

private theorem carryOp154 (z : Fin 9 → BitVec 128) :
    Operation.mul { nsw := true, nuw := true } (.value (carryValue153 z)) (.value 671914833335277#128) = .value (carryValue154 z) := by
  simpa only [carryValue154, carryValue153, carryValue152] using
    masked52_mul0 (carryValue151 z)

private theorem carryOp155 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue154 z)) (.value (carryValue149 z)) = .value (carryValue155 z) := by
  simp [carryValue155, Operation.add]

private theorem carryOp156 (z : Fin 9 → BitVec 128) :
    Operation.lshr false (.value (carryValue155 z)) (.value 52#128) = .value (carryValue156 z) := by
  simp [carryValue156, Operation.lshr]

private theorem carryOp157 (z : Fin 9 → BitVec 128) :
    Operation.shl { nsw := true, nuw := true } (.value (carryValue115 z)) (.value 44#128) = .value (carryValue157 z) := by
  simpa only [carryValue157, carryValue115, carryValue114] using
    masked52_shl44 (carryValue113 z)

private theorem carryOp158 (z : Fin 9 → BitVec 128) :
    Operation.mul { nsw := true, nuw := true } (.value (carryValue139 z)) (.value 1367801#128) = .value (carryValue158 z) := by
  simpa only [carryValue158, carryValue139, carryValue138] using
    masked52_mul2 (carryValue137 z)

private theorem carryOp159 (z : Fin 9 → BitVec 128) :
    Operation.mul { nsw := true, nuw := true } (.value (carryValue153 z)) (.value 3916664325105025#128) = .value (carryValue159 z) := by
  simpa only [carryValue159, carryValue153, carryValue152] using
    masked52_mul1 (carryValue151 z)

private theorem carryOp160 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue157 z)) (.value (z 5)) = .value (carryValue160 z) := by
  simp [carryValue160, Operation.add]

private theorem carryOp161 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue160 z)) (.value (carryValue158 z)) = .value (carryValue161 z) := by
  simp [carryValue161, Operation.add]

private theorem carryOp162 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue161 z)) (.value (carryValue159 z)) = .value (carryValue162 z) := by
  simp [carryValue162, Operation.add]

private theorem carryOp163 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue162 z)) (.value (carryValue156 z)) = .value (carryValue163 z) := by
  simp [carryValue163, Operation.add]

private theorem carryOp164 (z : Fin 9 → BitVec 128) :
    Operation.trunc {} (.value (carryValue163 z)) = .value (carryValue164 z) := by
  simp [carryValue164, Operation.trunc]

private theorem carryOp165 (z : Fin 9 → BitVec 128) :
    Operation.and (.value (carryValue164 z)) (.value 4503599627370495#64) = .value (carryValue165 z) := by
  simp [carryValue165, Operation.and]

private theorem carryOp166 (z : Fin 9 → BitVec 128) :
    Operation.lshr false (.value (carryValue163 z)) (.value 52#128) = .value (carryValue166 z) := by
  simp [carryValue166, Operation.lshr]

private theorem carryOp167 (z : Fin 9 → BitVec 128) :
    Operation.shl { nsw := true, nuw := true } (.value (carryValue127 z)) (.value 44#128) = .value (carryValue167 z) := by
  simpa only [carryValue167, carryValue127, carryValue126] using
    masked52_shl44 (carryValue125 z)

private theorem carryOp168 (z : Fin 9 → BitVec 128) :
    Operation.mul { nsw := true, nuw := true } (.value (carryValue153 z)) (.value 1367801#128) = .value (carryValue168 z) := by
  simpa only [carryValue168, carryValue153, carryValue152] using
    masked52_mul2 (carryValue151 z)

private theorem carryOp169 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue167 z)) (.value (z 6)) = .value (carryValue169 z) := by
  simp [carryValue169, Operation.add]

private theorem carryOp170 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue169 z)) (.value (carryValue168 z)) = .value (carryValue170 z) := by
  simp [carryValue170, Operation.add]

private theorem carryOp171 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue170 z)) (.value (carryValue166 z)) = .value (carryValue171 z) := by
  simp [carryValue171, Operation.add]

private theorem carryOp172 (z : Fin 9 → BitVec 128) :
    Operation.trunc {} (.value (carryValue171 z)) = .value (carryValue172 z) := by
  simp [carryValue172, Operation.trunc]

private theorem carryOp173 (z : Fin 9 → BitVec 128) :
    Operation.and (.value (carryValue172 z)) (.value 4503599627370495#64) = .value (carryValue173 z) := by
  simp [carryValue173, Operation.and]

private theorem carryOp174 (z : Fin 9 → BitVec 128) :
    Operation.lshr false (.value (carryValue171 z)) (.value 52#128) = .value (carryValue174 z) := by
  simp [carryValue174, Operation.lshr]

private theorem carryOp175 (z : Fin 9 → BitVec 128) :
    Operation.shl { nsw := true, nuw := true } (.value (carryValue139 z)) (.value 44#128) = .value (carryValue175 z) := by
  simpa only [carryValue175, carryValue139, carryValue138] using
    masked52_shl44 (carryValue137 z)

private theorem carryOp176 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue175 z)) (.value (z 7)) = .value (carryValue176 z) := by
  simp [carryValue176, Operation.add]

private theorem carryOp177 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue176 z)) (.value (carryValue174 z)) = .value (carryValue177 z) := by
  simp [carryValue177, Operation.add]

private theorem carryOp178 (z : Fin 9 → BitVec 128) :
    Operation.trunc {} (.value (carryValue177 z)) = .value (carryValue178 z) := by
  simp [carryValue178, Operation.trunc]

private theorem carryOp179 (z : Fin 9 → BitVec 128) :
    Operation.and (.value (carryValue178 z)) (.value 4503599627370495#64) = .value (carryValue179 z) := by
  simp [carryValue179, Operation.and]

private theorem carryOp180 (z : Fin 9 → BitVec 128) :
    Operation.lshr false (.value (carryValue177 z)) (.value 52#128) = .value (carryValue180 z) := by
  simp [carryValue180, Operation.lshr]

private theorem carryOp181 (z : Fin 9 → BitVec 128) :
    Operation.shl { nsw := true, nuw := true } (.value (carryValue153 z)) (.value 44#128) = .value (carryValue181 z) := by
  simpa only [carryValue181, carryValue153, carryValue152] using
    masked52_shl44 (carryValue151 z)

private theorem carryOp182 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue181 z)) (.value (z 8)) = .value (carryValue182 z) := by
  simp [carryValue182, Operation.add]

private theorem carryOp183 (z : Fin 9 → BitVec 128) :
    Operation.add {} (.value (carryValue182 z)) (.value (carryValue180 z)) = .value (carryValue183 z) := by
  simp [carryValue183, Operation.add]

private theorem carryOp184 (z : Fin 9 → BitVec 128) :
    Operation.trunc {} (.value (carryValue183 z)) = .value (carryValue184 z) := by
  simp [carryValue184, Operation.trunc]

private theorem carryOp185 (z : Fin 9 → BitVec 128) :
    Operation.and (.value (carryValue184 z)) (.value 4503599627370495#64) = .value (carryValue185 z) := by
  simp [carryValue185, Operation.and]

private theorem carryOp186 (z : Fin 9 → BitVec 128) :
    Operation.lshr false (.value (carryValue183 z)) (.value 52#128) = .value (carryValue186 z) := by
  simp [carryValue186, Operation.lshr]

private theorem carryOp187 (z : Fin 9 → BitVec 128) :
    Operation.trunc {} (.value (carryValue186 z)) = .value (carryValue187 z) := by
  simp [carryValue187, Operation.trunc]

private def carryChunkEnv0 (E : Env program.Γ) (z : Fin 9 → BitVec 128) : Env program.Γ :=
  E[%102 := .value (carryValue102 z),
    %103 := .value (carryValue103 z),
    %104 := .value (carryValue104 z),
    %105 := .value (carryValue105 z),
    %106 := .value (carryValue106 z),
    %107 := .value (carryValue107 z),
    %108 := .value (carryValue108 z),
    %109 := .value (carryValue109 z),
    %110 := .value (carryValue110 z),
    %111 := .value (carryValue111 z)]

private def carryChunkEnv1 (E : Env program.Γ) (z : Fin 9 → BitVec 128) : Env program.Γ :=
  (carryChunkEnv0 E z)[%112 := .value (carryValue112 z),
    %113 := .value (carryValue113 z),
    %114 := .value (carryValue114 z),
    %115 := .value (carryValue115 z),
    %116 := .value (carryValue116 z),
    %117 := .value (carryValue117 z),
    %118 := .value (carryValue118 z),
    %119 := .value (carryValue119 z),
    %120 := .value (carryValue120 z),
    %121 := .value (carryValue121 z)]

private def carryChunkEnv2 (E : Env program.Γ) (z : Fin 9 → BitVec 128) : Env program.Γ :=
  (carryChunkEnv1 E z)[%122 := .value (carryValue122 z),
    %123 := .value (carryValue123 z),
    %124 := .value (carryValue124 z),
    %125 := .value (carryValue125 z),
    %126 := .value (carryValue126 z),
    %127 := .value (carryValue127 z),
    %128 := .value (carryValue128 z),
    %129 := .value (carryValue129 z),
    %130 := .value (carryValue130 z),
    %131 := .value (carryValue131 z)]

private def carryChunkEnv3 (E : Env program.Γ) (z : Fin 9 → BitVec 128) : Env program.Γ :=
  (carryChunkEnv2 E z)[%132 := .value (carryValue132 z),
    %133 := .value (carryValue133 z),
    %134 := .value (carryValue134 z),
    %135 := .value (carryValue135 z),
    %136 := .value (carryValue136 z),
    %137 := .value (carryValue137 z),
    %138 := .value (carryValue138 z),
    %139 := .value (carryValue139 z),
    %140 := .value (carryValue140 z),
    %141 := .value (carryValue141 z)]

private def carryChunkEnv4 (E : Env program.Γ) (z : Fin 9 → BitVec 128) : Env program.Γ :=
  (carryChunkEnv3 E z)[%142 := .value (carryValue142 z),
    %143 := .value (carryValue143 z),
    %144 := .value (carryValue144 z),
    %145 := .value (carryValue145 z),
    %146 := .value (carryValue146 z),
    %147 := .value (carryValue147 z),
    %148 := .value (carryValue148 z),
    %149 := .value (carryValue149 z),
    %150 := .value (carryValue150 z),
    %151 := .value (carryValue151 z)]

private def carryChunkEnv5 (E : Env program.Γ) (z : Fin 9 → BitVec 128) : Env program.Γ :=
  (carryChunkEnv4 E z)[%152 := .value (carryValue152 z),
    %153 := .value (carryValue153 z),
    %154 := .value (carryValue154 z),
    %155 := .value (carryValue155 z),
    %156 := .value (carryValue156 z),
    %157 := .value (carryValue157 z),
    %158 := .value (carryValue158 z),
    %159 := .value (carryValue159 z),
    %160 := .value (carryValue160 z),
    %161 := .value (carryValue161 z)]

private def carryChunkEnv6 (E : Env program.Γ) (z : Fin 9 → BitVec 128) : Env program.Γ :=
  (carryChunkEnv5 E z)[%162 := .value (carryValue162 z),
    %163 := .value (carryValue163 z),
    %164 := .value (carryValue164 z),
    %165 := .value (carryValue165 z),
    %166 := .value (carryValue166 z),
    %167 := .value (carryValue167 z),
    %168 := .value (carryValue168 z),
    %169 := .value (carryValue169 z),
    %170 := .value (carryValue170 z),
    %171 := .value (carryValue171 z)]

private def carryChunkEnv7 (E : Env program.Γ) (z : Fin 9 → BitVec 128) : Env program.Γ :=
  (carryChunkEnv6 E z)[%172 := .value (carryValue172 z),
    %173 := .value (carryValue173 z),
    %174 := .value (carryValue174 z),
    %175 := .value (carryValue175 z),
    %176 := .value (carryValue176 z),
    %177 := .value (carryValue177 z),
    %178 := .value (carryValue178 z),
    %179 := .value (carryValue179 z),
    %180 := .value (carryValue180 z),
    %181 := .value (carryValue181 z)]

private def carryChunkEnv8 (E : Env program.Γ) (z : Fin 9 → BitVec 128) : Env program.Γ :=
  (carryChunkEnv7 E z)[%182 := .value (carryValue182 z),
    %183 := .value (carryValue183 z),
    %184 := .value (carryValue184 z),
    %185 := .value (carryValue185 z),
    %186 := .value (carryValue186 z),
    %187 := .value (carryValue187 z)]

def carryWordEnv (E : Env program.Γ) (z : Fin 9 → BitVec 128) : Env program.Γ :=
  carryChunkEnv8 E z

/-- The carry window writes only SSA values, preserving every argument. -/
theorem carryWordEnv_read_arg (E : Env program.Γ) (z : Fin 9 → BitVec 128)
    (i : Fin program.Γ.args.length) (ht : program.Γ.args[i] = t) :
    (carryWordEnv E z).read (.arg i ht) = E.read (.arg i ht) := by
  simp only [carryWordEnv, carryChunkEnv8, carryChunkEnv7, carryChunkEnv6, carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, Env.read_write_arg]

/-- The carry window writes registers 102–187 and preserves every earlier value. -/
theorem carryWordEnv_read_early (E : Env program.Γ) (z : Fin 9 → BitVec 128)
    (i : Fin program.Γ.n) (ht : program.Γ.ty i = t) (hi : i.val < 102) :
    (carryWordEnv E z).read (.val i ht) = E.read (.val i ht) := by
  unfold carryWordEnv carryChunkEnv8 carryChunkEnv7 carryChunkEnv6 carryChunkEnv5 carryChunkEnv4 carryChunkEnv3 carryChunkEnv2 carryChunkEnv1 carryChunkEnv0
  repeat' rw [Env.read_write_ne _ _ (by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega)]

/-- The five quotient registers agree with the arithmetic word schedule. -/
theorem carryWordEnv_quotient (E : Env program.Γ) (z : Fin 9 → BitVec 128) :
    (carryWordEnv E z).read (%165) = .value (wordQuotientLimbs z 0) ∧
    (carryWordEnv E z).read (%173) = .value (wordQuotientLimbs z 1) ∧
    (carryWordEnv E z).read (%179) = .value (wordQuotientLimbs z 2) ∧
    (carryWordEnv E z).read (%185) = .value (wordQuotientLimbs z 3) ∧
    (carryWordEnv E z).read (%187) = .value (wordQuotientLimbs z 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [carryWordEnv, carryChunkEnv8, carryChunkEnv7, carryChunkEnv6, carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, mlir_env,
      Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq, Fin.mk.injEq, not_false_eq_true]
    rfl

section CarryExecution

-- Keep failed rewrite candidates from unfolding unrelated register expressions.
attribute [local irreducible]
  carryValue102 carryValue103 carryValue104 carryValue105 carryValue106 carryValue107 carryValue108 carryValue109
  carryValue110 carryValue111 carryValue112 carryValue113 carryValue114 carryValue115 carryValue116 carryValue117
  carryValue118 carryValue119 carryValue120 carryValue121 carryValue122 carryValue123 carryValue124 carryValue125
  carryValue126 carryValue127 carryValue128 carryValue129 carryValue130 carryValue131 carryValue132 carryValue133
  carryValue134 carryValue135 carryValue136 carryValue137 carryValue138 carryValue139 carryValue140 carryValue141
  carryValue142 carryValue143 carryValue144 carryValue145 carryValue146 carryValue147 carryValue148 carryValue149
  carryValue150 carryValue151 carryValue152 carryValue153 carryValue154 carryValue155 carryValue156 carryValue157
  carryValue158 carryValue159 carryValue160 carryValue161 carryValue162 carryValue163 carryValue164 carryValue165
  carryValue166 carryValue167 carryValue168 carryValue169 carryValue170 carryValue171 carryValue172 carryValue173
  carryValue174 carryValue175 carryValue176 carryValue177 carryValue178 carryValue179 carryValue180 carryValue181
  carryValue182 carryValue183 carryValue184 carryValue185 carryValue186 carryValue187

private theorem carry_slices_compose {Γ : Ctx} {body : List (Instr Γ)}
    {E E1 E2 : Env Γ} {state : GlobalState} {start next count1 count2 total : Nat}
    (hnext : start + count1 = next) (htotal : count1 + count2 = total)
    (h1 : List.foldlM Instr.run E ((body.drop start).take count1) state = .value (E1, state))
    (h2 : List.foldlM Instr.run E1 ((body.drop next).take count2) state =
      .value (E2, state)) :
    List.foldlM Instr.run E ((body.drop start).take total) state =
      .value (E2, state) := by
  rw [← htotal, List.take_add, List.foldlM_append]
  simp only [EffectM.bind_eq, h1, LeanMLIR.RIR.PoisonOr.value_bind, List.drop_drop, hnext]
  exact h2

/-- Execute every retained flag in the actual carry window. Input columns may
be arbitrary u128 words here; their no-wrap arithmetic bounds are proved separately. -/
theorem carry_word_run (p : Primitives) (E : Env program.Γ) (state : GlobalState)
    (z : Fin 9 → BitVec 128)
    (hz0 : E.read (%37) = .value (z 0))
    (hz1 : E.read (%46) = .value (z 1))
    (hz2 : E.read (%57) = .value (z 2))
    (hz3 : E.read (%70) = .value (z 3))
    (hz4 : E.read (%85) = .value (z 4))
    (hz5 : E.read (%92) = .value (z 5))
    (hz6 : E.read (%97) = .value (z 6))
    (hz7 : E.read (%100) = .value (z 7))
    (hz8 : E.read (%101) = .value (z 8))
    (hc5 : E.read (%5) = .value 1439961107955227#64)
    (hc6 : E.read (%6) = .value 4503599627370495#64)
    (hc7 : E.read (%7) = .value 671914833335277#128)
    (hc8 : E.read (%8) = .value 52#128)
    (hc9 : E.read (%9) = .value 3916664325105025#128)
    (hc10 : E.read (%10) = .value 1367801#128)
    (hc11 : E.read (%11) = .value 44#128)
    : List.foldlM Instr.run E (((program.entry p).body.drop 122).take 86) state =
      .value (carryWordEnv E z, state) := by
  have h0 : List.foldlM Instr.run E
      (((program.entry p).body.drop 122).take 10) state =
      .value (carryChunkEnv0 E z, state) := by
    simp (config := { maxSteps := 1000000 }) only [
      carryChunkEnv0, hz0, hz1, hz2, hz3,
      hz4, hz5, hz6, hz7, hz8,
      hc5, hc6, hc7, hc8, hc9,
      hc10, hc11, carryOp102 z, carryOp103 z, carryOp104 z,
      carryOp105 z, carryOp106 z, carryOp107 z, carryOp108 z, carryOp109 z,
      carryOp110 z, carryOp111 z, program.entry, List.foldlM_cons, List.foldlM_nil,
      Instr.run, UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      List.drop_zero, LeanMLIR.RIR.PoisonOr.value_bind, LeanMLIR.RIR.PoisonOr.pure_def, Prod.fst, Prod.snd, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true, BitVec.ushiftRight_eq]
  have h1_5 : (carryChunkEnv0 E z).read (%5) = .value 1439961107955227#64 := by
    simp only [carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h1_6 : (carryChunkEnv0 E z).read (%6) = .value 4503599627370495#64 := by
    simp only [carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h1_7 : (carryChunkEnv0 E z).read (%7) = .value 671914833335277#128 := by
    simp only [carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h1_8 : (carryChunkEnv0 E z).read (%8) = .value 52#128 := by
    simp only [carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h1_9 : (carryChunkEnv0 E z).read (%9) = .value 3916664325105025#128 := by
    simp only [carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h1_10 : (carryChunkEnv0 E z).read (%10) = .value 1367801#128 := by
    simp only [carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h1_57 : (carryChunkEnv0 E z).read (%57) = .value (z 2) := by
    simp only [carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h1_105 : (carryChunkEnv0 E z).read (%105) = .value (carryValue105 z) := by
    simp only [carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h1_111 : (carryChunkEnv0 E z).read (%111) = .value (carryValue111 z) := by
    simp only [carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h1 : List.foldlM Instr.run (carryChunkEnv0 E z)
      (((program.entry p).body.drop 132).take 10) state =
      .value (carryChunkEnv1 E z, state) := by
    simp (config := { maxSteps := 1000000 }) only [
      carryChunkEnv1, h1_5, h1_6, h1_7, h1_8,
      h1_9, h1_10, h1_57, h1_105, h1_111,
      carryOp112 z, carryOp113 z, carryOp114 z, carryOp115 z, carryOp116 z,
      carryOp117 z, carryOp118 z, carryOp119 z, carryOp120 z, carryOp121 z,
      program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run, UnOp.compute,
      BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, LeanMLIR.RIR.PoisonOr.value_bind,
      LeanMLIR.RIR.PoisonOr.pure_def, Prod.fst, Prod.snd, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true, BitVec.ushiftRight_eq]
  have h2_5 : (carryChunkEnv1 E z).read (%5) = .value 1439961107955227#64 := by
    simp only [carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h2_6 : (carryChunkEnv1 E z).read (%6) = .value 4503599627370495#64 := by
    simp only [carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h2_7 : (carryChunkEnv1 E z).read (%7) = .value 671914833335277#128 := by
    simp only [carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h2_8 : (carryChunkEnv1 E z).read (%8) = .value 52#128 := by
    simp only [carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h2_10 : (carryChunkEnv1 E z).read (%10) = .value 1367801#128 := by
    simp only [carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h2_115 : (carryChunkEnv1 E z).read (%115) = .value (carryValue115 z) := by
    simp only [carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h2_118 : (carryChunkEnv1 E z).read (%118) = .value (carryValue118 z) := by
    simp only [carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h2_120 : (carryChunkEnv1 E z).read (%120) = .value (carryValue120 z) := by
    simp only [carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h2_121 : (carryChunkEnv1 E z).read (%121) = .value (carryValue121 z) := by
    simp only [carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h2 : List.foldlM Instr.run (carryChunkEnv1 E z)
      (((program.entry p).body.drop 142).take 10) state =
      .value (carryChunkEnv2 E z, state) := by
    simp (config := { maxSteps := 1000000 }) only [
      carryChunkEnv2, h2_5, h2_6, h2_7, h2_8,
      h2_10, h2_115, h2_118, h2_120, h2_121,
      carryOp122 z, carryOp123 z, carryOp124 z, carryOp125 z, carryOp126 z,
      carryOp127 z, carryOp128 z, carryOp129 z, carryOp130 z, carryOp131 z,
      program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run, UnOp.compute,
      BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, LeanMLIR.RIR.PoisonOr.value_bind,
      LeanMLIR.RIR.PoisonOr.pure_def, Prod.fst, Prod.snd, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true, BitVec.ushiftRight_eq]
  have h3_5 : (carryChunkEnv2 E z).read (%5) = .value 1439961107955227#64 := by
    simp only [carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h3_6 : (carryChunkEnv2 E z).read (%6) = .value 4503599627370495#64 := by
    simp only [carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h3_7 : (carryChunkEnv2 E z).read (%7) = .value 671914833335277#128 := by
    simp only [carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h3_9 : (carryChunkEnv2 E z).read (%9) = .value 3916664325105025#128 := by
    simp only [carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h3_70 : (carryChunkEnv2 E z).read (%70) = .value (z 3) := by
    simp only [carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h3_127 : (carryChunkEnv2 E z).read (%127) = .value (carryValue127 z) := by
    simp only [carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h3_130 : (carryChunkEnv2 E z).read (%130) = .value (carryValue130 z) := by
    simp only [carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h3_131 : (carryChunkEnv2 E z).read (%131) = .value (carryValue131 z) := by
    simp only [carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h3 : List.foldlM Instr.run (carryChunkEnv2 E z)
      (((program.entry p).body.drop 152).take 10) state =
      .value (carryChunkEnv3 E z, state) := by
    simp (config := { maxSteps := 1000000 }) only [
      carryChunkEnv3, h3_5, h3_6, h3_7, h3_9,
      h3_70, h3_127, h3_130, h3_131, carryOp132 z,
      carryOp133 z, carryOp134 z, carryOp135 z, carryOp136 z, carryOp137 z,
      carryOp138 z, carryOp139 z, carryOp140 z, carryOp141 z, program.entry,
      List.foldlM_cons, List.foldlM_nil, Instr.run, UnOp.compute, BinOp.compute,
      EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, List.take_succ_cons,
      List.take_zero, List.drop_succ_cons, List.drop_zero, LeanMLIR.RIR.PoisonOr.value_bind, LeanMLIR.RIR.PoisonOr.pure_def,
      Prod.fst, Prod.snd, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true, BitVec.ushiftRight_eq]
  have h4_5 : (carryChunkEnv3 E z).read (%5) = .value 1439961107955227#64 := by
    simp only [carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h4_8 : (carryChunkEnv3 E z).read (%8) = .value 52#128 := by
    simp only [carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h4_9 : (carryChunkEnv3 E z).read (%9) = .value 3916664325105025#128 := by
    simp only [carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h4_10 : (carryChunkEnv3 E z).read (%10) = .value 1367801#128 := by
    simp only [carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h4_11 : (carryChunkEnv3 E z).read (%11) = .value 44#128 := by
    simp only [carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h4_85 : (carryChunkEnv3 E z).read (%85) = .value (z 4) := by
    simp only [carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h4_105 : (carryChunkEnv3 E z).read (%105) = .value (carryValue105 z) := by
    simp only [carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h4_127 : (carryChunkEnv3 E z).read (%127) = .value (carryValue127 z) := by
    simp only [carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h4_139 : (carryChunkEnv3 E z).read (%139) = .value (carryValue139 z) := by
    simp only [carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h4_141 : (carryChunkEnv3 E z).read (%141) = .value (carryValue141 z) := by
    simp only [carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h4 : List.foldlM Instr.run (carryChunkEnv3 E z)
      (((program.entry p).body.drop 162).take 10) state =
      .value (carryChunkEnv4 E z, state) := by
    simp (config := { maxSteps := 1000000 }) only [
      carryChunkEnv4, h4_5, h4_8, h4_9, h4_10,
      h4_11, h4_85, h4_105, h4_127, h4_139,
      h4_141, carryOp142 z, carryOp143 z, carryOp144 z, carryOp145 z,
      carryOp146 z, carryOp147 z, carryOp148 z, carryOp149 z, carryOp150 z,
      carryOp151 z, program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
      UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env,
      mlir_effect, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      LeanMLIR.RIR.PoisonOr.value_bind, LeanMLIR.RIR.PoisonOr.pure_def, Prod.fst, Prod.snd, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true, BitVec.ushiftRight_eq]
  have h5_6 : (carryChunkEnv4 E z).read (%6) = .value 4503599627370495#64 := by
    simp only [carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h5_7 : (carryChunkEnv4 E z).read (%7) = .value 671914833335277#128 := by
    simp only [carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h5_8 : (carryChunkEnv4 E z).read (%8) = .value 52#128 := by
    simp only [carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h5_9 : (carryChunkEnv4 E z).read (%9) = .value 3916664325105025#128 := by
    simp only [carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h5_10 : (carryChunkEnv4 E z).read (%10) = .value 1367801#128 := by
    simp only [carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h5_11 : (carryChunkEnv4 E z).read (%11) = .value 44#128 := by
    simp only [carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h5_92 : (carryChunkEnv4 E z).read (%92) = .value (z 5) := by
    simp only [carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h5_115 : (carryChunkEnv4 E z).read (%115) = .value (carryValue115 z) := by
    simp only [carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h5_139 : (carryChunkEnv4 E z).read (%139) = .value (carryValue139 z) := by
    simp only [carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h5_149 : (carryChunkEnv4 E z).read (%149) = .value (carryValue149 z) := by
    simp only [carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h5_151 : (carryChunkEnv4 E z).read (%151) = .value (carryValue151 z) := by
    simp only [carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h5 : List.foldlM Instr.run (carryChunkEnv4 E z)
      (((program.entry p).body.drop 172).take 10) state =
      .value (carryChunkEnv5 E z, state) := by
    simp (config := { maxSteps := 1000000 }) only [
      carryChunkEnv5, h5_6, h5_7, h5_8, h5_9,
      h5_10, h5_11, h5_92, h5_115, h5_139,
      h5_149, h5_151, carryOp152 z, carryOp153 z, carryOp154 z,
      carryOp155 z, carryOp156 z, carryOp157 z, carryOp158 z, carryOp159 z,
      carryOp160 z, carryOp161 z, program.entry, List.foldlM_cons, List.foldlM_nil,
      Instr.run, UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      List.drop_zero, LeanMLIR.RIR.PoisonOr.value_bind, LeanMLIR.RIR.PoisonOr.pure_def, Prod.fst, Prod.snd, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true, BitVec.ushiftRight_eq]
  have h6_6 : (carryChunkEnv5 E z).read (%6) = .value 4503599627370495#64 := by
    simp only [carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h6_8 : (carryChunkEnv5 E z).read (%8) = .value 52#128 := by
    simp only [carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h6_10 : (carryChunkEnv5 E z).read (%10) = .value 1367801#128 := by
    simp only [carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h6_11 : (carryChunkEnv5 E z).read (%11) = .value 44#128 := by
    simp only [carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h6_97 : (carryChunkEnv5 E z).read (%97) = .value (z 6) := by
    simp only [carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h6_127 : (carryChunkEnv5 E z).read (%127) = .value (carryValue127 z) := by
    simp only [carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h6_153 : (carryChunkEnv5 E z).read (%153) = .value (carryValue153 z) := by
    simp only [carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h6_156 : (carryChunkEnv5 E z).read (%156) = .value (carryValue156 z) := by
    simp only [carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h6_159 : (carryChunkEnv5 E z).read (%159) = .value (carryValue159 z) := by
    simp only [carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h6_161 : (carryChunkEnv5 E z).read (%161) = .value (carryValue161 z) := by
    simp only [carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h6 : List.foldlM Instr.run (carryChunkEnv5 E z)
      (((program.entry p).body.drop 182).take 10) state =
      .value (carryChunkEnv6 E z, state) := by
    simp (config := { maxSteps := 1000000 }) only [
      carryChunkEnv6, h6_6, h6_8, h6_10, h6_11,
      h6_97, h6_127, h6_153, h6_156, h6_159,
      h6_161, carryOp162 z, carryOp163 z, carryOp164 z, carryOp165 z,
      carryOp166 z, carryOp167 z, carryOp168 z, carryOp169 z, carryOp170 z,
      carryOp171 z, program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
      UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env,
      mlir_effect, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      LeanMLIR.RIR.PoisonOr.value_bind, LeanMLIR.RIR.PoisonOr.pure_def, Prod.fst, Prod.snd, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true, BitVec.ushiftRight_eq]
  have h7_6 : (carryChunkEnv6 E z).read (%6) = .value 4503599627370495#64 := by
    simp only [carryChunkEnv6, carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h7_8 : (carryChunkEnv6 E z).read (%8) = .value 52#128 := by
    simp only [carryChunkEnv6, carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h7_11 : (carryChunkEnv6 E z).read (%11) = .value 44#128 := by
    simp only [carryChunkEnv6, carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h7_100 : (carryChunkEnv6 E z).read (%100) = .value (z 7) := by
    simp only [carryChunkEnv6, carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h7_139 : (carryChunkEnv6 E z).read (%139) = .value (carryValue139 z) := by
    simp only [carryChunkEnv6, carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h7_153 : (carryChunkEnv6 E z).read (%153) = .value (carryValue153 z) := by
    simp only [carryChunkEnv6, carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h7_171 : (carryChunkEnv6 E z).read (%171) = .value (carryValue171 z) := by
    simp only [carryChunkEnv6, carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h7 : List.foldlM Instr.run (carryChunkEnv6 E z)
      (((program.entry p).body.drop 192).take 10) state =
      .value (carryChunkEnv7 E z, state) := by
    simp (config := { maxSteps := 1000000 }) only [
      carryChunkEnv7, h7_6, h7_8, h7_11, h7_100,
      h7_139, h7_153, h7_171, carryOp172 z, carryOp173 z,
      carryOp174 z, carryOp175 z, carryOp176 z, carryOp177 z, carryOp178 z,
      carryOp179 z, carryOp180 z, carryOp181 z, program.entry, List.foldlM_cons,
      List.foldlM_nil, Instr.run, UnOp.compute, BinOp.compute, EffectM.bind_eq,
      EffectM.pure_eq, mlir_env, mlir_effect, List.take_succ_cons, List.take_zero,
      List.drop_succ_cons, List.drop_zero, LeanMLIR.RIR.PoisonOr.value_bind, LeanMLIR.RIR.PoisonOr.pure_def, Prod.fst,
      Prod.snd, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true, BitVec.ushiftRight_eq]
  have h8_6 : (carryChunkEnv7 E z).read (%6) = .value 4503599627370495#64 := by
    simp only [carryChunkEnv7, carryChunkEnv6, carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h8_8 : (carryChunkEnv7 E z).read (%8) = .value 52#128 := by
    simp only [carryChunkEnv7, carryChunkEnv6, carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h8_101 : (carryChunkEnv7 E z).read (%101) = .value (z 8) := by
    simp only [carryChunkEnv7, carryChunkEnv6, carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h8_180 : (carryChunkEnv7 E z).read (%180) = .value (carryValue180 z) := by
    simp only [carryChunkEnv7, carryChunkEnv6, carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h8_181 : (carryChunkEnv7 E z).read (%181) = .value (carryValue181 z) := by
    simp only [carryChunkEnv7, carryChunkEnv6, carryChunkEnv5, carryChunkEnv4, carryChunkEnv3, carryChunkEnv2, carryChunkEnv1, carryChunkEnv0, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hc5, hc6, hc7, hc8, hc9, hc10, hc11, mlir_env, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true]
  have h8 : List.foldlM Instr.run (carryChunkEnv7 E z)
      (((program.entry p).body.drop 202).take 6) state =
      .value (carryChunkEnv8 E z, state) := by
    simp (config := { maxSteps := 1000000 }) only [
      carryChunkEnv8, h8_6, h8_8, h8_101, h8_180,
      h8_181, carryOp182 z, carryOp183 z, carryOp184 z, carryOp185 z,
      carryOp186 z, carryOp187 z, program.entry, List.foldlM_cons, List.foldlM_nil,
      Instr.run, UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq,
      mlir_env, mlir_effect, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      List.drop_zero, LeanMLIR.RIR.PoisonOr.value_bind, LeanMLIR.RIR.PoisonOr.pure_def, Prod.fst, Prod.snd, Fin.reduceEq, Fin.reduceNe, Nat.reduceEqDiff, ne_eq,
      Fin.mk.injEq, not_false_eq_true, BitVec.ushiftRight_eq]
  change List.foldlM Instr.run E (((program.entry p).body.drop 122).take 86) state =
    .value (carryChunkEnv8 E z, state)
  have hThrough1 : List.foldlM Instr.run E
      (((program.entry p).body.drop 122).take 20) state =
      .value (carryChunkEnv1 E z, state) := by
    exact carry_slices_compose (body := (program.entry p).body)
      (E := E) (E1 := carryChunkEnv0 E z) (E2 := carryChunkEnv1 E z)
      (state := state) (start := 122) (next := 132)
      (count1 := 10) (count2 := 10) (total := 20) rfl rfl h0 h1
  have hThrough2 : List.foldlM Instr.run E
      (((program.entry p).body.drop 122).take 30) state =
      .value (carryChunkEnv2 E z, state) := by
    exact carry_slices_compose (body := (program.entry p).body)
      (E := E) (E1 := carryChunkEnv1 E z) (E2 := carryChunkEnv2 E z)
      (state := state) (start := 122) (next := 142)
      (count1 := 20) (count2 := 10) (total := 30) rfl rfl hThrough1 h2
  have hThrough3 : List.foldlM Instr.run E
      (((program.entry p).body.drop 122).take 40) state =
      .value (carryChunkEnv3 E z, state) := by
    exact carry_slices_compose (body := (program.entry p).body)
      (E := E) (E1 := carryChunkEnv2 E z) (E2 := carryChunkEnv3 E z)
      (state := state) (start := 122) (next := 152)
      (count1 := 30) (count2 := 10) (total := 40) rfl rfl hThrough2 h3
  have hThrough4 : List.foldlM Instr.run E
      (((program.entry p).body.drop 122).take 50) state =
      .value (carryChunkEnv4 E z, state) := by
    exact carry_slices_compose (body := (program.entry p).body)
      (E := E) (E1 := carryChunkEnv3 E z) (E2 := carryChunkEnv4 E z)
      (state := state) (start := 122) (next := 162)
      (count1 := 40) (count2 := 10) (total := 50) rfl rfl hThrough3 h4
  have hThrough5 : List.foldlM Instr.run E
      (((program.entry p).body.drop 122).take 60) state =
      .value (carryChunkEnv5 E z, state) := by
    exact carry_slices_compose (body := (program.entry p).body)
      (E := E) (E1 := carryChunkEnv4 E z) (E2 := carryChunkEnv5 E z)
      (state := state) (start := 122) (next := 172)
      (count1 := 50) (count2 := 10) (total := 60) rfl rfl hThrough4 h5
  have hThrough6 : List.foldlM Instr.run E
      (((program.entry p).body.drop 122).take 70) state =
      .value (carryChunkEnv6 E z, state) := by
    exact carry_slices_compose (body := (program.entry p).body)
      (E := E) (E1 := carryChunkEnv5 E z) (E2 := carryChunkEnv6 E z)
      (state := state) (start := 122) (next := 182)
      (count1 := 60) (count2 := 10) (total := 70) rfl rfl hThrough5 h6
  have hThrough7 : List.foldlM Instr.run E
      (((program.entry p).body.drop 122).take 80) state =
      .value (carryChunkEnv7 E z, state) := by
    exact carry_slices_compose (body := (program.entry p).body)
      (E := E) (E1 := carryChunkEnv6 E z) (E2 := carryChunkEnv7 E z)
      (state := state) (start := 122) (next := 192)
      (count1 := 70) (count2 := 10) (total := 80) rfl rfl hThrough6 h7
  have hThrough8 : List.foldlM Instr.run E
      (((program.entry p).body.drop 122).take 86) state =
      .value (carryChunkEnv8 E z, state) := by
    exact carry_slices_compose (body := (program.entry p).body)
      (E := E) (E1 := carryChunkEnv7 E z) (E2 := carryChunkEnv8 E z)
      (state := state) (start := 122) (next := 202)
      (count1 := 80) (count2 := 6) (total := 86) rfl rfl hThrough7 h8
  exact hThrough8

end CarryExecution

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
