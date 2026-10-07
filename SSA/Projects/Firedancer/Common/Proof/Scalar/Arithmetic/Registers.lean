import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.SourceEvaluator

/-! Numbered pure registers from the committed scalar reducer. The final equality
is checked definitionally against the source proof witness, including overflow flags. -/

namespace Firedancer.Common.ScalarArithmetic.Registers
open LeanMLIR SLLVM
open InstCombine (LLVM)

noncomputable def r0 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (16))

noncomputable def r1 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (40))

noncomputable def r2 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (2097151))

noncomputable def r3 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (21))

noncomputable def r4 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (42))

noncomputable def r5 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (1))

noncomputable def r6 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (20))

noncomputable def r7 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (41))

noncomputable def r8 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (2))

noncomputable def r9 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (19))

noncomputable def r10 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (3))

noncomputable def r11 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (18))

noncomputable def r12 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (39))

noncomputable def r13 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (4))

noncomputable def r14 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (17))

noncomputable def r15 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (38))

noncomputable def r16 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (5))

noncomputable def r17 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (37))

noncomputable def r18 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (6))

noncomputable def r19 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (15))

noncomputable def r20 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (36))

noncomputable def r21 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (7))

noncomputable def r22 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (14))

noncomputable def r23 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (35))

noncomputable def r24 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (666643))

noncomputable def r25 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (470296))

noncomputable def r26 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (654183))

noncomputable def r27 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (-997805))

noncomputable def r28 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (136657))

noncomputable def r29 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (-683901))

noncomputable def r30 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (1048576))

noncomputable def r31 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (8796090925056))

noncomputable def r32 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (-2097152))

noncomputable def r33 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (4398044413952))

noncomputable def r34 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (9223367638808264704))

noncomputable def r35 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (63))

noncomputable def r36 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (1048575))

noncomputable def r37 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (2199022206976))

noncomputable def r38 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (4611683819404132352))

noncomputable def r39 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (62))

noncomputable def r40 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (524287))

noncomputable def r41 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (1099511103488))

noncomputable def r42 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (2305841909702066176))

noncomputable def r43 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (61))

noncomputable def r44 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (262143))

noncomputable def r45 (_digest : BitVec 512) : LLVM.IntW 64 :=
  .value (BitVec.ofInt 64 (549755551744))

noncomputable def r46 (digest : BitVec 512) : LLVM.IntW 64 :=
  .value (digest.extractLsb' 0 64)

noncomputable def r48 (digest : BitVec 512) : LLVM.IntW 64 :=
  .value (digest.extractLsb' 64 64)

noncomputable def r50 (digest : BitVec 512) : LLVM.IntW 64 :=
  .value (digest.extractLsb' 128 64)

noncomputable def r52 (digest : BitVec 512) : LLVM.IntW 64 :=
  .value (digest.extractLsb' 192 64)

noncomputable def r54 (digest : BitVec 512) : LLVM.IntW 64 :=
  .value (digest.extractLsb' 256 64)

noncomputable def r56 (digest : BitVec 512) : LLVM.IntW 64 :=
  .value (digest.extractLsb' 320 64)

noncomputable def r58 (digest : BitVec 512) : LLVM.IntW 64 :=
  .value (digest.extractLsb' 384 64)

noncomputable def r60 (digest : BitVec 512) : LLVM.IntW 64 :=
  .value (digest.extractLsb' 448 64)

noncomputable def r61 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r46 digest) (r2 digest)

noncomputable def r62 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r46 digest) (r3 digest)

noncomputable def r63 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r62 digest) (r2 digest)

noncomputable def r64 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r46 digest) (r4 digest)

noncomputable def r65 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r64 digest) (r2 digest)

noncomputable def r66 (digest : BitVec 512) : LLVM.IntW 64 :=
  SLLVM.fshl (r48 digest) (r46 digest) (r5 digest)

noncomputable def r67 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r66 digest) (r2 digest)

noncomputable def r68 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r48 digest) (r6 digest)

noncomputable def r69 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r68 digest) (r2 digest)

noncomputable def r70 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r48 digest) (r7 digest)

noncomputable def r71 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r70 digest) (r2 digest)

noncomputable def r72 (digest : BitVec 512) : LLVM.IntW 64 :=
  SLLVM.fshl (r50 digest) (r48 digest) (r8 digest)

noncomputable def r73 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r72 digest) (r2 digest)

noncomputable def r74 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r50 digest) (r9 digest)

noncomputable def r75 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r74 digest) (r2 digest)

noncomputable def r76 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r50 digest) (r1 digest)

noncomputable def r77 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r76 digest) (r2 digest)

noncomputable def r78 (digest : BitVec 512) : LLVM.IntW 64 :=
  SLLVM.fshl (r52 digest) (r50 digest) (r10 digest)

noncomputable def r79 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r78 digest) (r2 digest)

noncomputable def r80 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r52 digest) (r11 digest)

noncomputable def r81 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r80 digest) (r2 digest)

noncomputable def r82 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r52 digest) (r12 digest)

noncomputable def r83 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r82 digest) (r2 digest)

noncomputable def r84 (digest : BitVec 512) : LLVM.IntW 64 :=
  SLLVM.fshl (r54 digest) (r52 digest) (r13 digest)

noncomputable def r85 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r84 digest) (r2 digest)

noncomputable def r86 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r54 digest) (r14 digest)

noncomputable def r87 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r86 digest) (r2 digest)

noncomputable def r88 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r54 digest) (r15 digest)

noncomputable def r89 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r88 digest) (r2 digest)

noncomputable def r90 (digest : BitVec 512) : LLVM.IntW 64 :=
  SLLVM.fshl (r56 digest) (r54 digest) (r16 digest)

noncomputable def r91 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r90 digest) (r2 digest)

noncomputable def r92 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r56 digest) (r0 digest)

noncomputable def r93 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r92 digest) (r2 digest)

noncomputable def r94 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r56 digest) (r17 digest)

noncomputable def r95 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r94 digest) (r2 digest)

noncomputable def r96 (digest : BitVec 512) : LLVM.IntW 64 :=
  SLLVM.fshl (r58 digest) (r56 digest) (r18 digest)

noncomputable def r97 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r96 digest) (r2 digest)

noncomputable def r98 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r58 digest) (r19 digest)

noncomputable def r99 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r98 digest) (r2 digest)

noncomputable def r100 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r58 digest) (r20 digest)

noncomputable def r101 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r100 digest) (r2 digest)

noncomputable def r102 (digest : BitVec 512) : LLVM.IntW 64 :=
  SLLVM.fshl (r60 digest) (r58 digest) (r21 digest)

noncomputable def r103 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r102 digest) (r2 digest)

noncomputable def r104 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r60 digest) (r22 digest)

noncomputable def r105 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r104 digest) (r2 digest)

noncomputable def r106 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r60 digest) (r23 digest)

noncomputable def r107 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r106 digest) (r24 digest) { nsw := true, nuw := true }

noncomputable def r108 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r107 digest) (r83 digest) { nsw := true, nuw := true }

noncomputable def r109 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r106 digest) (r25 digest) { nsw := true, nuw := true }

noncomputable def r110 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r109 digest) (r85 digest) { nsw := true, nuw := true }

noncomputable def r111 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r106 digest) (r26 digest) { nsw := true, nuw := true }

noncomputable def r112 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r111 digest) (r87 digest) { nsw := true, nuw := true }

noncomputable def r113 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r106 digest) (r27 digest) { nsw := true, nuw := false }

noncomputable def r114 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r113 digest) (r89 digest) { nsw := true, nuw := false }

noncomputable def r115 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r106 digest) (r28 digest) { nsw := true, nuw := true }

noncomputable def r116 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r115 digest) (r91 digest) { nsw := true, nuw := true }

noncomputable def r117 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r106 digest) (r29 digest) { nsw := true, nuw := false }

noncomputable def r118 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r117 digest) (r93 digest) { nsw := true, nuw := false }

noncomputable def r119 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r105 digest) (r24 digest) { nsw := true, nuw := true }

noncomputable def r120 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r105 digest) (r25 digest) { nsw := true, nuw := true }

noncomputable def r121 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r105 digest) (r26 digest) { nsw := true, nuw := true }

noncomputable def r122 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r105 digest) (r27 digest) { nsw := true, nuw := false }

noncomputable def r123 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r105 digest) (r28 digest) { nsw := true, nuw := true }

noncomputable def r124 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r114 digest) (r123 digest) { nsw := true, nuw := false }

noncomputable def r125 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r105 digest) (r29 digest) { nsw := true, nuw := false }

noncomputable def r126 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r116 digest) (r125 digest) { nsw := true, nuw := false }

noncomputable def r127 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r103 digest) (r24 digest) { nsw := true, nuw := true }

noncomputable def r128 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r103 digest) (r25 digest) { nsw := true, nuw := true }

noncomputable def r129 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r103 digest) (r26 digest) { nsw := true, nuw := true }

noncomputable def r130 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r103 digest) (r27 digest) { nsw := true, nuw := false }

noncomputable def r131 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r103 digest) (r28 digest) { nsw := true, nuw := true }

noncomputable def r132 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r103 digest) (r29 digest) { nsw := true, nuw := false }

noncomputable def r133 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r124 digest) (r132 digest) { nsw := true, nuw := false }

noncomputable def r134 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r101 digest) (r24 digest) { nsw := true, nuw := true }

noncomputable def r135 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r134 digest) (r77 digest) { nsw := true, nuw := true }

noncomputable def r136 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r101 digest) (r25 digest) { nsw := true, nuw := true }

noncomputable def r137 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r101 digest) (r26 digest) { nsw := true, nuw := true }

noncomputable def r138 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r101 digest) (r27 digest) { nsw := true, nuw := false }

noncomputable def r139 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r101 digest) (r28 digest) { nsw := true, nuw := true }

noncomputable def r140 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r101 digest) (r29 digest) { nsw := true, nuw := false }

noncomputable def r141 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r99 digest) (r24 digest) { nsw := true, nuw := true }

noncomputable def r142 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r141 digest) (r75 digest) { nsw := true, nuw := true }

noncomputable def r143 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r99 digest) (r25 digest) { nsw := true, nuw := true }

noncomputable def r144 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r135 digest) (r143 digest) { nsw := true, nuw := true }

noncomputable def r145 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r99 digest) (r26 digest) { nsw := true, nuw := true }

noncomputable def r146 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r99 digest) (r27 digest) { nsw := true, nuw := false }

noncomputable def r147 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r99 digest) (r28 digest) { nsw := true, nuw := true }

noncomputable def r148 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r99 digest) (r29 digest) { nsw := true, nuw := false }

noncomputable def r149 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r110 digest) (r139 digest) { nsw := true, nuw := true }

noncomputable def r150 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r149 digest) (r148 digest) { nsw := true, nuw := false }

noncomputable def r151 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r150 digest) (r121 digest) { nsw := true, nuw := false }

noncomputable def r152 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r151 digest) (r130 digest) { nsw := true, nuw := false }

noncomputable def r153 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r97 digest) (r24 digest) { nsw := true, nuw := true }

noncomputable def r154 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r153 digest) (r73 digest) { nsw := true, nuw := true }

noncomputable def r155 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r97 digest) (r25 digest) { nsw := true, nuw := true }

noncomputable def r156 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r142 digest) (r155 digest) { nsw := true, nuw := true }

noncomputable def r157 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r97 digest) (r26 digest) { nsw := true, nuw := true }

noncomputable def r158 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r144 digest) (r157 digest) { nsw := true, nuw := true }

noncomputable def r159 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r97 digest) (r27 digest) { nsw := true, nuw := false }

noncomputable def r160 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r97 digest) (r28 digest) { nsw := true, nuw := true }

noncomputable def r161 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r137 digest) (r81 digest) { nsw := true, nuw := true }

noncomputable def r162 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r161 digest) (r146 digest) { nsw := true, nuw := false }

noncomputable def r163 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r162 digest) (r160 digest) { nsw := true, nuw := false }

noncomputable def r164 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r163 digest) (r119 digest) { nsw := true, nuw := false }

noncomputable def r165 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r164 digest) (r128 digest) { nsw := true, nuw := false }

noncomputable def r166 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r97 digest) (r29 digest) { nsw := true, nuw := false }

noncomputable def r167 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r154 digest) (r30 digest) { nsw := true, nuw := true }

noncomputable def r168 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r167 digest) (r3 digest)

noncomputable def r169 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r156 digest) (r168 digest) { nsw := true, nuw := true }

noncomputable def r170 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r167 digest) (r31 digest)

noncomputable def r171 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r154 digest) (r170 digest) { nsw := true, nuw := false }

noncomputable def r172 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r158 digest) (r30 digest) { nsw := true, nuw := true }

noncomputable def r173 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r172 digest) (r3 digest)

noncomputable def r174 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r136 digest) (r79 digest) { nsw := true, nuw := true }

noncomputable def r175 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r174 digest) (r145 digest) { nsw := true, nuw := true }

noncomputable def r176 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r175 digest) (r159 digest) { nsw := true, nuw := false }

noncomputable def r177 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r176 digest) (r127 digest) { nsw := true, nuw := false }

noncomputable def r178 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r177 digest) (r173 digest) { nsw := true, nuw := false }

noncomputable def r179 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r172 digest) (r32 digest)

noncomputable def r180 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r158 digest) (r179 digest) { nsw := true, nuw := false }

noncomputable def r181 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r165 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r182 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r181 digest) (r3 digest)

noncomputable def r183 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r108 digest) (r138 digest) { nsw := true, nuw := false }

noncomputable def r184 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r183 digest) (r147 digest) { nsw := true, nuw := false }

noncomputable def r185 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r184 digest) (r166 digest) { nsw := true, nuw := false }

noncomputable def r186 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r185 digest) (r120 digest) { nsw := true, nuw := false }

noncomputable def r187 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r186 digest) (r129 digest) { nsw := true, nuw := false }

noncomputable def r188 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r187 digest) (r182 digest) { nsw := true, nuw := false }

noncomputable def r189 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r181 digest) (r32 digest)

noncomputable def r190 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r152 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r191 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r190 digest) (r3 digest)

noncomputable def r192 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r112 digest) (r140 digest) { nsw := true, nuw := false }

noncomputable def r193 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r192 digest) (r122 digest) { nsw := true, nuw := false }

noncomputable def r194 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r193 digest) (r131 digest) { nsw := true, nuw := false }

noncomputable def r195 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r194 digest) (r191 digest) { nsw := true, nuw := false }

noncomputable def r196 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r190 digest) (r32 digest)

noncomputable def r197 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r152 digest) (r196 digest) { nsw := true, nuw := false }

noncomputable def r198 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r133 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r199 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r198 digest) (r3 digest)

noncomputable def r200 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r126 digest) (r199 digest) { nsw := true, nuw := false }

noncomputable def r201 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r198 digest) (r32 digest)

noncomputable def r202 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r133 digest) (r201 digest) { nsw := true, nuw := false }

noncomputable def r203 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r118 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r204 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r203 digest) (r3 digest)

noncomputable def r205 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r204 digest) (r95 digest) { nsw := true, nuw := false }

noncomputable def r206 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r203 digest) (r32 digest)

noncomputable def r207 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r118 digest) (r206 digest) { nsw := true, nuw := false }

noncomputable def r208 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r169 digest) (r30 digest) { nsw := true, nuw := true }

noncomputable def r209 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r208 digest) (r3 digest)

noncomputable def r210 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r208 digest) (r32 digest)

noncomputable def r211 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r178 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r212 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r211 digest) (r3 digest)

noncomputable def r213 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r211 digest) (r32 digest)

noncomputable def r214 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r188 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r215 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r214 digest) (r3 digest)

noncomputable def r216 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r215 digest) (r197 digest) { nsw := true, nuw := false }

noncomputable def r217 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r214 digest) (r32 digest)

noncomputable def r218 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r188 digest) (r217 digest) { nsw := true, nuw := false }

noncomputable def r219 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r195 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r220 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r219 digest) (r3 digest)

noncomputable def r221 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r220 digest) (r202 digest) { nsw := true, nuw := false }

noncomputable def r222 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r219 digest) (r32 digest)

noncomputable def r223 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r195 digest) (r222 digest) { nsw := true, nuw := false }

noncomputable def r224 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r200 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r225 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r224 digest) (r3 digest)

noncomputable def r226 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r225 digest) (r207 digest) { nsw := true, nuw := false }

noncomputable def r227 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r224 digest) (r32 digest)

noncomputable def r228 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r200 digest) (r227 digest) { nsw := true, nuw := false }

noncomputable def r229 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r205 digest) (r24 digest) { nsw := true, nuw := false }

noncomputable def r230 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r229 digest) (r71 digest) { nsw := true, nuw := false }

noncomputable def r231 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r205 digest) (r25 digest) { nsw := true, nuw := false }

noncomputable def r232 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r171 digest) (r231 digest) { nsw := true, nuw := false }

noncomputable def r233 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r205 digest) (r26 digest) { nsw := true, nuw := false }

noncomputable def r234 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r205 digest) (r27 digest) { nsw := true, nuw := false }

noncomputable def r235 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r205 digest) (r28 digest) { nsw := true, nuw := false }

noncomputable def r236 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r205 digest) (r29 digest) { nsw := true, nuw := false }

noncomputable def r237 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r165 digest) (r236 digest) { nsw := true, nuw := false }

noncomputable def r238 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r237 digest) (r189 digest) { nsw := false, nuw := false }

noncomputable def r239 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r238 digest) (r212 digest) { nsw := false, nuw := false }

noncomputable def r240 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r226 digest) (r24 digest) { nsw := true, nuw := false }

noncomputable def r241 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r240 digest) (r69 digest) { nsw := true, nuw := false }

noncomputable def r242 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r226 digest) (r25 digest) { nsw := true, nuw := false }

noncomputable def r243 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r230 digest) (r242 digest) { nsw := true, nuw := false }

noncomputable def r244 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r226 digest) (r26 digest) { nsw := true, nuw := false }

noncomputable def r245 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r232 digest) (r244 digest) { nsw := true, nuw := false }

noncomputable def r246 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r226 digest) (r27 digest) { nsw := false, nuw := false }

noncomputable def r247 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r226 digest) (r28 digest) { nsw := true, nuw := false }

noncomputable def r248 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r226 digest) (r29 digest) { nsw := false, nuw := false }

noncomputable def r249 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r228 digest) (r24 digest) { nsw := true, nuw := false }

noncomputable def r250 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r249 digest) (r67 digest) { nsw := true, nuw := false }

noncomputable def r251 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r228 digest) (r25 digest) { nsw := true, nuw := false }

noncomputable def r252 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r241 digest) (r251 digest) { nsw := true, nuw := false }

noncomputable def r253 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r228 digest) (r26 digest) { nsw := true, nuw := false }

noncomputable def r254 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r243 digest) (r253 digest) { nsw := true, nuw := false }

noncomputable def r255 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r228 digest) (r27 digest) { nsw := false, nuw := false }

noncomputable def r256 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r245 digest) (r255 digest) { nsw := false, nuw := false }

noncomputable def r257 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r228 digest) (r28 digest) { nsw := true, nuw := false }

noncomputable def r258 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r228 digest) (r29 digest) { nsw := false, nuw := false }

noncomputable def r259 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r180 digest) (r234 digest) { nsw := true, nuw := false }

noncomputable def r260 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r259 digest) (r209 digest) { nsw := true, nuw := false }

noncomputable def r261 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r260 digest) (r247 digest) { nsw := true, nuw := false }

noncomputable def r262 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r261 digest) (r258 digest) { nsw := false, nuw := false }

noncomputable def r263 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r221 digest) (r24 digest) { nsw := true, nuw := false }

noncomputable def r264 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r263 digest) (r65 digest) { nsw := true, nuw := false }

noncomputable def r265 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r221 digest) (r25 digest) { nsw := true, nuw := false }

noncomputable def r266 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r250 digest) (r265 digest) { nsw := true, nuw := false }

noncomputable def r267 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r221 digest) (r26 digest) { nsw := true, nuw := false }

noncomputable def r268 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r252 digest) (r267 digest) { nsw := true, nuw := false }

noncomputable def r269 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r221 digest) (r27 digest) { nsw := false, nuw := false }

noncomputable def r270 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r254 digest) (r269 digest) { nsw := false, nuw := false }

noncomputable def r271 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r221 digest) (r28 digest) { nsw := true, nuw := false }

noncomputable def r272 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r256 digest) (r271 digest) { nsw := true, nuw := false }

noncomputable def r273 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r221 digest) (r29 digest) { nsw := false, nuw := false }

noncomputable def r274 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r223 digest) (r24 digest) { nsw := true, nuw := false }

noncomputable def r275 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r274 digest) (r63 digest) { nsw := true, nuw := false }

noncomputable def r276 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r223 digest) (r25 digest) { nsw := true, nuw := false }

noncomputable def r277 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r264 digest) (r276 digest) { nsw := true, nuw := false }

noncomputable def r278 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r223 digest) (r26 digest) { nsw := true, nuw := false }

noncomputable def r279 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r266 digest) (r278 digest) { nsw := true, nuw := false }

noncomputable def r280 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r223 digest) (r27 digest) { nsw := false, nuw := false }

noncomputable def r281 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r268 digest) (r280 digest) { nsw := false, nuw := false }

noncomputable def r282 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r223 digest) (r28 digest) { nsw := true, nuw := false }

noncomputable def r283 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r270 digest) (r282 digest) { nsw := true, nuw := false }

noncomputable def r284 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r223 digest) (r29 digest) { nsw := false, nuw := false }

noncomputable def r285 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r272 digest) (r284 digest) { nsw := false, nuw := false }

noncomputable def r286 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r216 digest) (r24 digest) { nsw := true, nuw := false }

noncomputable def r287 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r286 digest) (r61 digest) { nsw := true, nuw := false }

noncomputable def r288 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r216 digest) (r25 digest) { nsw := true, nuw := false }

noncomputable def r289 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r275 digest) (r288 digest) { nsw := true, nuw := false }

noncomputable def r290 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r216 digest) (r26 digest) { nsw := true, nuw := false }

noncomputable def r291 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r277 digest) (r290 digest) { nsw := true, nuw := false }

noncomputable def r292 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r216 digest) (r27 digest) { nsw := false, nuw := false }

noncomputable def r293 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r279 digest) (r292 digest) { nsw := false, nuw := false }

noncomputable def r294 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r216 digest) (r28 digest) { nsw := true, nuw := false }

noncomputable def r295 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r281 digest) (r294 digest) { nsw := true, nuw := false }

noncomputable def r296 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r216 digest) (r29 digest) { nsw := false, nuw := false }

noncomputable def r297 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r283 digest) (r296 digest) { nsw := false, nuw := false }

noncomputable def r298 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r287 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r299 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r298 digest) (r3 digest)

noncomputable def r300 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r289 digest) (r299 digest) { nsw := true, nuw := false }

noncomputable def r301 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r298 digest) (r32 digest)

noncomputable def r302 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r287 digest) (r301 digest) { nsw := true, nuw := false }

noncomputable def r303 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r291 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r304 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r303 digest) (r3 digest)

noncomputable def r305 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r293 digest) (r304 digest) { nsw := true, nuw := false }

noncomputable def r306 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r303 digest) (r32 digest)

noncomputable def r307 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r291 digest) (r306 digest) { nsw := false, nuw := false }

noncomputable def r308 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r295 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r309 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r308 digest) (r3 digest)

noncomputable def r310 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r297 digest) (r309 digest) { nsw := true, nuw := false }

noncomputable def r311 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r308 digest) (r32 digest)

noncomputable def r312 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r295 digest) (r311 digest) { nsw := false, nuw := false }

noncomputable def r313 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r285 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r314 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r313 digest) (r3 digest)

noncomputable def r315 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r233 digest) (r169 digest) { nsw := true, nuw := false }

noncomputable def r316 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r315 digest) (r210 digest) { nsw := true, nuw := false }

noncomputable def r317 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r316 digest) (r246 digest) { nsw := false, nuw := false }

noncomputable def r318 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r317 digest) (r257 digest) { nsw := true, nuw := false }

noncomputable def r319 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r318 digest) (r273 digest) { nsw := false, nuw := false }

noncomputable def r320 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r319 digest) (r314 digest) { nsw := true, nuw := false }

noncomputable def r321 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r313 digest) (r32 digest)

noncomputable def r322 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r285 digest) (r321 digest) { nsw := false, nuw := false }

noncomputable def r323 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r262 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r324 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r323 digest) (r3 digest)

noncomputable def r325 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r178 digest) (r235 digest) { nsw := true, nuw := false }

noncomputable def r326 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r325 digest) (r213 digest) { nsw := false, nuw := false }

noncomputable def r327 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r326 digest) (r248 digest) { nsw := false, nuw := false }

noncomputable def r328 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r327 digest) (r324 digest) { nsw := true, nuw := false }

noncomputable def r329 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r323 digest) (r32 digest)

noncomputable def r330 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r262 digest) (r329 digest) { nsw := false, nuw := false }

noncomputable def r331 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r239 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r332 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r331 digest) (r3 digest)

noncomputable def r333 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r332 digest) (r218 digest) { nsw := true, nuw := false }

noncomputable def r334 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r331 digest) (r32 digest)

noncomputable def r335 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r239 digest) (r334 digest) { nsw := false, nuw := false }

noncomputable def r336 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r300 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r337 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r336 digest) (r3 digest)

noncomputable def r338 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r336 digest) (r32 digest)

noncomputable def r339 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r305 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r340 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r339 digest) (r3 digest)

noncomputable def r341 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r339 digest) (r32 digest)

noncomputable def r342 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r310 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r343 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r342 digest) (r3 digest)

noncomputable def r344 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r322 digest) (r343 digest) { nsw := true, nuw := false }

noncomputable def r345 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r342 digest) (r32 digest)

noncomputable def r346 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r320 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r347 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r346 digest) (r3 digest)

noncomputable def r348 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r330 digest) (r347 digest) { nsw := true, nuw := false }

noncomputable def r349 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r346 digest) (r32 digest)

noncomputable def r350 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r320 digest) (r349 digest) { nsw := true, nuw := false }

noncomputable def r351 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r328 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r352 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r351 digest) (r3 digest)

noncomputable def r353 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r335 digest) (r352 digest) { nsw := true, nuw := false }

noncomputable def r354 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r351 digest) (r32 digest)

noncomputable def r355 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r328 digest) (r354 digest) { nsw := true, nuw := false }

noncomputable def r356 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r333 digest) (r30 digest) { nsw := true, nuw := false }

noncomputable def r357 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r356 digest) (r3 digest)

noncomputable def r358 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r356 digest) (r32 digest)

noncomputable def r359 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r333 digest) (r358 digest) { nsw := true, nuw := false }

noncomputable def r360 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r357 digest) (r24 digest) { nsw := true, nuw := false }

noncomputable def r361 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r302 digest) (r360 digest) { nsw := true, nuw := false }

noncomputable def r362 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r357 digest) (r25 digest) { nsw := true, nuw := false }

noncomputable def r363 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r357 digest) (r26 digest) { nsw := true, nuw := false }

noncomputable def r364 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r357 digest) (r27 digest) { nsw := true, nuw := false }

noncomputable def r365 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r357 digest) (r28 digest) { nsw := true, nuw := false }

noncomputable def r366 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r357 digest) (r29 digest) { nsw := true, nuw := false }

noncomputable def r367 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r361 digest) (r3 digest)

noncomputable def r368 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r362 digest) (r300 digest) { nsw := false, nuw := false }

noncomputable def r369 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r368 digest) (r338 digest) { nsw := false, nuw := false }

noncomputable def r370 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r369 digest) (r367 digest) { nsw := true, nuw := false }

noncomputable def r371 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r361 digest) (r2 digest)

noncomputable def r372 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r370 digest) (r3 digest)

noncomputable def r373 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r307 digest) (r363 digest) { nsw := false, nuw := false }

noncomputable def r374 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r373 digest) (r337 digest) { nsw := false, nuw := false }

noncomputable def r375 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r374 digest) (r372 digest) { nsw := true, nuw := false }

noncomputable def r376 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r370 digest) (r2 digest)

noncomputable def r377 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r375 digest) (r3 digest)

noncomputable def r378 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r305 digest) (r364 digest) { nsw := false, nuw := false }

noncomputable def r379 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r378 digest) (r341 digest) { nsw := false, nuw := false }

noncomputable def r380 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r379 digest) (r377 digest) { nsw := true, nuw := false }

noncomputable def r381 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r375 digest) (r2 digest)

noncomputable def r382 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r380 digest) (r3 digest)

noncomputable def r383 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r312 digest) (r365 digest) { nsw := false, nuw := false }

noncomputable def r384 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r383 digest) (r340 digest) { nsw := false, nuw := false }

noncomputable def r385 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r384 digest) (r382 digest) { nsw := true, nuw := false }

noncomputable def r386 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r380 digest) (r2 digest)

noncomputable def r387 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r385 digest) (r3 digest)

noncomputable def r388 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r310 digest) (r366 digest) { nsw := false, nuw := false }

noncomputable def r389 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.sub (r388 digest) (r345 digest) { nsw := false, nuw := false }

noncomputable def r390 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r389 digest) (r387 digest) { nsw := true, nuw := false }

noncomputable def r391 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r385 digest) (r2 digest)

noncomputable def r392 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r390 digest) (r3 digest)

noncomputable def r393 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r344 digest) (r392 digest) { nsw := true, nuw := false }

noncomputable def r394 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r390 digest) (r2 digest)

noncomputable def r395 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r393 digest) (r3 digest)

noncomputable def r396 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r395 digest) (r350 digest) { nsw := true, nuw := false }

noncomputable def r397 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r393 digest) (r2 digest)

noncomputable def r398 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r396 digest) (r3 digest)

noncomputable def r399 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r348 digest) (r398 digest) { nsw := true, nuw := false }

noncomputable def r400 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r396 digest) (r2 digest)

noncomputable def r401 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r399 digest) (r3 digest)

noncomputable def r402 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r401 digest) (r355 digest) { nsw := true, nuw := false }

noncomputable def r403 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r399 digest) (r2 digest)

noncomputable def r404 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r402 digest) (r3 digest)

noncomputable def r405 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r353 digest) (r404 digest) { nsw := true, nuw := false }

noncomputable def r406 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r402 digest) (r2 digest)

noncomputable def r407 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r405 digest) (r3 digest)

noncomputable def r408 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r407 digest) (r359 digest) { nsw := true, nuw := false }

noncomputable def r409 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r405 digest) (r2 digest)

noncomputable def r410 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r408 digest) (r3 digest)

noncomputable def r411 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r408 digest) (r2 digest)

noncomputable def r412 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r410 digest) (r24 digest) { nsw := true, nuw := false }

noncomputable def r413 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r412 digest) (r371 digest) { nsw := true, nuw := false }

noncomputable def r414 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r410 digest) (r25 digest) { nsw := true, nuw := false }

noncomputable def r415 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r414 digest) (r376 digest) { nsw := true, nuw := false }

noncomputable def r416 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r410 digest) (r26 digest) { nsw := true, nuw := false }

noncomputable def r417 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r416 digest) (r381 digest) { nsw := true, nuw := false }

noncomputable def r418 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r410 digest) (r27 digest) { nsw := true, nuw := false }

noncomputable def r419 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r418 digest) (r386 digest) { nsw := true, nuw := false }

noncomputable def r420 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r410 digest) (r28 digest) { nsw := true, nuw := false }

noncomputable def r421 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r420 digest) (r391 digest) { nsw := true, nuw := false }

noncomputable def r422 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.mul (r410 digest) (r29 digest) { nsw := true, nuw := false }

noncomputable def r423 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r422 digest) (r394 digest) { nsw := true, nuw := false }

noncomputable def r424 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r413 digest) (r3 digest)

noncomputable def r425 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r415 digest) (r424 digest) { nsw := true, nuw := false }

noncomputable def r426 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r413 digest) (r2 digest)

noncomputable def r427 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r425 digest) (r3 digest)

noncomputable def r428 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r417 digest) (r427 digest) { nsw := true, nuw := false }

noncomputable def r429 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r428 digest) (r3 digest)

noncomputable def r430 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r419 digest) (r429 digest) { nsw := true, nuw := false }

noncomputable def r431 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r430 digest) (r3 digest)

noncomputable def r432 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r421 digest) (r431 digest) { nsw := true, nuw := false }

noncomputable def r433 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r432 digest) (r3 digest)

noncomputable def r434 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r423 digest) (r433 digest) { nsw := true, nuw := false }

noncomputable def r435 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r434 digest) (r3 digest)

noncomputable def r436 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r435 digest) (r397 digest) { nsw := true, nuw := false }

noncomputable def r437 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r436 digest) (r3 digest)

noncomputable def r438 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r437 digest) (r400 digest) { nsw := true, nuw := false }

noncomputable def r439 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r438 digest) (r3 digest)

noncomputable def r440 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r439 digest) (r403 digest) { nsw := true, nuw := false }

noncomputable def r441 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r440 digest) (r3 digest)

noncomputable def r442 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r441 digest) (r406 digest) { nsw := true, nuw := false }

noncomputable def r443 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r442 digest) (r3 digest)

noncomputable def r444 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r443 digest) (r409 digest) { nsw := true, nuw := false }

noncomputable def r445 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.ashr (r444 digest) (r3 digest)

noncomputable def r446 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.add (r445 digest) (r411 digest) { nsw := true, nuw := false }

noncomputable def r447 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.shl (r425 digest) (r3 digest) { nsw := false, nuw := false }

noncomputable def r448 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r447 digest) (r33 digest)

noncomputable def r449 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.or (r448 digest) (r426 digest)

noncomputable def r450 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.shl (r428 digest) (r4 digest) { nsw := false, nuw := false }

noncomputable def r451 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r450 digest) (r34 digest)

noncomputable def r452 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.or (r449 digest) (r451 digest)

noncomputable def r453 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.shl (r430 digest) (r35 digest) { nsw := false, nuw := false }

noncomputable def r454 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.or (r452 digest) (r453 digest)

noncomputable def r455 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r430 digest) (r5 digest)

noncomputable def r456 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r455 digest) (r36 digest)

noncomputable def r457 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.shl (r432 digest) (r6 digest) { nsw := false, nuw := false }

noncomputable def r458 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r457 digest) (r37 digest)

noncomputable def r459 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.or (r458 digest) (r456 digest)

noncomputable def r460 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.shl (r434 digest) (r7 digest) { nsw := false, nuw := false }

noncomputable def r461 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r460 digest) (r38 digest)

noncomputable def r462 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.or (r459 digest) (r461 digest)

noncomputable def r463 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.shl (r436 digest) (r39 digest) { nsw := false, nuw := false }

noncomputable def r464 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.or (r462 digest) (r463 digest)

noncomputable def r466 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r436 digest) (r8 digest)

noncomputable def r467 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r466 digest) (r40 digest)

noncomputable def r468 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.shl (r438 digest) (r9 digest) { nsw := true, nuw := false }

noncomputable def r469 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r468 digest) (r41 digest)

noncomputable def r470 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.or (r469 digest) (r467 digest)

noncomputable def r471 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.shl (r440 digest) (r1 digest) { nsw := true, nuw := false }

noncomputable def r472 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r471 digest) (r42 digest)

noncomputable def r473 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.or (r470 digest) (r472 digest)

noncomputable def r474 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.shl (r442 digest) (r43 digest) { nsw := false, nuw := false }

noncomputable def r475 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.or (r473 digest) (r474 digest)

noncomputable def r477 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.lshr (r442 digest) (r10 digest)

noncomputable def r478 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r477 digest) (r44 digest)

noncomputable def r479 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.shl (r444 digest) (r11 digest) { nsw := true, nuw := false }

noncomputable def r480 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.and (r479 digest) (r45 digest)

noncomputable def r481 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.or (r478 digest) (r480 digest)

noncomputable def r482 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.shl (r446 digest) (r12 digest) { nsw := true, nuw := false }

noncomputable def r483 (digest : BitVec 512) : LLVM.IntW 64 :=
  LLVM.or (r481 digest) (r482 digest)

noncomputable def reduce (digest : BitVec 512) : Option (Fin 4 → BitVec 64) :=
  wordsOf (r454 digest) (r464 digest) (r475 digest) (r483 digest)

end Firedancer.Common.ScalarArithmetic.Registers
