import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.SourceAlignment0

namespace Firedancer.Common.ScalarArithmetic.Registers
open InstCombine (LLVM)

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem op_107 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 107) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_107 (digest : BitVec 512) :
    (source_stage_expr 107) digest = r107 digest :=
  source_stage_congruence 107 digest

theorem op_108 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 108) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_108 (digest : BitVec 512) :
    (source_stage_expr 108) digest = r108 digest :=
  source_stage_congruence 108 digest

theorem op_109 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 109) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_109 (digest : BitVec 512) :
    (source_stage_expr 109) digest = r109 digest :=
  source_stage_congruence 109 digest

theorem op_110 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 110) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_110 (digest : BitVec 512) :
    (source_stage_expr 110) digest = r110 digest :=
  source_stage_congruence 110 digest

theorem op_111 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 111) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_111 (digest : BitVec 512) :
    (source_stage_expr 111) digest = r111 digest :=
  source_stage_congruence 111 digest

theorem op_112 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 112) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_112 (digest : BitVec 512) :
    (source_stage_expr 112) digest = r112 digest :=
  source_stage_congruence 112 digest

theorem op_113 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 113) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_113 (digest : BitVec 512) :
    (source_stage_expr 113) digest = r113 digest :=
  source_stage_congruence 113 digest

theorem op_114 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 114) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_114 (digest : BitVec 512) :
    (source_stage_expr 114) digest = r114 digest :=
  source_stage_congruence 114 digest

theorem op_115 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 115) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_115 (digest : BitVec 512) :
    (source_stage_expr 115) digest = r115 digest :=
  source_stage_congruence 115 digest

theorem op_116 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 116) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_116 (digest : BitVec 512) :
    (source_stage_expr 116) digest = r116 digest :=
  source_stage_congruence 116 digest

theorem op_117 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 117) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_117 (digest : BitVec 512) :
    (source_stage_expr 117) digest = r117 digest :=
  source_stage_congruence 117 digest

theorem op_118 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 118) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_118 (digest : BitVec 512) :
    (source_stage_expr 118) digest = r118 digest :=
  source_stage_congruence 118 digest

theorem op_119 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 119) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_119 (digest : BitVec 512) :
    (source_stage_expr 119) digest = r119 digest :=
  source_stage_congruence 119 digest

theorem op_120 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 120) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_120 (digest : BitVec 512) :
    (source_stage_expr 120) digest = r120 digest :=
  source_stage_congruence 120 digest

theorem op_121 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 121) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_121 (digest : BitVec 512) :
    (source_stage_expr 121) digest = r121 digest :=
  source_stage_congruence 121 digest

theorem op_122 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 122) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_122 (digest : BitVec 512) :
    (source_stage_expr 122) digest = r122 digest :=
  source_stage_congruence 122 digest

theorem op_123 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 123) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_123 (digest : BitVec 512) :
    (source_stage_expr 123) digest = r123 digest :=
  source_stage_congruence 123 digest

theorem op_124 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 124) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_124 (digest : BitVec 512) :
    (source_stage_expr 124) digest = r124 digest :=
  source_stage_congruence 124 digest

theorem op_125 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 125) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_125 (digest : BitVec 512) :
    (source_stage_expr 125) digest = r125 digest :=
  source_stage_congruence 125 digest

theorem op_126 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 126) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_126 (digest : BitVec 512) :
    (source_stage_expr 126) digest = r126 digest :=
  source_stage_congruence 126 digest

theorem op_127 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 127) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_127 (digest : BitVec 512) :
    (source_stage_expr 127) digest = r127 digest :=
  source_stage_congruence 127 digest

theorem op_128 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 128) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_128 (digest : BitVec 512) :
    (source_stage_expr 128) digest = r128 digest :=
  source_stage_congruence 128 digest

theorem op_129 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 129) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_129 (digest : BitVec 512) :
    (source_stage_expr 129) digest = r129 digest :=
  source_stage_congruence 129 digest

theorem op_130 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 130) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_130 (digest : BitVec 512) :
    (source_stage_expr 130) digest = r130 digest :=
  source_stage_congruence 130 digest

theorem op_131 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 131) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_131 (digest : BitVec 512) :
    (source_stage_expr 131) digest = r131 digest :=
  source_stage_congruence 131 digest

theorem op_132 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 132) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_132 (digest : BitVec 512) :
    (source_stage_expr 132) digest = r132 digest :=
  source_stage_congruence 132 digest

theorem op_133 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 133) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_133 (digest : BitVec 512) :
    (source_stage_expr 133) digest = r133 digest :=
  source_stage_congruence 133 digest

theorem op_134 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 134) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_134 (digest : BitVec 512) :
    (source_stage_expr 134) digest = r134 digest :=
  source_stage_congruence 134 digest

theorem op_135 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 135) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_135 (digest : BitVec 512) :
    (source_stage_expr 135) digest = r135 digest :=
  source_stage_congruence 135 digest

theorem op_136 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 136) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_136 (digest : BitVec 512) :
    (source_stage_expr 136) digest = r136 digest :=
  source_stage_congruence 136 digest

theorem op_137 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 137) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_137 (digest : BitVec 512) :
    (source_stage_expr 137) digest = r137 digest :=
  source_stage_congruence 137 digest

theorem op_138 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 138) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_138 (digest : BitVec 512) :
    (source_stage_expr 138) digest = r138 digest :=
  source_stage_congruence 138 digest

theorem op_139 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 139) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_139 (digest : BitVec 512) :
    (source_stage_expr 139) digest = r139 digest :=
  source_stage_congruence 139 digest

theorem op_140 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 140) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_140 (digest : BitVec 512) :
    (source_stage_expr 140) digest = r140 digest :=
  source_stage_congruence 140 digest

theorem op_141 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 141) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_141 (digest : BitVec 512) :
    (source_stage_expr 141) digest = r141 digest :=
  source_stage_congruence 141 digest

theorem op_142 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 142) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_142 (digest : BitVec 512) :
    (source_stage_expr 142) digest = r142 digest :=
  source_stage_congruence 142 digest

theorem op_143 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 143) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_143 (digest : BitVec 512) :
    (source_stage_expr 143) digest = r143 digest :=
  source_stage_congruence 143 digest

theorem op_144 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 144) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_144 (digest : BitVec 512) :
    (source_stage_expr 144) digest = r144 digest :=
  source_stage_congruence 144 digest

theorem op_145 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 145) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_145 (digest : BitVec 512) :
    (source_stage_expr 145) digest = r145 digest :=
  source_stage_congruence 145 digest

theorem op_146 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 146) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_146 (digest : BitVec 512) :
    (source_stage_expr 146) digest = r146 digest :=
  source_stage_congruence 146 digest

theorem op_147 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 147) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_147 (digest : BitVec 512) :
    (source_stage_expr 147) digest = r147 digest :=
  source_stage_congruence 147 digest

theorem op_148 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 148) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_148 (digest : BitVec 512) :
    (source_stage_expr 148) digest = r148 digest :=
  source_stage_congruence 148 digest

theorem op_149 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 149) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_149 (digest : BitVec 512) :
    (source_stage_expr 149) digest = r149 digest :=
  source_stage_congruence 149 digest

theorem op_150 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 150) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_150 (digest : BitVec 512) :
    (source_stage_expr 150) digest = r150 digest :=
  source_stage_congruence 150 digest

theorem op_151 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 151) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_151 (digest : BitVec 512) :
    (source_stage_expr 151) digest = r151 digest :=
  source_stage_congruence 151 digest

theorem op_152 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 152) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_152 (digest : BitVec 512) :
    (source_stage_expr 152) digest = r152 digest :=
  source_stage_congruence 152 digest

theorem op_153 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 153) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_153 (digest : BitVec 512) :
    (source_stage_expr 153) digest = r153 digest :=
  source_stage_congruence 153 digest

theorem op_154 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 154) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_154 (digest : BitVec 512) :
    (source_stage_expr 154) digest = r154 digest :=
  source_stage_congruence 154 digest

theorem op_155 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 155) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_155 (digest : BitVec 512) :
    (source_stage_expr 155) digest = r155 digest :=
  source_stage_congruence 155 digest

theorem op_156 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 156) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_156 (digest : BitVec 512) :
    (source_stage_expr 156) digest = r156 digest :=
  source_stage_congruence 156 digest

theorem op_157 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 157) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_157 (digest : BitVec 512) :
    (source_stage_expr 157) digest = r157 digest :=
  source_stage_congruence 157 digest

theorem op_158 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 158) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_158 (digest : BitVec 512) :
    (source_stage_expr 158) digest = r158 digest :=
  source_stage_congruence 158 digest

theorem op_159 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 159) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_159 (digest : BitVec 512) :
    (source_stage_expr 159) digest = r159 digest :=
  source_stage_congruence 159 digest

theorem op_160 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 160) digest a b = LLVM.mul a b { nsw := true, nuw := true } := rfl

theorem align_160 (digest : BitVec 512) :
    (source_stage_expr 160) digest = r160 digest :=
  source_stage_congruence 160 digest

theorem op_161 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 161) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_161 (digest : BitVec 512) :
    (source_stage_expr 161) digest = r161 digest :=
  source_stage_congruence 161 digest

theorem op_162 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 162) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_162 (digest : BitVec 512) :
    (source_stage_expr 162) digest = r162 digest :=
  source_stage_congruence 162 digest

theorem op_163 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 163) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_163 (digest : BitVec 512) :
    (source_stage_expr 163) digest = r163 digest :=
  source_stage_congruence 163 digest

theorem op_164 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 164) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_164 (digest : BitVec 512) :
    (source_stage_expr 164) digest = r164 digest :=
  source_stage_congruence 164 digest

theorem op_165 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 165) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_165 (digest : BitVec 512) :
    (source_stage_expr 165) digest = r165 digest :=
  source_stage_congruence 165 digest

theorem op_166 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 166) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_166 (digest : BitVec 512) :
    (source_stage_expr 166) digest = r166 digest :=
  source_stage_congruence 166 digest

end Firedancer.Common.ScalarArithmetic.Registers
