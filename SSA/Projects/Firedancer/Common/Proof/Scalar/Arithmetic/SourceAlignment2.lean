import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.SourceAlignment1

namespace Firedancer.Common.ScalarArithmetic.Registers
open InstCombine (LLVM)

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem op_167 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 167) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_167 (digest : BitVec 512) :
    (source_stage_expr 167) digest = r167 digest :=
  source_stage_congruence 167 digest

theorem op_168 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 168) digest a b = LLVM.lshr a b := rfl

theorem align_168 (digest : BitVec 512) :
    (source_stage_expr 168) digest = r168 digest :=
  source_stage_congruence 168 digest

theorem op_169 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 169) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_169 (digest : BitVec 512) :
    (source_stage_expr 169) digest = r169 digest :=
  source_stage_congruence 169 digest

theorem op_170 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 170) digest a b = LLVM.and a b := rfl

theorem align_170 (digest : BitVec 512) :
    (source_stage_expr 170) digest = r170 digest :=
  source_stage_congruence 170 digest

theorem op_171 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 171) digest a b = LLVM.sub a b { nsw := true, nuw := false } := rfl

theorem align_171 (digest : BitVec 512) :
    (source_stage_expr 171) digest = r171 digest :=
  source_stage_congruence 171 digest

theorem op_172 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 172) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_172 (digest : BitVec 512) :
    (source_stage_expr 172) digest = r172 digest :=
  source_stage_congruence 172 digest

theorem op_173 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 173) digest a b = LLVM.lshr a b := rfl

theorem align_173 (digest : BitVec 512) :
    (source_stage_expr 173) digest = r173 digest :=
  source_stage_congruence 173 digest

theorem op_174 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 174) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_174 (digest : BitVec 512) :
    (source_stage_expr 174) digest = r174 digest :=
  source_stage_congruence 174 digest

theorem op_175 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 175) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_175 (digest : BitVec 512) :
    (source_stage_expr 175) digest = r175 digest :=
  source_stage_congruence 175 digest

theorem op_176 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 176) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_176 (digest : BitVec 512) :
    (source_stage_expr 176) digest = r176 digest :=
  source_stage_congruence 176 digest

theorem op_177 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 177) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_177 (digest : BitVec 512) :
    (source_stage_expr 177) digest = r177 digest :=
  source_stage_congruence 177 digest

theorem op_178 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 178) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_178 (digest : BitVec 512) :
    (source_stage_expr 178) digest = r178 digest :=
  source_stage_congruence 178 digest

theorem op_179 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 179) digest a b = LLVM.and a b := rfl

theorem align_179 (digest : BitVec 512) :
    (source_stage_expr 179) digest = r179 digest :=
  source_stage_congruence 179 digest

theorem op_180 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 180) digest a b = LLVM.sub a b { nsw := true, nuw := false } := rfl

theorem align_180 (digest : BitVec 512) :
    (source_stage_expr 180) digest = r180 digest :=
  source_stage_congruence 180 digest

theorem op_181 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 181) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_181 (digest : BitVec 512) :
    (source_stage_expr 181) digest = r181 digest :=
  source_stage_congruence 181 digest

theorem op_182 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 182) digest a b = LLVM.ashr a b := rfl

theorem align_182 (digest : BitVec 512) :
    (source_stage_expr 182) digest = r182 digest :=
  source_stage_congruence 182 digest

theorem op_183 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 183) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_183 (digest : BitVec 512) :
    (source_stage_expr 183) digest = r183 digest :=
  source_stage_congruence 183 digest

theorem op_184 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 184) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_184 (digest : BitVec 512) :
    (source_stage_expr 184) digest = r184 digest :=
  source_stage_congruence 184 digest

theorem op_185 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 185) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_185 (digest : BitVec 512) :
    (source_stage_expr 185) digest = r185 digest :=
  source_stage_congruence 185 digest

theorem op_186 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 186) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_186 (digest : BitVec 512) :
    (source_stage_expr 186) digest = r186 digest :=
  source_stage_congruence 186 digest

theorem op_187 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 187) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_187 (digest : BitVec 512) :
    (source_stage_expr 187) digest = r187 digest :=
  source_stage_congruence 187 digest

theorem op_188 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 188) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_188 (digest : BitVec 512) :
    (source_stage_expr 188) digest = r188 digest :=
  source_stage_congruence 188 digest

theorem op_189 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 189) digest a b = LLVM.and a b := rfl

theorem align_189 (digest : BitVec 512) :
    (source_stage_expr 189) digest = r189 digest :=
  source_stage_congruence 189 digest

theorem op_190 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 190) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_190 (digest : BitVec 512) :
    (source_stage_expr 190) digest = r190 digest :=
  source_stage_congruence 190 digest

theorem op_191 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 191) digest a b = LLVM.ashr a b := rfl

theorem align_191 (digest : BitVec 512) :
    (source_stage_expr 191) digest = r191 digest :=
  source_stage_congruence 191 digest

theorem op_192 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 192) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_192 (digest : BitVec 512) :
    (source_stage_expr 192) digest = r192 digest :=
  source_stage_congruence 192 digest

theorem op_193 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 193) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_193 (digest : BitVec 512) :
    (source_stage_expr 193) digest = r193 digest :=
  source_stage_congruence 193 digest

theorem op_194 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 194) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_194 (digest : BitVec 512) :
    (source_stage_expr 194) digest = r194 digest :=
  source_stage_congruence 194 digest

theorem op_195 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 195) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_195 (digest : BitVec 512) :
    (source_stage_expr 195) digest = r195 digest :=
  source_stage_congruence 195 digest

theorem op_196 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 196) digest a b = LLVM.and a b := rfl

theorem align_196 (digest : BitVec 512) :
    (source_stage_expr 196) digest = r196 digest :=
  source_stage_congruence 196 digest

theorem op_197 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 197) digest a b = LLVM.sub a b { nsw := true, nuw := false } := rfl

theorem align_197 (digest : BitVec 512) :
    (source_stage_expr 197) digest = r197 digest :=
  source_stage_congruence 197 digest

theorem op_198 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 198) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_198 (digest : BitVec 512) :
    (source_stage_expr 198) digest = r198 digest :=
  source_stage_congruence 198 digest

theorem op_199 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 199) digest a b = LLVM.ashr a b := rfl

theorem align_199 (digest : BitVec 512) :
    (source_stage_expr 199) digest = r199 digest :=
  source_stage_congruence 199 digest

theorem op_200 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 200) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_200 (digest : BitVec 512) :
    (source_stage_expr 200) digest = r200 digest :=
  source_stage_congruence 200 digest

theorem op_201 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 201) digest a b = LLVM.and a b := rfl

theorem align_201 (digest : BitVec 512) :
    (source_stage_expr 201) digest = r201 digest :=
  source_stage_congruence 201 digest

theorem op_202 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 202) digest a b = LLVM.sub a b { nsw := true, nuw := false } := rfl

theorem align_202 (digest : BitVec 512) :
    (source_stage_expr 202) digest = r202 digest :=
  source_stage_congruence 202 digest

theorem op_203 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 203) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_203 (digest : BitVec 512) :
    (source_stage_expr 203) digest = r203 digest :=
  source_stage_congruence 203 digest

theorem op_204 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 204) digest a b = LLVM.ashr a b := rfl

theorem align_204 (digest : BitVec 512) :
    (source_stage_expr 204) digest = r204 digest :=
  source_stage_congruence 204 digest

theorem op_205 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 205) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_205 (digest : BitVec 512) :
    (source_stage_expr 205) digest = r205 digest :=
  source_stage_congruence 205 digest

theorem op_206 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 206) digest a b = LLVM.and a b := rfl

theorem align_206 (digest : BitVec 512) :
    (source_stage_expr 206) digest = r206 digest :=
  source_stage_congruence 206 digest

theorem op_207 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 207) digest a b = LLVM.sub a b { nsw := true, nuw := false } := rfl

theorem align_207 (digest : BitVec 512) :
    (source_stage_expr 207) digest = r207 digest :=
  source_stage_congruence 207 digest

theorem op_208 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 208) digest a b = LLVM.add a b { nsw := true, nuw := true } := rfl

theorem align_208 (digest : BitVec 512) :
    (source_stage_expr 208) digest = r208 digest :=
  source_stage_congruence 208 digest

theorem op_209 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 209) digest a b = LLVM.lshr a b := rfl

theorem align_209 (digest : BitVec 512) :
    (source_stage_expr 209) digest = r209 digest :=
  source_stage_congruence 209 digest

theorem op_210 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 210) digest a b = LLVM.and a b := rfl

theorem align_210 (digest : BitVec 512) :
    (source_stage_expr 210) digest = r210 digest :=
  source_stage_congruence 210 digest

theorem op_211 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 211) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_211 (digest : BitVec 512) :
    (source_stage_expr 211) digest = r211 digest :=
  source_stage_congruence 211 digest

theorem op_212 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 212) digest a b = LLVM.ashr a b := rfl

theorem align_212 (digest : BitVec 512) :
    (source_stage_expr 212) digest = r212 digest :=
  source_stage_congruence 212 digest

theorem op_213 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 213) digest a b = LLVM.and a b := rfl

theorem align_213 (digest : BitVec 512) :
    (source_stage_expr 213) digest = r213 digest :=
  source_stage_congruence 213 digest

theorem op_214 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 214) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_214 (digest : BitVec 512) :
    (source_stage_expr 214) digest = r214 digest :=
  source_stage_congruence 214 digest

theorem op_215 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 215) digest a b = LLVM.ashr a b := rfl

theorem align_215 (digest : BitVec 512) :
    (source_stage_expr 215) digest = r215 digest :=
  source_stage_congruence 215 digest

theorem op_216 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 216) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_216 (digest : BitVec 512) :
    (source_stage_expr 216) digest = r216 digest :=
  source_stage_congruence 216 digest

theorem op_217 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 217) digest a b = LLVM.and a b := rfl

theorem align_217 (digest : BitVec 512) :
    (source_stage_expr 217) digest = r217 digest :=
  source_stage_congruence 217 digest

theorem op_218 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 218) digest a b = LLVM.sub a b { nsw := true, nuw := false } := rfl

theorem align_218 (digest : BitVec 512) :
    (source_stage_expr 218) digest = r218 digest :=
  source_stage_congruence 218 digest

theorem op_219 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 219) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_219 (digest : BitVec 512) :
    (source_stage_expr 219) digest = r219 digest :=
  source_stage_congruence 219 digest

theorem op_220 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 220) digest a b = LLVM.ashr a b := rfl

theorem align_220 (digest : BitVec 512) :
    (source_stage_expr 220) digest = r220 digest :=
  source_stage_congruence 220 digest

theorem op_221 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 221) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_221 (digest : BitVec 512) :
    (source_stage_expr 221) digest = r221 digest :=
  source_stage_congruence 221 digest

theorem op_222 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 222) digest a b = LLVM.and a b := rfl

theorem align_222 (digest : BitVec 512) :
    (source_stage_expr 222) digest = r222 digest :=
  source_stage_congruence 222 digest

theorem op_223 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 223) digest a b = LLVM.sub a b { nsw := true, nuw := false } := rfl

theorem align_223 (digest : BitVec 512) :
    (source_stage_expr 223) digest = r223 digest :=
  source_stage_congruence 223 digest

theorem op_224 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 224) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_224 (digest : BitVec 512) :
    (source_stage_expr 224) digest = r224 digest :=
  source_stage_congruence 224 digest

theorem op_225 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 225) digest a b = LLVM.ashr a b := rfl

theorem align_225 (digest : BitVec 512) :
    (source_stage_expr 225) digest = r225 digest :=
  source_stage_congruence 225 digest

theorem op_226 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 226) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_226 (digest : BitVec 512) :
    (source_stage_expr 226) digest = r226 digest :=
  source_stage_congruence 226 digest

theorem op_227 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 227) digest a b = LLVM.and a b := rfl

theorem align_227 (digest : BitVec 512) :
    (source_stage_expr 227) digest = r227 digest :=
  source_stage_congruence 227 digest

theorem op_228 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 228) digest a b = LLVM.sub a b { nsw := true, nuw := false } := rfl

theorem align_228 (digest : BitVec 512) :
    (source_stage_expr 228) digest = r228 digest :=
  source_stage_congruence 228 digest

end Firedancer.Common.ScalarArithmetic.Registers
