import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.SourceAlignment2

namespace Firedancer.Common.ScalarArithmetic.Registers
open InstCombine (LLVM)

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem op_229 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 229) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_229 (digest : BitVec 512) :
    (source_stage_expr 229) digest = r229 digest :=
  source_stage_congruence 229 digest

theorem op_230 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 230) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_230 (digest : BitVec 512) :
    (source_stage_expr 230) digest = r230 digest :=
  source_stage_congruence 230 digest

theorem op_231 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 231) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_231 (digest : BitVec 512) :
    (source_stage_expr 231) digest = r231 digest :=
  source_stage_congruence 231 digest

theorem op_232 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 232) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_232 (digest : BitVec 512) :
    (source_stage_expr 232) digest = r232 digest :=
  source_stage_congruence 232 digest

theorem op_233 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 233) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_233 (digest : BitVec 512) :
    (source_stage_expr 233) digest = r233 digest :=
  source_stage_congruence 233 digest

theorem op_234 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 234) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_234 (digest : BitVec 512) :
    (source_stage_expr 234) digest = r234 digest :=
  source_stage_congruence 234 digest

theorem op_235 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 235) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_235 (digest : BitVec 512) :
    (source_stage_expr 235) digest = r235 digest :=
  source_stage_congruence 235 digest

theorem op_236 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 236) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_236 (digest : BitVec 512) :
    (source_stage_expr 236) digest = r236 digest :=
  source_stage_congruence 236 digest

theorem op_237 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 237) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_237 (digest : BitVec 512) :
    (source_stage_expr 237) digest = r237 digest :=
  source_stage_congruence 237 digest

theorem op_238 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 238) digest a b = LLVM.sub a b { nsw := false, nuw := false } := rfl

theorem align_238 (digest : BitVec 512) :
    (source_stage_expr 238) digest = r238 digest :=
  source_stage_congruence 238 digest

theorem op_239 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 239) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_239 (digest : BitVec 512) :
    (source_stage_expr 239) digest = r239 digest :=
  source_stage_congruence 239 digest

theorem op_240 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 240) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_240 (digest : BitVec 512) :
    (source_stage_expr 240) digest = r240 digest :=
  source_stage_congruence 240 digest

theorem op_241 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 241) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_241 (digest : BitVec 512) :
    (source_stage_expr 241) digest = r241 digest :=
  source_stage_congruence 241 digest

theorem op_242 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 242) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_242 (digest : BitVec 512) :
    (source_stage_expr 242) digest = r242 digest :=
  source_stage_congruence 242 digest

theorem op_243 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 243) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_243 (digest : BitVec 512) :
    (source_stage_expr 243) digest = r243 digest :=
  source_stage_congruence 243 digest

theorem op_244 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 244) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_244 (digest : BitVec 512) :
    (source_stage_expr 244) digest = r244 digest :=
  source_stage_congruence 244 digest

theorem op_245 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 245) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_245 (digest : BitVec 512) :
    (source_stage_expr 245) digest = r245 digest :=
  source_stage_congruence 245 digest

theorem op_246 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 246) digest a b = LLVM.mul a b { nsw := false, nuw := false } := rfl

theorem align_246 (digest : BitVec 512) :
    (source_stage_expr 246) digest = r246 digest :=
  source_stage_congruence 246 digest

theorem op_247 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 247) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_247 (digest : BitVec 512) :
    (source_stage_expr 247) digest = r247 digest :=
  source_stage_congruence 247 digest

theorem op_248 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 248) digest a b = LLVM.mul a b { nsw := false, nuw := false } := rfl

theorem align_248 (digest : BitVec 512) :
    (source_stage_expr 248) digest = r248 digest :=
  source_stage_congruence 248 digest

theorem op_249 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 249) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_249 (digest : BitVec 512) :
    (source_stage_expr 249) digest = r249 digest :=
  source_stage_congruence 249 digest

theorem op_250 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 250) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_250 (digest : BitVec 512) :
    (source_stage_expr 250) digest = r250 digest :=
  source_stage_congruence 250 digest

theorem op_251 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 251) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_251 (digest : BitVec 512) :
    (source_stage_expr 251) digest = r251 digest :=
  source_stage_congruence 251 digest

theorem op_252 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 252) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_252 (digest : BitVec 512) :
    (source_stage_expr 252) digest = r252 digest :=
  source_stage_congruence 252 digest

theorem op_253 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 253) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_253 (digest : BitVec 512) :
    (source_stage_expr 253) digest = r253 digest :=
  source_stage_congruence 253 digest

theorem op_254 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 254) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_254 (digest : BitVec 512) :
    (source_stage_expr 254) digest = r254 digest :=
  source_stage_congruence 254 digest

theorem op_255 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 255) digest a b = LLVM.mul a b { nsw := false, nuw := false } := rfl

theorem align_255 (digest : BitVec 512) :
    (source_stage_expr 255) digest = r255 digest :=
  source_stage_congruence 255 digest

theorem op_256 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 256) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_256 (digest : BitVec 512) :
    (source_stage_expr 256) digest = r256 digest :=
  source_stage_congruence 256 digest

theorem op_257 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 257) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_257 (digest : BitVec 512) :
    (source_stage_expr 257) digest = r257 digest :=
  source_stage_congruence 257 digest

theorem op_258 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 258) digest a b = LLVM.mul a b { nsw := false, nuw := false } := rfl

theorem align_258 (digest : BitVec 512) :
    (source_stage_expr 258) digest = r258 digest :=
  source_stage_congruence 258 digest

theorem op_259 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 259) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_259 (digest : BitVec 512) :
    (source_stage_expr 259) digest = r259 digest :=
  source_stage_congruence 259 digest

theorem op_260 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 260) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_260 (digest : BitVec 512) :
    (source_stage_expr 260) digest = r260 digest :=
  source_stage_congruence 260 digest

theorem op_261 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 261) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_261 (digest : BitVec 512) :
    (source_stage_expr 261) digest = r261 digest :=
  source_stage_congruence 261 digest

theorem op_262 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 262) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_262 (digest : BitVec 512) :
    (source_stage_expr 262) digest = r262 digest :=
  source_stage_congruence 262 digest

theorem op_263 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 263) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_263 (digest : BitVec 512) :
    (source_stage_expr 263) digest = r263 digest :=
  source_stage_congruence 263 digest

theorem op_264 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 264) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_264 (digest : BitVec 512) :
    (source_stage_expr 264) digest = r264 digest :=
  source_stage_congruence 264 digest

theorem op_265 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 265) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_265 (digest : BitVec 512) :
    (source_stage_expr 265) digest = r265 digest :=
  source_stage_congruence 265 digest

theorem op_266 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 266) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_266 (digest : BitVec 512) :
    (source_stage_expr 266) digest = r266 digest :=
  source_stage_congruence 266 digest

theorem op_267 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 267) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_267 (digest : BitVec 512) :
    (source_stage_expr 267) digest = r267 digest :=
  source_stage_congruence 267 digest

theorem op_268 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 268) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_268 (digest : BitVec 512) :
    (source_stage_expr 268) digest = r268 digest :=
  source_stage_congruence 268 digest

theorem op_269 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 269) digest a b = LLVM.mul a b { nsw := false, nuw := false } := rfl

theorem align_269 (digest : BitVec 512) :
    (source_stage_expr 269) digest = r269 digest :=
  source_stage_congruence 269 digest

theorem op_270 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 270) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_270 (digest : BitVec 512) :
    (source_stage_expr 270) digest = r270 digest :=
  source_stage_congruence 270 digest

theorem op_271 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 271) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_271 (digest : BitVec 512) :
    (source_stage_expr 271) digest = r271 digest :=
  source_stage_congruence 271 digest

theorem op_272 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 272) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_272 (digest : BitVec 512) :
    (source_stage_expr 272) digest = r272 digest :=
  source_stage_congruence 272 digest

theorem op_273 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 273) digest a b = LLVM.mul a b { nsw := false, nuw := false } := rfl

theorem align_273 (digest : BitVec 512) :
    (source_stage_expr 273) digest = r273 digest :=
  source_stage_congruence 273 digest

theorem op_274 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 274) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_274 (digest : BitVec 512) :
    (source_stage_expr 274) digest = r274 digest :=
  source_stage_congruence 274 digest

theorem op_275 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 275) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_275 (digest : BitVec 512) :
    (source_stage_expr 275) digest = r275 digest :=
  source_stage_congruence 275 digest

theorem op_276 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 276) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_276 (digest : BitVec 512) :
    (source_stage_expr 276) digest = r276 digest :=
  source_stage_congruence 276 digest

theorem op_277 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 277) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_277 (digest : BitVec 512) :
    (source_stage_expr 277) digest = r277 digest :=
  source_stage_congruence 277 digest

theorem op_278 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 278) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_278 (digest : BitVec 512) :
    (source_stage_expr 278) digest = r278 digest :=
  source_stage_congruence 278 digest

theorem op_279 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 279) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_279 (digest : BitVec 512) :
    (source_stage_expr 279) digest = r279 digest :=
  source_stage_congruence 279 digest

theorem op_280 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 280) digest a b = LLVM.mul a b { nsw := false, nuw := false } := rfl

theorem align_280 (digest : BitVec 512) :
    (source_stage_expr 280) digest = r280 digest :=
  source_stage_congruence 280 digest

theorem op_281 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 281) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_281 (digest : BitVec 512) :
    (source_stage_expr 281) digest = r281 digest :=
  source_stage_congruence 281 digest

theorem op_282 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 282) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_282 (digest : BitVec 512) :
    (source_stage_expr 282) digest = r282 digest :=
  source_stage_congruence 282 digest

theorem op_283 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 283) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_283 (digest : BitVec 512) :
    (source_stage_expr 283) digest = r283 digest :=
  source_stage_congruence 283 digest

theorem op_284 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 284) digest a b = LLVM.mul a b { nsw := false, nuw := false } := rfl

theorem align_284 (digest : BitVec 512) :
    (source_stage_expr 284) digest = r284 digest :=
  source_stage_congruence 284 digest

theorem op_285 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 285) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_285 (digest : BitVec 512) :
    (source_stage_expr 285) digest = r285 digest :=
  source_stage_congruence 285 digest

theorem op_286 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 286) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_286 (digest : BitVec 512) :
    (source_stage_expr 286) digest = r286 digest :=
  source_stage_congruence 286 digest

theorem op_287 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 287) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_287 (digest : BitVec 512) :
    (source_stage_expr 287) digest = r287 digest :=
  source_stage_congruence 287 digest

theorem op_288 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 288) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_288 (digest : BitVec 512) :
    (source_stage_expr 288) digest = r288 digest :=
  source_stage_congruence 288 digest

theorem op_289 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 289) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_289 (digest : BitVec 512) :
    (source_stage_expr 289) digest = r289 digest :=
  source_stage_congruence 289 digest

theorem op_290 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 290) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_290 (digest : BitVec 512) :
    (source_stage_expr 290) digest = r290 digest :=
  source_stage_congruence 290 digest

theorem op_291 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 291) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_291 (digest : BitVec 512) :
    (source_stage_expr 291) digest = r291 digest :=
  source_stage_congruence 291 digest

theorem op_292 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 292) digest a b = LLVM.mul a b { nsw := false, nuw := false } := rfl

theorem align_292 (digest : BitVec 512) :
    (source_stage_expr 292) digest = r292 digest :=
  source_stage_congruence 292 digest

theorem op_293 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 293) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_293 (digest : BitVec 512) :
    (source_stage_expr 293) digest = r293 digest :=
  source_stage_congruence 293 digest

theorem op_294 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 294) digest a b = LLVM.mul a b { nsw := true, nuw := false } := rfl

theorem align_294 (digest : BitVec 512) :
    (source_stage_expr 294) digest = r294 digest :=
  source_stage_congruence 294 digest

theorem op_295 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 295) digest a b = LLVM.add a b { nsw := true, nuw := false } := rfl

theorem align_295 (digest : BitVec 512) :
    (source_stage_expr 295) digest = r295 digest :=
  source_stage_congruence 295 digest

theorem op_296 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 296) digest a b = LLVM.mul a b { nsw := false, nuw := false } := rfl

theorem align_296 (digest : BitVec 512) :
    (source_stage_expr 296) digest = r296 digest :=
  source_stage_congruence 296 digest

theorem op_297 (digest : BitVec 512) (a b : LLVM.IntW 64) :
    (source_step_expr 297) digest a b = LLVM.add a b { nsw := false, nuw := false } := rfl

theorem align_297 (digest : BitVec 512) :
    (source_stage_expr 297) digest = r297 digest :=
  source_stage_congruence 297 digest

end Firedancer.Common.ScalarArithmetic.Registers
