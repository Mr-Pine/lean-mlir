import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.IntegerConservation1

/-! Source-aligned exact integer identities. Carry masks and remainders are
related to their numbered quotient registers before ring normalization. -/

namespace Firedancer.Common.ScalarArithmetic.IntegerRegisters

set_option maxHeartbeats 2000000

attribute [local irreducible] z61 z63 z65 z67 z69 z71 z73 z75 z77 z79 z81 z83 z85 z87 z89 z91 z93 z95 z97 z99 z101 z103 z105 z106 z107 z108 z109 z110 z111 z112 z113 z114 z115 z116 z117 z118 z119 z120 z121 z122 z123 z124 z125 z126 z127 z128 z129 z130 z131 z132 z133 z134 z135 z136 z137 z138 z139 z140 z141 z142 z143 z144 z145 z146 z147 z148 z149 z150 z151 z152 z153 z154 z155 z156 z157 z158 z159 z160 z161 z162 z163 z164 z165 z166 z167 z168 z169 z170 z171 z172 z173 z174 z175 z176 z177 z178 z179 z180 z181 z182 z183 z184 z185 z186 z187 z188 z189 z190 z191 z192 z193 z194 z195 z196 z197 z198 z199 z200 z201 z202 z203 z204 z205 z206 z207 z208 z209 z210 z211 z212 z213 z214 z215 z216 z217 z218 z219 z220 z221 z222 z223 z224 z225 z226 z227 z228 z229 z230 z231 z232 z233 z234 z235 z236 z237 z238 z239 z240 z241 z242 z243 z244 z245 z246 z247 z248 z249 z250 z251 z252 z253 z254 z255 z256 z257 z258 z259 z260 z261 z262 z263 z264 z265 z266 z267 z268 z269 z270 z271 z272 z273 z274 z275 z276 z277 z278 z279 z280 z281 z282 z283 z284 z285 z286 z287 z288 z289 z290 z291 z292 z293 z294 z295 z296 z297 z298 z299 z300 z301 z302 z303 z304 z305 z306 z307 z308 z309 z310 z311 z312 z313 z314 z315 z316 z317 z318 z319 z320 z321 z322 z323 z324 z325 z326 z327 z328 z329 z330 z331 z332 z333 z334 z335 z336 z337 z338 z339 z340 z341 z342 z343 z344 z345 z346 z347 z348 z349 z350 z351 z352 z353 z354 z355 z356 z357 z358 z359 z360 z361 z362 z363 z364 z365 z366 z367 z368 z369 z370 z371 z372 z373 z374 z375 z376 z377 z378 z379 z380 z381 z382 z383 z384 z385 z386 z387 z388 z389 z390 z391 z392 z393 z394 z395 z396 z397 z398 z399 z400 z401 z402 z403 z404 z405 z406 z407 z408 z409 z410 z411 z412 z413 z414 z415 z416 z417 z418 z419 z420 z421 z422 z423 z424 z425 z426 z427 z428 z429 z430 z431 z432 z433 z434 z435 z436 z437 z438 z439 z440 z441 z442 z443 z444 z445 z446 m170 m179 m189 m196 m201 m206 m210 m213 m217 m222 m227 m301 m306 m311 m321 m329 m334 m338 m341 m345 m349 m354 m358

theorem z229_conservation (d : Digits) : z229 d = (666643) * (d 17) + (666643) * (z204 d) := by
  simp only [z229, z205_conservation] <;> ring

theorem z230_conservation (d : Digits) : z230 d = (666643) * (d 17) + (d 5) + (666643) * (z204 d) := by
  simp only [z230, z229_conservation, z71_linear] <;> ring

theorem z231_conservation (d : Digits) : z231 d = (470296) * (d 17) + (470296) * (z204 d) := by
  simp only [z231, z205_conservation] <;> ring

theorem z232_conservation (d : Digits) : z232 d = (470296) * (d 17) + (666643) * (d 18) + (d 6) + (-2097152) * (z168 d) + (470296) * (z204 d) := by
  simp only [z232, z171_conservation, z231_conservation] <;> ring

theorem z233_conservation (d : Digits) : z233 d = (654183) * (d 17) + (654183) * (z204 d) := by
  simp only [z233, z205_conservation] <;> ring

theorem z234_conservation (d : Digits) : z234 d = (-997805) * (d 17) + (-997805) * (z204 d) := by
  simp only [z234, z205_conservation] <;> ring

theorem z235_conservation (d : Digits) : z235 d = (136657) * (d 17) + (136657) * (z204 d) := by
  simp only [z235, z205_conservation] <;> ring

theorem z236_conservation (d : Digits) : z236 d = (-683901) * (d 17) + (-683901) * (z204 d) := by
  simp only [z236, z205_conservation] <;> ring

theorem z237_conservation (d : Digits) : z237 d = (d 10) + (-683901) * (d 17) + (136657) * (d 18) + (-997805) * (d 19) + (654183) * (d 20) + (470296) * (d 21) + (666643) * (d 22) + (-683901) * (z204 d) := by
  simp only [z237, z165_conservation, z236_conservation] <;> ring

theorem z238_conservation (d : Digits) : z238 d = (d 10) + (-683901) * (d 17) + (136657) * (d 18) + (-997805) * (d 19) + (654183) * (d 20) + (470296) * (d 21) + (666643) * (d 22) + (-2097152) * (z182 d) + (-683901) * (z204 d) := by
  simp only [z238, z237_conservation, z189_conservation] <;> ring

theorem z239_conservation (d : Digits) : z239 d = (d 10) + (-683901) * (d 17) + (136657) * (d 18) + (-997805) * (d 19) + (654183) * (d 20) + (470296) * (d 21) + (666643) * (d 22) + (-2097152) * (z182 d) + (-683901) * (z204 d) + (z212 d) := by
  simp only [z239, z238_conservation] <;> ring

theorem z240_conservation (d : Digits) : z240 d = (666643) * (d 16) + (-455917814343) * (d 23) + (-1398051700736) * (z204 d) + (666643) * (z225 d) := by
  simp only [z240, z226_conservation] <;> ring

theorem z241_conservation (d : Digits) : z241 d = (666643) * (d 16) + (-455917814343) * (d 23) + (d 4) + (-1398051700736) * (z204 d) + (666643) * (z225 d) := by
  simp only [z241, z240_conservation, z69_linear] <;> ring

theorem z242_conservation (d : Digits) : z242 d = (470296) * (d 16) + (-321635904696) * (d 23) + (-986282196992) * (z204 d) + (470296) * (z225 d) := by
  simp only [z242, z226_conservation] <;> ring

theorem z243_conservation (d : Digits) : z243 d = (470296) * (d 16) + (666643) * (d 17) + (-321635904696) * (d 23) + (d 5) + (-986281530349) * (z204 d) + (470296) * (z225 d) := by
  simp only [z243, z230_conservation, z242_conservation] <;> ring

theorem z244_conservation (d : Digits) : z244 d = (654183) * (d 16) + (-447396407883) * (d 23) + (-1371921186816) * (z204 d) + (654183) * (z225 d) := by
  simp only [z244, z226_conservation] <;> ring

theorem z245_conservation (d : Digits) : z245 d = (654183) * (d 16) + (470296) * (d 17) + (666643) * (d 18) + (-447396407883) * (d 23) + (d 6) + (-2097152) * (z168 d) + (-1371920716520) * (z204 d) + (654183) * (z225 d) := by
  simp only [z245, z232_conservation, z244_conservation] <;> ring

theorem z246_conservation (d : Digits) : z246 d = (-997805) * (d 16) + (682399837305) * (d 23) + (2092548751360) * (z204 d) + (-997805) * (z225 d) := by
  simp only [z246, z226_conservation] <;> ring

theorem z247_conservation (d : Digits) : z247 d = (136657) * (d 16) + (-93459858957) * (d 23) + (-286590500864) * (z204 d) + (136657) * (z225 d) := by
  simp only [z247, z226_conservation] <;> ring

theorem z248_conservation (d : Digits) : z248 d = (-683901) * (d 16) + (467720577801) * (d 23) + (1434244349952) * (z204 d) + (-683901) * (z225 d) := by
  simp only [z248, z226_conservation] <;> ring

theorem z249_conservation (d : Digits) : z249 d = (666643) * (d 15) + (-455917814343) * (d 22) + (91101432451) * (d 23) + (666643) * (z199 d) + (-1398051700736) * (z225 d) := by
  simp only [z249, z228_conservation] <;> ring

theorem z250_conservation (d : Digits) : z250 d = (666643) * (d 15) + (-455917814343) * (d 22) + (91101432451) * (d 23) + (d 3) + (666643) * (z199 d) + (-1398051700736) * (z225 d) := by
  simp only [z250, z249_conservation, z67_linear] <;> ring

theorem z251_conservation (d : Digits) : z251 d = (470296) * (d 15) + (-321635904696) * (d 22) + (64269240472) * (d 23) + (470296) * (z199 d) + (-986282196992) * (z225 d) := by
  simp only [z251, z228_conservation] <;> ring

theorem z252_conservation (d : Digits) : z252 d = (470296) * (d 15) + (666643) * (d 16) + (-321635904696) * (d 22) + (-391648573871) * (d 23) + (d 4) + (470296) * (z199 d) + (-1398051700736) * (z204 d) + (-986281530349) * (z225 d) := by
  simp only [z252, z241_conservation, z251_conservation] <;> ring

theorem z253_conservation (d : Digits) : z253 d = (654183) * (d 15) + (-447396407883) * (d 22) + (89398686231) * (d 23) + (654183) * (z199 d) + (-1371921186816) * (z225 d) := by
  simp only [z253, z228_conservation] <;> ring

theorem z254_conservation (d : Digits) : z254 d = (654183) * (d 15) + (470296) * (d 16) + (666643) * (d 17) + (-447396407883) * (d 22) + (-232237218465) * (d 23) + (d 5) + (654183) * (z199 d) + (-986281530349) * (z204 d) + (-1371920716520) * (z225 d) := by
  simp only [z254, z243_conservation, z253_conservation] <;> ring

theorem z255_conservation (d : Digits) : z255 d = (-997805) * (d 15) + (682399837305) * (d 22) + (-136357037885) * (d 23) + (-997805) * (z199 d) + (2092548751360) * (z225 d) := by
  simp only [z255, z228_conservation] <;> ring

theorem z256_conservation (d : Digits) : z256 d = (-997805) * (d 15) + (654183) * (d 16) + (470296) * (d 17) + (666643) * (d 18) + (682399837305) * (d 22) + (-583753445768) * (d 23) + (d 6) + (-2097152) * (z168 d) + (-997805) * (z199 d) + (-1371920716520) * (z204 d) + (2092549405543) * (z225 d) := by
  simp only [z256, z245_conservation, z255_conservation] <;> ring

theorem z257_conservation (d : Digits) : z257 d = (136657) * (d 15) + (-93459858957) * (d 22) + (18675135649) * (d 23) + (136657) * (z199 d) + (-286590500864) * (z225 d) := by
  simp only [z257, z228_conservation] <;> ring

theorem z258_conservation (d : Digits) : z258 d = (-683901) * (d 15) + (467720577801) * (d 22) + (-93459858957) * (d 23) + (-683901) * (z199 d) + (1434244349952) * (z225 d) := by
  simp only [z258, z228_conservation] <;> ring

theorem z259_conservation (d : Digits) : z259 d = (-997805) * (d 17) + (654183) * (d 18) + (470296) * (d 19) + (666643) * (d 20) + (d 8) + (-2097152) * (z173 d) + (-997805) * (z204 d) := by
  simp only [z259, z180_conservation, z234_conservation] <;> ring

theorem z260_conservation (d : Digits) : z260 d = (-997805) * (d 17) + (654183) * (d 18) + (470296) * (d 19) + (666643) * (d 20) + (d 8) + (-2097152) * (z173 d) + (-997805) * (z204 d) + (z209 d) := by
  simp only [z260, z259_conservation] <;> ring

theorem z261_conservation (d : Digits) : z261 d = (136657) * (d 16) + (-997805) * (d 17) + (654183) * (d 18) + (470296) * (d 19) + (666643) * (d 20) + (-93459858957) * (d 23) + (d 8) + (-2097152) * (z173 d) + (-286591498669) * (z204 d) + (z209 d) + (136657) * (z225 d) := by
  simp only [z261, z260_conservation, z247_conservation] <;> ring

theorem z262_conservation (d : Digits) : z262 d = (-683901) * (d 15) + (136657) * (d 16) + (-997805) * (d 17) + (654183) * (d 18) + (470296) * (d 19) + (666643) * (d 20) + (467720577801) * (d 22) + (-186919717914) * (d 23) + (d 8) + (-2097152) * (z173 d) + (-683901) * (z199 d) + (-286591498669) * (z204 d) + (z209 d) + (1434244486609) * (z225 d) := by
  simp only [z262, z261_conservation, z258_conservation] <;> ring

theorem z263_conservation (d : Digits) : z263 d = (666643) * (d 14) + (-455917814343) * (d 21) + (91101432451) * (d 22) + (-665179718615) * (d 23) + (-1398051700736) * (z199 d) + (666643) * (z220 d) := by
  simp only [z263, z221_conservation] <;> ring

theorem z264_conservation (d : Digits) : z264 d = (666643) * (d 14) + (d 2) + (-455917814343) * (d 21) + (91101432451) * (d 22) + (-665179718615) * (d 23) + (-1398051700736) * (z199 d) + (666643) * (z220 d) := by
  simp only [z264, z263_conservation, z65_linear] <;> ring

theorem z265_conservation (d : Digits) : z265 d = (470296) * (d 14) + (-321635904696) * (d 21) + (64269240472) * (d 22) + (-469263700280) * (d 23) + (-986282196992) * (z199 d) + (470296) * (z220 d) := by
  simp only [z265, z221_conservation] <;> ring

theorem z266_conservation (d : Digits) : z266 d = (470296) * (d 14) + (666643) * (d 15) + (-321635904696) * (d 21) + (-391648573871) * (d 22) + (-378162267829) * (d 23) + (d 3) + (-986281530349) * (z199 d) + (470296) * (z220 d) + (-1398051700736) * (z225 d) := by
  simp only [z266, z250_conservation, z265_conservation] <;> ring

theorem z267_conservation (d : Digits) : z267 d = (654183) * (d 14) + (-447396407883) * (d 21) + (89398686231) * (d 22) + (-652747068315) * (d 23) + (-1371921186816) * (z199 d) + (654183) * (z220 d) := by
  simp only [z267, z221_conservation] <;> ring

theorem z268_conservation (d : Digits) : z268 d = (654183) * (d 14) + (470296) * (d 15) + (666643) * (d 16) + (-447396407883) * (d 21) + (-232237218465) * (d 22) + (-1044395642186) * (d 23) + (d 4) + (-1371920716520) * (z199 d) + (-1398051700736) * (z204 d) + (654183) * (z220 d) + (-986281530349) * (z225 d) := by
  simp only [z268, z252_conservation, z267_conservation] <;> ring

theorem z269_conservation (d : Digits) : z269 d = (-997805) * (d 14) + (682399837305) * (d 21) + (-136357037885) * (d 22) + (995614818025) * (d 23) + (2092548751360) * (z199 d) + (-997805) * (z220 d) := by
  simp only [z269, z221_conservation] <;> ring

theorem z270_conservation (d : Digits) : z270 d = (-997805) * (d 14) + (654183) * (d 15) + (470296) * (d 16) + (666643) * (d 17) + (682399837305) * (d 21) + (-583753445768) * (d 22) + (763377599560) * (d 23) + (d 5) + (2092549405543) * (z199 d) + (-986281530349) * (z204 d) + (-997805) * (z220 d) + (-1371920716520) * (z225 d) := by
  simp only [z270, z254_conservation, z269_conservation] <;> ring

theorem z271_conservation (d : Digits) : z271 d = (136657) * (d 14) + (-93459858957) * (d 21) + (18675135649) * (d 22) + (-136357037885) * (d 23) + (-286590500864) * (z199 d) + (136657) * (z220 d) := by
  simp only [z271, z221_conservation] <;> ring

theorem z272_conservation (d : Digits) : z272 d = (136657) * (d 14) + (-997805) * (d 15) + (654183) * (d 16) + (470296) * (d 17) + (666643) * (d 18) + (-93459858957) * (d 21) + (701074972954) * (d 22) + (-720110483653) * (d 23) + (d 6) + (-2097152) * (z168 d) + (-286591498669) * (z199 d) + (-1371920716520) * (z204 d) + (136657) * (z220 d) + (2092549405543) * (z225 d) := by
  simp only [z272, z256_conservation, z271_conservation] <;> ring

theorem z273_conservation (d : Digits) : z273 d = (-683901) * (d 14) + (467720577801) * (d 21) + (-93459858957) * (d 22) + (682399837305) * (d 23) + (1434244349952) * (z199 d) + (-683901) * (z220 d) := by
  simp only [z273, z221_conservation] <;> ring

theorem z274_conservation (d : Digits) : z274 d = (666643) * (d 13) + (-455917814343) * (d 20) + (91101432451) * (d 21) + (-665179718615) * (d 22) + (436106517669) * (d 23) + (666643) * (z191 d) + (-1398051700736) * (z220 d) := by
  simp only [z274, z223_conservation] <;> ring

theorem z275_conservation (d : Digits) : z275 d = (d 1) + (666643) * (d 13) + (-455917814343) * (d 20) + (91101432451) * (d 21) + (-665179718615) * (d 22) + (436106517669) * (d 23) + (666643) * (z191 d) + (-1398051700736) * (z220 d) := by
  simp only [z275, z274_conservation, z63_linear] <;> ring

theorem z276_conservation (d : Digits) : z276 d = (470296) * (d 13) + (-321635904696) * (d 20) + (64269240472) * (d 21) + (-469263700280) * (d 22) + (307659648168) * (d 23) + (470296) * (z191 d) + (-986282196992) * (z220 d) := by
  simp only [z276, z223_conservation] <;> ring

theorem z277_conservation (d : Digits) : z277 d = (470296) * (d 13) + (666643) * (d 14) + (d 2) + (-321635904696) * (d 20) + (-391648573871) * (d 21) + (-378162267829) * (d 22) + (-357520070447) * (d 23) + (470296) * (z191 d) + (-1398051700736) * (z199 d) + (-986281530349) * (z220 d) := by
  simp only [z277, z264_conservation, z276_conservation] <;> ring

theorem z278_conservation (d : Digits) : z278 d = (654183) * (d 13) + (-447396407883) * (d 20) + (89398686231) * (d 21) + (-652747068315) * (d 22) + (427955397489) * (d 23) + (654183) * (z191 d) + (-1371921186816) * (z220 d) := by
  simp only [z278, z223_conservation] <;> ring

theorem z279_conservation (d : Digits) : z279 d = (654183) * (d 13) + (470296) * (d 14) + (666643) * (d 15) + (-447396407883) * (d 20) + (-232237218465) * (d 21) + (-1044395642186) * (d 22) + (49793129660) * (d 23) + (d 3) + (654183) * (z191 d) + (-986281530349) * (z199 d) + (-1371920716520) * (z220 d) + (-1398051700736) * (z225 d) := by
  simp only [z279, z266_conservation, z278_conservation] <;> ring

theorem z280_conservation (d : Digits) : z280 d = (-997805) * (d 13) + (682399837305) * (d 20) + (-136357037885) * (d 21) + (995614818025) * (d 22) + (-652747068315) * (d 23) + (-997805) * (z191 d) + (2092548751360) * (z220 d) := by
  simp only [z280, z223_conservation] <;> ring

theorem z281_conservation (d : Digits) : z281 d = (-997805) * (d 13) + (654183) * (d 14) + (470296) * (d 15) + (666643) * (d 16) + (682399837305) * (d 20) + (-583753445768) * (d 21) + (763377599560) * (d 22) + (-1697142710501) * (d 23) + (d 4) + (-997805) * (z191 d) + (-1371920716520) * (z199 d) + (-1398051700736) * (z204 d) + (2092549405543) * (z220 d) + (-986281530349) * (z225 d) := by
  simp only [z281, z268_conservation, z280_conservation] <;> ring

theorem z282_conservation (d : Digits) : z282 d = (136657) * (d 13) + (-93459858957) * (d 20) + (18675135649) * (d 21) + (-136357037885) * (d 22) + (89398686231) * (d 23) + (136657) * (z191 d) + (-286590500864) * (z220 d) := by
  simp only [z282, z223_conservation] <;> ring

theorem z283_conservation (d : Digits) : z283 d = (136657) * (d 13) + (-997805) * (d 14) + (654183) * (d 15) + (470296) * (d 16) + (666643) * (d 17) + (-93459858957) * (d 20) + (701074972954) * (d 21) + (-720110483653) * (d 22) + (852776285791) * (d 23) + (d 5) + (136657) * (z191 d) + (2092549405543) * (z199 d) + (-986281530349) * (z204 d) + (-286591498669) * (z220 d) + (-1371920716520) * (z225 d) := by
  simp only [z283, z270_conservation, z282_conservation] <;> ring

theorem z284_conservation (d : Digits) : z284 d = (-683901) * (d 13) + (467720577801) * (d 20) + (-93459858957) * (d 21) + (682399837305) * (d 22) + (-447396407883) * (d 23) + (-683901) * (z191 d) + (1434244349952) * (z220 d) := by
  simp only [z284, z223_conservation] <;> ring

theorem z285_conservation (d : Digits) : z285 d = (-683901) * (d 13) + (136657) * (d 14) + (-997805) * (d 15) + (654183) * (d 16) + (470296) * (d 17) + (666643) * (d 18) + (467720577801) * (d 20) + (-186919717914) * (d 21) + (1383474810259) * (d 22) + (-1167506891536) * (d 23) + (d 6) + (-2097152) * (z168 d) + (-683901) * (z191 d) + (-286591498669) * (z199 d) + (-1371920716520) * (z204 d) + (1434244486609) * (z220 d) + (2092549405543) * (z225 d) := by
  simp only [z285, z272_conservation, z284_conservation] <;> ring

theorem z286_conservation (d : Digits) : z286 d = (666643) * (d 12) + (-455917814343) * (d 19) + (91101432451) * (d 20) + (-665179718615) * (d 21) + (436106517669) * (d 22) + (313519536328) * (d 23) + (-1398051700736) * (z191 d) + (666643) * (z215 d) := by
  simp only [z286, z216_conservation] <;> ring

theorem z287_conservation (d : Digits) : z287 d = (d 0) + (666643) * (d 12) + (-455917814343) * (d 19) + (91101432451) * (d 20) + (-665179718615) * (d 21) + (436106517669) * (d 22) + (313519536328) * (d 23) + (-1398051700736) * (z191 d) + (666643) * (z215 d) := by
  simp only [z287, z286_conservation, z61_linear] <;> ring

theorem z288_conservation (d : Digits) : z288 d = (470296) * (d 12) + (-321635904696) * (d 19) + (64269240472) * (d 20) + (-469263700280) * (d 21) + (307659648168) * (d 22) + (221178327616) * (d 23) + (-986282196992) * (z191 d) + (470296) * (z215 d) := by
  simp only [z288, z216_conservation] <;> ring

theorem z289_conservation (d : Digits) : z289 d = (d 1) + (470296) * (d 12) + (666643) * (d 13) + (-321635904696) * (d 19) + (-391648573871) * (d 20) + (-378162267829) * (d 21) + (-357520070447) * (d 22) + (657284845285) * (d 23) + (-986281530349) * (z191 d) + (470296) * (z215 d) + (-1398051700736) * (z220 d) := by
  simp only [z289, z275_conservation, z288_conservation] <;> ring

theorem z290_conservation (d : Digits) : z290 d = (654183) * (d 12) + (-447396407883) * (d 19) + (89398686231) * (d 20) + (-652747068315) * (d 21) + (427955397489) * (d 22) + (307659648168) * (d 23) + (-1371921186816) * (z191 d) + (654183) * (z215 d) := by
  simp only [z290, z216_conservation] <;> ring

theorem z291_conservation (d : Digits) : z291 d = (654183) * (d 12) + (470296) * (d 13) + (666643) * (d 14) + (-447396407883) * (d 19) + (d 2) + (-232237218465) * (d 20) + (-1044395642186) * (d 21) + (49793129660) * (d 22) + (-49860422279) * (d 23) + (-1371920716520) * (z191 d) + (-1398051700736) * (z199 d) + (654183) * (z215 d) + (-986281530349) * (z220 d) := by
  simp only [z291, z277_conservation, z290_conservation] <;> ring

theorem z292_conservation (d : Digits) : z292 d = (-997805) * (d 12) + (682399837305) * (d 19) + (-136357037885) * (d 20) + (995614818025) * (d 21) + (-652747068315) * (d 22) + (-469263700280) * (d 23) + (2092548751360) * (z191 d) + (-997805) * (z215 d) := by
  simp only [z292, z216_conservation] <;> ring

theorem z293_conservation (d : Digits) : z293 d = (-997805) * (d 12) + (654183) * (d 13) + (470296) * (d 14) + (666643) * (d 15) + (682399837305) * (d 19) + (-583753445768) * (d 20) + (763377599560) * (d 21) + (-1697142710501) * (d 22) + (-419470570620) * (d 23) + (d 3) + (2092549405543) * (z191 d) + (-986281530349) * (z199 d) + (-997805) * (z215 d) + (-1371920716520) * (z220 d) + (-1398051700736) * (z225 d) := by
  simp only [z293, z279_conservation, z292_conservation] <;> ring

theorem z294_conservation (d : Digits) : z294 d = (136657) * (d 12) + (-93459858957) * (d 19) + (18675135649) * (d 20) + (-136357037885) * (d 21) + (89398686231) * (d 22) + (64269240472) * (d 23) + (-286590500864) * (z191 d) + (136657) * (z215 d) := by
  simp only [z294, z216_conservation] <;> ring

theorem z295_conservation (d : Digits) : z295 d = (136657) * (d 12) + (-997805) * (d 13) + (654183) * (d 14) + (470296) * (d 15) + (666643) * (d 16) + (-93459858957) * (d 19) + (701074972954) * (d 20) + (-720110483653) * (d 21) + (852776285791) * (d 22) + (-1632873470029) * (d 23) + (d 4) + (-286591498669) * (z191 d) + (-1371920716520) * (z199 d) + (-1398051700736) * (z204 d) + (136657) * (z215 d) + (2092549405543) * (z220 d) + (-986281530349) * (z225 d) := by
  simp only [z295, z281_conservation, z294_conservation] <;> ring

theorem z296_conservation (d : Digits) : z296 d = (-683901) * (d 12) + (467720577801) * (d 19) + (-93459858957) * (d 20) + (682399837305) * (d 21) + (-447396407883) * (d 22) + (-321635904696) * (d 23) + (1434244349952) * (z191 d) + (-683901) * (z215 d) := by
  simp only [z296, z216_conservation] <;> ring

theorem z297_conservation (d : Digits) : z297 d = (-683901) * (d 12) + (136657) * (d 13) + (-997805) * (d 14) + (654183) * (d 15) + (470296) * (d 16) + (666643) * (d 17) + (467720577801) * (d 19) + (-186919717914) * (d 20) + (1383474810259) * (d 21) + (-1167506891536) * (d 22) + (531140381095) * (d 23) + (d 5) + (1434244486609) * (z191 d) + (2092549405543) * (z199 d) + (-986281530349) * (z204 d) + (-683901) * (z215 d) + (-286591498669) * (z220 d) + (-1371920716520) * (z225 d) := by
  simp only [z297, z283_conservation, z296_conservation] <;> ring

end Firedancer.Common.ScalarArithmetic.IntegerRegisters
