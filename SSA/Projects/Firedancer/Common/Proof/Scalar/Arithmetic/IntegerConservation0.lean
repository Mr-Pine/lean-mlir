import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.IntegerBounds5

/-! Source-aligned exact integer identities. Carry masks and remainders are
related to their numbered quotient registers before ring normalization. -/

namespace Firedancer.Common.ScalarArithmetic.IntegerRegisters

set_option maxHeartbeats 2000000

attribute [local irreducible] z61 z63 z65 z67 z69 z71 z73 z75 z77 z79 z81 z83 z85 z87 z89 z91 z93 z95 z97 z99 z101 z103 z105 z106 z107 z108 z109 z110 z111 z112 z113 z114 z115 z116 z117 z118 z119 z120 z121 z122 z123 z124 z125 z126 z127 z128 z129 z130 z131 z132 z133 z134 z135 z136 z137 z138 z139 z140 z141 z142 z143 z144 z145 z146 z147 z148 z149 z150 z151 z152 z153 z154 z155 z156 z157 z158 z159 z160 z161 z162 z163 z164 z165 z166 z167 z168 z169 z170 z171 z172 z173 z174 z175 z176 z177 z178 z179 z180 z181 z182 z183 z184 z185 z186 z187 z188 z189 z190 z191 z192 z193 z194 z195 z196 z197 z198 z199 z200 z201 z202 z203 z204 z205 z206 z207 z208 z209 z210 z211 z212 z213 z214 z215 z216 z217 z218 z219 z220 z221 z222 z223 z224 z225 z226 z227 z228 z229 z230 z231 z232 z233 z234 z235 z236 z237 z238 z239 z240 z241 z242 z243 z244 z245 z246 z247 z248 z249 z250 z251 z252 z253 z254 z255 z256 z257 z258 z259 z260 z261 z262 z263 z264 z265 z266 z267 z268 z269 z270 z271 z272 z273 z274 z275 z276 z277 z278 z279 z280 z281 z282 z283 z284 z285 z286 z287 z288 z289 z290 z291 z292 z293 z294 z295 z296 z297 z298 z299 z300 z301 z302 z303 z304 z305 z306 z307 z308 z309 z310 z311 z312 z313 z314 z315 z316 z317 z318 z319 z320 z321 z322 z323 z324 z325 z326 z327 z328 z329 z330 z331 z332 z333 z334 z335 z336 z337 z338 z339 z340 z341 z342 z343 z344 z345 z346 z347 z348 z349 z350 z351 z352 z353 z354 z355 z356 z357 z358 z359 z360 z361 z362 z363 z364 z365 z366 z367 z368 z369 z370 z371 z372 z373 z374 z375 z376 z377 z378 z379 z380 z381 z382 z383 z384 z385 z386 z387 z388 z389 z390 z391 z392 z393 z394 z395 z396 z397 z398 z399 z400 z401 z402 z403 z404 z405 z406 z407 z408 z409 z410 z411 z412 z413 z414 z415 z416 z417 z418 z419 z420 z421 z422 z423 z424 z425 z426 z427 z428 z429 z430 z431 z432 z433 z434 z435 z436 z437 z438 z439 z440 z441 z442 z443 z444 z445 z446 m170 m179 m189 m196 m201 m206 m210 m213 m217 m222 m227 m301 m306 m311 m321 m329 m334 m338 m341 m345 m349 m354 m358

theorem z107_conservation (d : Digits) : z107 d = (666643) * (d 23) := by
  simp only [z107, z106_linear] <;> ring

theorem z108_conservation (d : Digits) : z108 d = (d 11) + (666643) * (d 23) := by
  simp only [z108, z107_conservation, z83_linear] <;> ring

theorem z109_conservation (d : Digits) : z109 d = (470296) * (d 23) := by
  simp only [z109, z106_linear] <;> ring

theorem z110_conservation (d : Digits) : z110 d = (d 12) + (470296) * (d 23) := by
  simp only [z110, z109_conservation, z85_linear] <;> ring

theorem z111_conservation (d : Digits) : z111 d = (654183) * (d 23) := by
  simp only [z111, z106_linear] <;> ring

theorem z112_conservation (d : Digits) : z112 d = (d 13) + (654183) * (d 23) := by
  simp only [z112, z111_conservation, z87_linear] <;> ring

theorem z113_conservation (d : Digits) : z113 d = (-997805) * (d 23) := by
  simp only [z113, z106_linear] <;> ring

theorem z114_conservation (d : Digits) : z114 d = (d 14) + (-997805) * (d 23) := by
  simp only [z114, z113_conservation, z89_linear] <;> ring

theorem z115_conservation (d : Digits) : z115 d = (136657) * (d 23) := by
  simp only [z115, z106_linear] <;> ring

theorem z116_conservation (d : Digits) : z116 d = (d 15) + (136657) * (d 23) := by
  simp only [z116, z115_conservation, z91_linear] <;> ring

theorem z117_conservation (d : Digits) : z117 d = (-683901) * (d 23) := by
  simp only [z117, z106_linear] <;> ring

theorem z118_conservation (d : Digits) : z118 d = (d 16) + (-683901) * (d 23) := by
  simp only [z118, z117_conservation, z93_linear] <;> ring

theorem z119_conservation (d : Digits) : z119 d = (666643) * (d 22) := by
  simp only [z119, z105_linear] <;> ring

theorem z120_conservation (d : Digits) : z120 d = (470296) * (d 22) := by
  simp only [z120, z105_linear] <;> ring

theorem z121_conservation (d : Digits) : z121 d = (654183) * (d 22) := by
  simp only [z121, z105_linear] <;> ring

theorem z122_conservation (d : Digits) : z122 d = (-997805) * (d 22) := by
  simp only [z122, z105_linear] <;> ring

theorem z123_conservation (d : Digits) : z123 d = (136657) * (d 22) := by
  simp only [z123, z105_linear] <;> ring

theorem z124_conservation (d : Digits) : z124 d = (d 14) + (136657) * (d 22) + (-997805) * (d 23) := by
  simp only [z124, z114_conservation, z123_conservation] <;> ring

theorem z125_conservation (d : Digits) : z125 d = (-683901) * (d 22) := by
  simp only [z125, z105_linear] <;> ring

theorem z126_conservation (d : Digits) : z126 d = (d 15) + (-683901) * (d 22) + (136657) * (d 23) := by
  simp only [z126, z116_conservation, z125_conservation] <;> ring

theorem z127_conservation (d : Digits) : z127 d = (666643) * (d 21) := by
  simp only [z127, z103_linear] <;> ring

theorem z128_conservation (d : Digits) : z128 d = (470296) * (d 21) := by
  simp only [z128, z103_linear] <;> ring

theorem z129_conservation (d : Digits) : z129 d = (654183) * (d 21) := by
  simp only [z129, z103_linear] <;> ring

theorem z130_conservation (d : Digits) : z130 d = (-997805) * (d 21) := by
  simp only [z130, z103_linear] <;> ring

theorem z131_conservation (d : Digits) : z131 d = (136657) * (d 21) := by
  simp only [z131, z103_linear] <;> ring

theorem z132_conservation (d : Digits) : z132 d = (-683901) * (d 21) := by
  simp only [z132, z103_linear] <;> ring

theorem z133_conservation (d : Digits) : z133 d = (d 14) + (-683901) * (d 21) + (136657) * (d 22) + (-997805) * (d 23) := by
  simp only [z133, z124_conservation, z132_conservation] <;> ring

theorem z134_conservation (d : Digits) : z134 d = (666643) * (d 20) := by
  simp only [z134, z101_linear] <;> ring

theorem z135_conservation (d : Digits) : z135 d = (666643) * (d 20) + (d 8) := by
  simp only [z135, z134_conservation, z77_linear] <;> ring

theorem z136_conservation (d : Digits) : z136 d = (470296) * (d 20) := by
  simp only [z136, z101_linear] <;> ring

theorem z137_conservation (d : Digits) : z137 d = (654183) * (d 20) := by
  simp only [z137, z101_linear] <;> ring

theorem z138_conservation (d : Digits) : z138 d = (-997805) * (d 20) := by
  simp only [z138, z101_linear] <;> ring

theorem z139_conservation (d : Digits) : z139 d = (136657) * (d 20) := by
  simp only [z139, z101_linear] <;> ring

theorem z140_conservation (d : Digits) : z140 d = (-683901) * (d 20) := by
  simp only [z140, z101_linear] <;> ring

theorem z141_conservation (d : Digits) : z141 d = (666643) * (d 19) := by
  simp only [z141, z99_linear] <;> ring

theorem z142_conservation (d : Digits) : z142 d = (666643) * (d 19) + (d 7) := by
  simp only [z142, z141_conservation, z75_linear] <;> ring

theorem z143_conservation (d : Digits) : z143 d = (470296) * (d 19) := by
  simp only [z143, z99_linear] <;> ring

theorem z144_conservation (d : Digits) : z144 d = (470296) * (d 19) + (666643) * (d 20) + (d 8) := by
  simp only [z144, z135_conservation, z143_conservation] <;> ring

theorem z145_conservation (d : Digits) : z145 d = (654183) * (d 19) := by
  simp only [z145, z99_linear] <;> ring

theorem z146_conservation (d : Digits) : z146 d = (-997805) * (d 19) := by
  simp only [z146, z99_linear] <;> ring

theorem z147_conservation (d : Digits) : z147 d = (136657) * (d 19) := by
  simp only [z147, z99_linear] <;> ring

theorem z148_conservation (d : Digits) : z148 d = (-683901) * (d 19) := by
  simp only [z148, z99_linear] <;> ring

theorem z149_conservation (d : Digits) : z149 d = (d 12) + (136657) * (d 20) + (470296) * (d 23) := by
  simp only [z149, z110_conservation, z139_conservation] <;> ring

theorem z150_conservation (d : Digits) : z150 d = (d 12) + (-683901) * (d 19) + (136657) * (d 20) + (470296) * (d 23) := by
  simp only [z150, z149_conservation, z148_conservation] <;> ring

theorem z151_conservation (d : Digits) : z151 d = (d 12) + (-683901) * (d 19) + (136657) * (d 20) + (654183) * (d 22) + (470296) * (d 23) := by
  simp only [z151, z150_conservation, z121_conservation] <;> ring

theorem z152_conservation (d : Digits) : z152 d = (d 12) + (-683901) * (d 19) + (136657) * (d 20) + (-997805) * (d 21) + (654183) * (d 22) + (470296) * (d 23) := by
  simp only [z152, z151_conservation, z130_conservation] <;> ring

theorem z153_conservation (d : Digits) : z153 d = (666643) * (d 18) := by
  simp only [z153, z97_linear] <;> ring

theorem z154_conservation (d : Digits) : z154 d = (666643) * (d 18) + (d 6) := by
  simp only [z154, z153_conservation, z73_linear] <;> ring

theorem z155_conservation (d : Digits) : z155 d = (470296) * (d 18) := by
  simp only [z155, z97_linear] <;> ring

theorem z156_conservation (d : Digits) : z156 d = (470296) * (d 18) + (666643) * (d 19) + (d 7) := by
  simp only [z156, z142_conservation, z155_conservation] <;> ring

theorem z157_conservation (d : Digits) : z157 d = (654183) * (d 18) := by
  simp only [z157, z97_linear] <;> ring

theorem z158_conservation (d : Digits) : z158 d = (654183) * (d 18) + (470296) * (d 19) + (666643) * (d 20) + (d 8) := by
  simp only [z158, z144_conservation, z157_conservation] <;> ring

theorem z159_conservation (d : Digits) : z159 d = (-997805) * (d 18) := by
  simp only [z159, z97_linear] <;> ring

theorem z160_conservation (d : Digits) : z160 d = (136657) * (d 18) := by
  simp only [z160, z97_linear] <;> ring

theorem z161_conservation (d : Digits) : z161 d = (d 10) + (654183) * (d 20) := by
  simp only [z161, z137_conservation, z81_linear] <;> ring

theorem z162_conservation (d : Digits) : z162 d = (d 10) + (-997805) * (d 19) + (654183) * (d 20) := by
  simp only [z162, z161_conservation, z146_conservation] <;> ring

theorem z163_conservation (d : Digits) : z163 d = (d 10) + (136657) * (d 18) + (-997805) * (d 19) + (654183) * (d 20) := by
  simp only [z163, z162_conservation, z160_conservation] <;> ring

theorem z164_conservation (d : Digits) : z164 d = (d 10) + (136657) * (d 18) + (-997805) * (d 19) + (654183) * (d 20) + (666643) * (d 22) := by
  simp only [z164, z163_conservation, z119_conservation] <;> ring

theorem z165_conservation (d : Digits) : z165 d = (d 10) + (136657) * (d 18) + (-997805) * (d 19) + (654183) * (d 20) + (470296) * (d 21) + (666643) * (d 22) := by
  simp only [z165, z164_conservation, z128_conservation] <;> ring

theorem z166_conservation (d : Digits) : z166 d = (-683901) * (d 18) := by
  simp only [z166, z97_linear] <;> ring

end Firedancer.Common.ScalarArithmetic.IntegerRegisters
