import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.IntegerConservation2

/-! Source-aligned exact integer identities. Carry masks and remainders are
related to their numbered quotient registers before ring normalization. -/

namespace Firedancer.Common.ScalarArithmetic.IntegerRegisters

set_option maxHeartbeats 2000000

attribute [local irreducible] z61 z63 z65 z67 z69 z71 z73 z75 z77 z79 z81 z83 z85 z87 z89 z91 z93 z95 z97 z99 z101 z103 z105 z106 z107 z108 z109 z110 z111 z112 z113 z114 z115 z116 z117 z118 z119 z120 z121 z122 z123 z124 z125 z126 z127 z128 z129 z130 z131 z132 z133 z134 z135 z136 z137 z138 z139 z140 z141 z142 z143 z144 z145 z146 z147 z148 z149 z150 z151 z152 z153 z154 z155 z156 z157 z158 z159 z160 z161 z162 z163 z164 z165 z166 z167 z168 z169 z170 z171 z172 z173 z174 z175 z176 z177 z178 z179 z180 z181 z182 z183 z184 z185 z186 z187 z188 z189 z190 z191 z192 z193 z194 z195 z196 z197 z198 z199 z200 z201 z202 z203 z204 z205 z206 z207 z208 z209 z210 z211 z212 z213 z214 z215 z216 z217 z218 z219 z220 z221 z222 z223 z224 z225 z226 z227 z228 z229 z230 z231 z232 z233 z234 z235 z236 z237 z238 z239 z240 z241 z242 z243 z244 z245 z246 z247 z248 z249 z250 z251 z252 z253 z254 z255 z256 z257 z258 z259 z260 z261 z262 z263 z264 z265 z266 z267 z268 z269 z270 z271 z272 z273 z274 z275 z276 z277 z278 z279 z280 z281 z282 z283 z284 z285 z286 z287 z288 z289 z290 z291 z292 z293 z294 z295 z296 z297 z298 z299 z300 z301 z302 z303 z304 z305 z306 z307 z308 z309 z310 z311 z312 z313 z314 z315 z316 z317 z318 z319 z320 z321 z322 z323 z324 z325 z326 z327 z328 z329 z330 z331 z332 z333 z334 z335 z336 z337 z338 z339 z340 z341 z342 z343 z344 z345 z346 z347 z348 z349 z350 z351 z352 z353 z354 z355 z356 z357 z358 z359 z360 z361 z362 z363 z364 z365 z366 z367 z368 z369 z370 z371 z372 z373 z374 z375 z376 z377 z378 z379 z380 z381 z382 z383 z384 z385 z386 z387 z388 z389 z390 z391 z392 z393 z394 z395 z396 z397 z398 z399 z400 z401 z402 z403 z404 z405 z406 z407 z408 z409 z410 z411 z412 z413 z414 z415 z416 z417 z418 z419 z420 z421 z422 z423 z424 z425 z426 z427 z428 z429 z430 z431 z432 z433 z434 z435 z436 z437 z438 z439 z440 z441 z442 z443 z444 z445 z446 m170 m179 m189 m196 m201 m206 m210 m213 m217 m222 m227 m301 m306 m311 m321 m329 m334 m338 m341 m345 m349 m354 m358

theorem z298_conservation (d : Digits) : z298 d = (d 0) + (666643) * (d 12) + (-455917814343) * (d 19) + (91101432451) * (d 20) + (-665179718615) * (d 21) + (436106517669) * (d 22) + (313519536328) * (d 23) + 1048576 + (-1398051700736) * (z191 d) + (666643) * (z215 d) := by
  simp only [z298, z287_conservation] <;> ring

theorem z300_conservation (d : Digits) : z300 d = (d 1) + (470296) * (d 12) + (666643) * (d 13) + (-321635904696) * (d 19) + (-391648573871) * (d 20) + (-378162267829) * (d 21) + (-357520070447) * (d 22) + (657284845285) * (d 23) + (-986281530349) * (z191 d) + (470296) * (z215 d) + (-1398051700736) * (z220 d) + (z299 d) := by
  simp only [z300, z289_conservation] <;> ring

theorem z301_conservation (d : Digits) : z301 d = (2097152) * (z299 d) := by
  have h : z301 d = 2097152 * z299 d := by
    rw [z301, m301, z299]
    have he := Int.emod_add_ediv_mul (z298 d) 2097152
    omega
  simp only [h] <;> ring

theorem z302_conservation (d : Digits) : z302 d = (d 0) + (666643) * (d 12) + (-455917814343) * (d 19) + (91101432451) * (d 20) + (-665179718615) * (d 21) + (436106517669) * (d 22) + (313519536328) * (d 23) + (-1398051700736) * (z191 d) + (666643) * (z215 d) + (-2097152) * (z299 d) := by
  simp only [z302, z287_conservation, z301_conservation] <;> ring

theorem z303_conservation (d : Digits) : z303 d = (654183) * (d 12) + (470296) * (d 13) + (666643) * (d 14) + (-447396407883) * (d 19) + (d 2) + (-232237218465) * (d 20) + (-1044395642186) * (d 21) + (49793129660) * (d 22) + (-49860422279) * (d 23) + 1048576 + (-1371920716520) * (z191 d) + (-1398051700736) * (z199 d) + (654183) * (z215 d) + (-986281530349) * (z220 d) := by
  simp only [z303, z291_conservation] <;> ring

theorem z305_conservation (d : Digits) : z305 d = (-997805) * (d 12) + (654183) * (d 13) + (470296) * (d 14) + (666643) * (d 15) + (682399837305) * (d 19) + (-583753445768) * (d 20) + (763377599560) * (d 21) + (-1697142710501) * (d 22) + (-419470570620) * (d 23) + (d 3) + (2092549405543) * (z191 d) + (-986281530349) * (z199 d) + (-997805) * (z215 d) + (-1371920716520) * (z220 d) + (-1398051700736) * (z225 d) + (z304 d) := by
  simp only [z305, z293_conservation] <;> ring

theorem z306_conservation (d : Digits) : z306 d = (2097152) * (z304 d) := by
  have h : z306 d = 2097152 * z304 d := by
    rw [z306, m306, z304]
    have he := Int.emod_add_ediv_mul (z303 d) 2097152
    omega
  simp only [h] <;> ring

theorem z307_conservation (d : Digits) : z307 d = (654183) * (d 12) + (470296) * (d 13) + (666643) * (d 14) + (-447396407883) * (d 19) + (d 2) + (-232237218465) * (d 20) + (-1044395642186) * (d 21) + (49793129660) * (d 22) + (-49860422279) * (d 23) + (-1371920716520) * (z191 d) + (-1398051700736) * (z199 d) + (654183) * (z215 d) + (-986281530349) * (z220 d) + (-2097152) * (z304 d) := by
  simp only [z307, z291_conservation, z306_conservation] <;> ring

theorem z308_conservation (d : Digits) : z308 d = (136657) * (d 12) + (-997805) * (d 13) + (654183) * (d 14) + (470296) * (d 15) + (666643) * (d 16) + (-93459858957) * (d 19) + (701074972954) * (d 20) + (-720110483653) * (d 21) + (852776285791) * (d 22) + (-1632873470029) * (d 23) + (d 4) + 1048576 + (-286591498669) * (z191 d) + (-1371920716520) * (z199 d) + (-1398051700736) * (z204 d) + (136657) * (z215 d) + (2092549405543) * (z220 d) + (-986281530349) * (z225 d) := by
  simp only [z308, z295_conservation] <;> ring

theorem z310_conservation (d : Digits) : z310 d = (-683901) * (d 12) + (136657) * (d 13) + (-997805) * (d 14) + (654183) * (d 15) + (470296) * (d 16) + (666643) * (d 17) + (467720577801) * (d 19) + (-186919717914) * (d 20) + (1383474810259) * (d 21) + (-1167506891536) * (d 22) + (531140381095) * (d 23) + (d 5) + (1434244486609) * (z191 d) + (2092549405543) * (z199 d) + (-986281530349) * (z204 d) + (-683901) * (z215 d) + (-286591498669) * (z220 d) + (-1371920716520) * (z225 d) + (z309 d) := by
  simp only [z310, z297_conservation] <;> ring

theorem z311_conservation (d : Digits) : z311 d = (2097152) * (z309 d) := by
  have h : z311 d = 2097152 * z309 d := by
    rw [z311, m311, z309]
    have he := Int.emod_add_ediv_mul (z308 d) 2097152
    omega
  simp only [h] <;> ring

theorem z312_conservation (d : Digits) : z312 d = (136657) * (d 12) + (-997805) * (d 13) + (654183) * (d 14) + (470296) * (d 15) + (666643) * (d 16) + (-93459858957) * (d 19) + (701074972954) * (d 20) + (-720110483653) * (d 21) + (852776285791) * (d 22) + (-1632873470029) * (d 23) + (d 4) + (-286591498669) * (z191 d) + (-1371920716520) * (z199 d) + (-1398051700736) * (z204 d) + (136657) * (z215 d) + (2092549405543) * (z220 d) + (-986281530349) * (z225 d) + (-2097152) * (z309 d) := by
  simp only [z312, z295_conservation, z311_conservation] <;> ring

theorem z313_conservation (d : Digits) : z313 d = (-683901) * (d 13) + (136657) * (d 14) + (-997805) * (d 15) + (654183) * (d 16) + (470296) * (d 17) + (666643) * (d 18) + (467720577801) * (d 20) + (-186919717914) * (d 21) + (1383474810259) * (d 22) + (-1167506891536) * (d 23) + (d 6) + 1048576 + (-2097152) * (z168 d) + (-683901) * (z191 d) + (-286591498669) * (z199 d) + (-1371920716520) * (z204 d) + (1434244486609) * (z220 d) + (2092549405543) * (z225 d) := by
  simp only [z313, z285_conservation] <;> ring

theorem z315_conservation (d : Digits) : z315 d = (654183) * (d 17) + (470296) * (d 18) + (666643) * (d 19) + (d 7) + (z168 d) + (654183) * (z204 d) := by
  simp only [z315, z233_conservation, z169_conservation] <;> ring

theorem z316_conservation (d : Digits) : z316 d = (654183) * (d 17) + (470296) * (d 18) + (666643) * (d 19) + (d 7) + (z168 d) + (654183) * (z204 d) + (-2097152) * (z209 d) := by
  simp only [z316, z315_conservation, z210_conservation] <;> ring

theorem z317_conservation (d : Digits) : z317 d = (-997805) * (d 16) + (654183) * (d 17) + (470296) * (d 18) + (666643) * (d 19) + (682399837305) * (d 23) + (d 7) + (z168 d) + (2092549405543) * (z204 d) + (-2097152) * (z209 d) + (-997805) * (z225 d) := by
  simp only [z317, z316_conservation, z246_conservation] <;> ring

theorem z318_conservation (d : Digits) : z318 d = (136657) * (d 15) + (-997805) * (d 16) + (654183) * (d 17) + (470296) * (d 18) + (666643) * (d 19) + (-93459858957) * (d 22) + (701074972954) * (d 23) + (d 7) + (z168 d) + (136657) * (z199 d) + (2092549405543) * (z204 d) + (-2097152) * (z209 d) + (-286591498669) * (z225 d) := by
  simp only [z318, z317_conservation, z257_conservation] <;> ring

theorem z319_conservation (d : Digits) : z319 d = (-683901) * (d 14) + (136657) * (d 15) + (-997805) * (d 16) + (654183) * (d 17) + (470296) * (d 18) + (666643) * (d 19) + (467720577801) * (d 21) + (-186919717914) * (d 22) + (1383474810259) * (d 23) + (d 7) + (z168 d) + (1434244486609) * (z199 d) + (2092549405543) * (z204 d) + (-2097152) * (z209 d) + (-683901) * (z220 d) + (-286591498669) * (z225 d) := by
  simp only [z319, z318_conservation, z273_conservation] <;> ring

theorem z320_conservation (d : Digits) : z320 d = (-683901) * (d 14) + (136657) * (d 15) + (-997805) * (d 16) + (654183) * (d 17) + (470296) * (d 18) + (666643) * (d 19) + (467720577801) * (d 21) + (-186919717914) * (d 22) + (1383474810259) * (d 23) + (d 7) + (z168 d) + (1434244486609) * (z199 d) + (2092549405543) * (z204 d) + (-2097152) * (z209 d) + (-683901) * (z220 d) + (-286591498669) * (z225 d) + (z314 d) := by
  simp only [z320, z319_conservation] <;> ring

theorem z321_conservation (d : Digits) : z321 d = (2097152) * (z314 d) := by
  have h : z321 d = 2097152 * z314 d := by
    rw [z321, m321, z314]
    have he := Int.emod_add_ediv_mul (z313 d) 2097152
    omega
  simp only [h] <;> ring

theorem z322_conservation (d : Digits) : z322 d = (-683901) * (d 13) + (136657) * (d 14) + (-997805) * (d 15) + (654183) * (d 16) + (470296) * (d 17) + (666643) * (d 18) + (467720577801) * (d 20) + (-186919717914) * (d 21) + (1383474810259) * (d 22) + (-1167506891536) * (d 23) + (d 6) + (-2097152) * (z168 d) + (-683901) * (z191 d) + (-286591498669) * (z199 d) + (-1371920716520) * (z204 d) + (1434244486609) * (z220 d) + (2092549405543) * (z225 d) + (-2097152) * (z314 d) := by
  simp only [z322, z285_conservation, z321_conservation] <;> ring

theorem z323_conservation (d : Digits) : z323 d = (-683901) * (d 15) + (136657) * (d 16) + (-997805) * (d 17) + (654183) * (d 18) + (470296) * (d 19) + (666643) * (d 20) + (467720577801) * (d 22) + (-186919717914) * (d 23) + (d 8) + 1048576 + (-2097152) * (z173 d) + (-683901) * (z199 d) + (-286591498669) * (z204 d) + (z209 d) + (1434244486609) * (z225 d) := by
  simp only [z323, z262_conservation] <;> ring

theorem z325_conservation (d : Digits) : z325 d = (136657) * (d 17) + (-997805) * (d 18) + (654183) * (d 19) + (470296) * (d 20) + (666643) * (d 21) + (d 9) + (z173 d) + (136657) * (z204 d) := by
  simp only [z325, z178_conservation, z235_conservation] <;> ring

theorem z326_conservation (d : Digits) : z326 d = (136657) * (d 17) + (-997805) * (d 18) + (654183) * (d 19) + (470296) * (d 20) + (666643) * (d 21) + (d 9) + (z173 d) + (136657) * (z204 d) + (-2097152) * (z212 d) := by
  simp only [z326, z325_conservation, z213_conservation] <;> ring

theorem z327_conservation (d : Digits) : z327 d = (-683901) * (d 16) + (136657) * (d 17) + (-997805) * (d 18) + (654183) * (d 19) + (470296) * (d 20) + (666643) * (d 21) + (467720577801) * (d 23) + (d 9) + (z173 d) + (1434244486609) * (z204 d) + (-2097152) * (z212 d) + (-683901) * (z225 d) := by
  simp only [z327, z326_conservation, z248_conservation] <;> ring

theorem z328_conservation (d : Digits) : z328 d = (-683901) * (d 16) + (136657) * (d 17) + (-997805) * (d 18) + (654183) * (d 19) + (470296) * (d 20) + (666643) * (d 21) + (467720577801) * (d 23) + (d 9) + (z173 d) + (1434244486609) * (z204 d) + (-2097152) * (z212 d) + (-683901) * (z225 d) + (z324 d) := by
  simp only [z328, z327_conservation] <;> ring

theorem z329_conservation (d : Digits) : z329 d = (2097152) * (z324 d) := by
  have h : z329 d = 2097152 * z324 d := by
    rw [z329, m329, z324]
    have he := Int.emod_add_ediv_mul (z323 d) 2097152
    omega
  simp only [h] <;> ring

theorem z330_conservation (d : Digits) : z330 d = (-683901) * (d 15) + (136657) * (d 16) + (-997805) * (d 17) + (654183) * (d 18) + (470296) * (d 19) + (666643) * (d 20) + (467720577801) * (d 22) + (-186919717914) * (d 23) + (d 8) + (-2097152) * (z173 d) + (-683901) * (z199 d) + (-286591498669) * (z204 d) + (z209 d) + (1434244486609) * (z225 d) + (-2097152) * (z324 d) := by
  simp only [z330, z262_conservation, z329_conservation] <;> ring

theorem z331_conservation (d : Digits) : z331 d = (d 10) + (-683901) * (d 17) + (136657) * (d 18) + (-997805) * (d 19) + (654183) * (d 20) + (470296) * (d 21) + (666643) * (d 22) + 1048576 + (-2097152) * (z182 d) + (-683901) * (z204 d) + (z212 d) := by
  simp only [z331, z239_conservation] <;> ring

theorem z333_conservation (d : Digits) : z333 d = (d 11) + (-683901) * (d 18) + (136657) * (d 19) + (-997805) * (d 20) + (654183) * (d 21) + (470296) * (d 22) + (666643) * (d 23) + (z182 d) + (-2097152) * (z215 d) + (z332 d) := by
  simp only [z333, z218_conservation] <;> ring

theorem z334_conservation (d : Digits) : z334 d = (2097152) * (z332 d) := by
  have h : z334 d = 2097152 * z332 d := by
    rw [z334, m334, z332]
    have he := Int.emod_add_ediv_mul (z331 d) 2097152
    omega
  simp only [h] <;> ring

theorem z335_conservation (d : Digits) : z335 d = (d 10) + (-683901) * (d 17) + (136657) * (d 18) + (-997805) * (d 19) + (654183) * (d 20) + (470296) * (d 21) + (666643) * (d 22) + (-2097152) * (z182 d) + (-683901) * (z204 d) + (z212 d) + (-2097152) * (z332 d) := by
  simp only [z335, z239_conservation, z334_conservation] <;> ring

theorem z336_conservation (d : Digits) : z336 d = (d 1) + (470296) * (d 12) + (666643) * (d 13) + (-321635904696) * (d 19) + (-391648573871) * (d 20) + (-378162267829) * (d 21) + (-357520070447) * (d 22) + (657284845285) * (d 23) + 1048576 + (-986281530349) * (z191 d) + (470296) * (z215 d) + (-1398051700736) * (z220 d) + (z299 d) := by
  simp only [z336, z300_conservation] <;> ring

theorem z338_conservation (d : Digits) : z338 d = (2097152) * (z337 d) := by
  have h : z338 d = 2097152 * z337 d := by
    rw [z338, m338, z337]
    have he := Int.emod_add_ediv_mul (z336 d) 2097152
    omega
  simp only [h] <;> ring

theorem z339_conservation (d : Digits) : z339 d = (-997805) * (d 12) + (654183) * (d 13) + (470296) * (d 14) + (666643) * (d 15) + (682399837305) * (d 19) + (-583753445768) * (d 20) + (763377599560) * (d 21) + (-1697142710501) * (d 22) + (-419470570620) * (d 23) + (d 3) + 1048576 + (2092549405543) * (z191 d) + (-986281530349) * (z199 d) + (-997805) * (z215 d) + (-1371920716520) * (z220 d) + (-1398051700736) * (z225 d) + (z304 d) := by
  simp only [z339, z305_conservation] <;> ring

theorem z341_conservation (d : Digits) : z341 d = (2097152) * (z340 d) := by
  have h : z341 d = 2097152 * z340 d := by
    rw [z341, m341, z340]
    have he := Int.emod_add_ediv_mul (z339 d) 2097152
    omega
  simp only [h] <;> ring

theorem z342_conservation (d : Digits) : z342 d = (-683901) * (d 12) + (136657) * (d 13) + (-997805) * (d 14) + (654183) * (d 15) + (470296) * (d 16) + (666643) * (d 17) + (467720577801) * (d 19) + (-186919717914) * (d 20) + (1383474810259) * (d 21) + (-1167506891536) * (d 22) + (531140381095) * (d 23) + (d 5) + 1048576 + (1434244486609) * (z191 d) + (2092549405543) * (z199 d) + (-986281530349) * (z204 d) + (-683901) * (z215 d) + (-286591498669) * (z220 d) + (-1371920716520) * (z225 d) + (z309 d) := by
  simp only [z342, z310_conservation] <;> ring

theorem z344_conservation (d : Digits) : z344 d = (-683901) * (d 13) + (136657) * (d 14) + (-997805) * (d 15) + (654183) * (d 16) + (470296) * (d 17) + (666643) * (d 18) + (467720577801) * (d 20) + (-186919717914) * (d 21) + (1383474810259) * (d 22) + (-1167506891536) * (d 23) + (d 6) + (-2097152) * (z168 d) + (-683901) * (z191 d) + (-286591498669) * (z199 d) + (-1371920716520) * (z204 d) + (1434244486609) * (z220 d) + (2092549405543) * (z225 d) + (-2097152) * (z314 d) + (z343 d) := by
  simp only [z344, z322_conservation] <;> ring

theorem z345_conservation (d : Digits) : z345 d = (2097152) * (z343 d) := by
  have h : z345 d = 2097152 * z343 d := by
    rw [z345, m345, z343]
    have he := Int.emod_add_ediv_mul (z342 d) 2097152
    omega
  simp only [h] <;> ring

theorem z346_conservation (d : Digits) : z346 d = (-683901) * (d 14) + (136657) * (d 15) + (-997805) * (d 16) + (654183) * (d 17) + (470296) * (d 18) + (666643) * (d 19) + (467720577801) * (d 21) + (-186919717914) * (d 22) + (1383474810259) * (d 23) + (d 7) + 1048576 + (z168 d) + (1434244486609) * (z199 d) + (2092549405543) * (z204 d) + (-2097152) * (z209 d) + (-683901) * (z220 d) + (-286591498669) * (z225 d) + (z314 d) := by
  simp only [z346, z320_conservation] <;> ring

theorem z348_conservation (d : Digits) : z348 d = (-683901) * (d 15) + (136657) * (d 16) + (-997805) * (d 17) + (654183) * (d 18) + (470296) * (d 19) + (666643) * (d 20) + (467720577801) * (d 22) + (-186919717914) * (d 23) + (d 8) + (-2097152) * (z173 d) + (-683901) * (z199 d) + (-286591498669) * (z204 d) + (z209 d) + (1434244486609) * (z225 d) + (-2097152) * (z324 d) + (z347 d) := by
  simp only [z348, z330_conservation] <;> ring

theorem z349_conservation (d : Digits) : z349 d = (2097152) * (z347 d) := by
  have h : z349 d = 2097152 * z347 d := by
    rw [z349, m349, z347]
    have he := Int.emod_add_ediv_mul (z346 d) 2097152
    omega
  simp only [h] <;> ring

theorem z350_conservation (d : Digits) : z350 d = (-683901) * (d 14) + (136657) * (d 15) + (-997805) * (d 16) + (654183) * (d 17) + (470296) * (d 18) + (666643) * (d 19) + (467720577801) * (d 21) + (-186919717914) * (d 22) + (1383474810259) * (d 23) + (d 7) + (z168 d) + (1434244486609) * (z199 d) + (2092549405543) * (z204 d) + (-2097152) * (z209 d) + (-683901) * (z220 d) + (-286591498669) * (z225 d) + (z314 d) + (-2097152) * (z347 d) := by
  simp only [z350, z320_conservation, z349_conservation] <;> ring

theorem z351_conservation (d : Digits) : z351 d = (-683901) * (d 16) + (136657) * (d 17) + (-997805) * (d 18) + (654183) * (d 19) + (470296) * (d 20) + (666643) * (d 21) + (467720577801) * (d 23) + (d 9) + 1048576 + (z173 d) + (1434244486609) * (z204 d) + (-2097152) * (z212 d) + (-683901) * (z225 d) + (z324 d) := by
  simp only [z351, z328_conservation] <;> ring

theorem z353_conservation (d : Digits) : z353 d = (d 10) + (-683901) * (d 17) + (136657) * (d 18) + (-997805) * (d 19) + (654183) * (d 20) + (470296) * (d 21) + (666643) * (d 22) + (-2097152) * (z182 d) + (-683901) * (z204 d) + (z212 d) + (-2097152) * (z332 d) + (z352 d) := by
  simp only [z353, z335_conservation] <;> ring

theorem z354_conservation (d : Digits) : z354 d = (2097152) * (z352 d) := by
  have h : z354 d = 2097152 * z352 d := by
    rw [z354, m354, z352]
    have he := Int.emod_add_ediv_mul (z351 d) 2097152
    omega
  simp only [h] <;> ring

theorem z355_conservation (d : Digits) : z355 d = (-683901) * (d 16) + (136657) * (d 17) + (-997805) * (d 18) + (654183) * (d 19) + (470296) * (d 20) + (666643) * (d 21) + (467720577801) * (d 23) + (d 9) + (z173 d) + (1434244486609) * (z204 d) + (-2097152) * (z212 d) + (-683901) * (z225 d) + (z324 d) + (-2097152) * (z352 d) := by
  simp only [z355, z328_conservation, z354_conservation] <;> ring

theorem z356_conservation (d : Digits) : z356 d = (d 11) + (-683901) * (d 18) + (136657) * (d 19) + (-997805) * (d 20) + (654183) * (d 21) + (470296) * (d 22) + (666643) * (d 23) + 1048576 + (z182 d) + (-2097152) * (z215 d) + (z332 d) := by
  simp only [z356, z333_conservation] <;> ring

theorem z358_conservation (d : Digits) : z358 d = (2097152) * (z357 d) := by
  have h : z358 d = 2097152 * z357 d := by
    rw [z358, m358, z357]
    have he := Int.emod_add_ediv_mul (z356 d) 2097152
    omega
  simp only [h] <;> ring

theorem z359_conservation (d : Digits) : z359 d = (d 11) + (-683901) * (d 18) + (136657) * (d 19) + (-997805) * (d 20) + (654183) * (d 21) + (470296) * (d 22) + (666643) * (d 23) + (z182 d) + (-2097152) * (z215 d) + (z332 d) + (-2097152) * (z357 d) := by
  simp only [z359, z333_conservation, z358_conservation] <;> ring

theorem z360_conservation (d : Digits) : z360 d = (666643) * (z357 d) := by
  simp only [z360] <;> ring

theorem z361_conservation (d : Digits) : z361 d = (d 0) + (666643) * (d 12) + (-455917814343) * (d 19) + (91101432451) * (d 20) + (-665179718615) * (d 21) + (436106517669) * (d 22) + (313519536328) * (d 23) + (-1398051700736) * (z191 d) + (666643) * (z215 d) + (-2097152) * (z299 d) + (666643) * (z357 d) := by
  simp only [z361, z302_conservation, z360_conservation] <;> ring

theorem z362_conservation (d : Digits) : z362 d = (470296) * (z357 d) := by
  simp only [z362] <;> ring

theorem z363_conservation (d : Digits) : z363 d = (654183) * (z357 d) := by
  simp only [z363] <;> ring

theorem z364_conservation (d : Digits) : z364 d = (-997805) * (z357 d) := by
  simp only [z364] <;> ring

theorem z365_conservation (d : Digits) : z365 d = (136657) * (z357 d) := by
  simp only [z365] <;> ring

theorem z366_conservation (d : Digits) : z366 d = (-683901) * (z357 d) := by
  simp only [z366] <;> ring

end Firedancer.Common.ScalarArithmetic.IntegerRegisters
