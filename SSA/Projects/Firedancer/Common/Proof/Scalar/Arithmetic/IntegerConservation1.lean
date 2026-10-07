import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.IntegerConservation0

/-! Source-aligned exact integer identities. Carry masks and remainders are
related to their numbered quotient registers before ring normalization. -/

namespace Firedancer.Common.ScalarArithmetic.IntegerRegisters

set_option maxHeartbeats 2000000

attribute [local irreducible] z61 z63 z65 z67 z69 z71 z73 z75 z77 z79 z81 z83 z85 z87 z89 z91 z93 z95 z97 z99 z101 z103 z105 z106 z107 z108 z109 z110 z111 z112 z113 z114 z115 z116 z117 z118 z119 z120 z121 z122 z123 z124 z125 z126 z127 z128 z129 z130 z131 z132 z133 z134 z135 z136 z137 z138 z139 z140 z141 z142 z143 z144 z145 z146 z147 z148 z149 z150 z151 z152 z153 z154 z155 z156 z157 z158 z159 z160 z161 z162 z163 z164 z165 z166 z167 z168 z169 z170 z171 z172 z173 z174 z175 z176 z177 z178 z179 z180 z181 z182 z183 z184 z185 z186 z187 z188 z189 z190 z191 z192 z193 z194 z195 z196 z197 z198 z199 z200 z201 z202 z203 z204 z205 z206 z207 z208 z209 z210 z211 z212 z213 z214 z215 z216 z217 z218 z219 z220 z221 z222 z223 z224 z225 z226 z227 z228 z229 z230 z231 z232 z233 z234 z235 z236 z237 z238 z239 z240 z241 z242 z243 z244 z245 z246 z247 z248 z249 z250 z251 z252 z253 z254 z255 z256 z257 z258 z259 z260 z261 z262 z263 z264 z265 z266 z267 z268 z269 z270 z271 z272 z273 z274 z275 z276 z277 z278 z279 z280 z281 z282 z283 z284 z285 z286 z287 z288 z289 z290 z291 z292 z293 z294 z295 z296 z297 z298 z299 z300 z301 z302 z303 z304 z305 z306 z307 z308 z309 z310 z311 z312 z313 z314 z315 z316 z317 z318 z319 z320 z321 z322 z323 z324 z325 z326 z327 z328 z329 z330 z331 z332 z333 z334 z335 z336 z337 z338 z339 z340 z341 z342 z343 z344 z345 z346 z347 z348 z349 z350 z351 z352 z353 z354 z355 z356 z357 z358 z359 z360 z361 z362 z363 z364 z365 z366 z367 z368 z369 z370 z371 z372 z373 z374 z375 z376 z377 z378 z379 z380 z381 z382 z383 z384 z385 z386 z387 z388 z389 z390 z391 z392 z393 z394 z395 z396 z397 z398 z399 z400 z401 z402 z403 z404 z405 z406 z407 z408 z409 z410 z411 z412 z413 z414 z415 z416 z417 z418 z419 z420 z421 z422 z423 z424 z425 z426 z427 z428 z429 z430 z431 z432 z433 z434 z435 z436 z437 z438 z439 z440 z441 z442 z443 z444 z445 z446 m170 m179 m189 m196 m201 m206 m210 m213 m217 m222 m227 m301 m306 m311 m321 m329 m334 m338 m341 m345 m349 m354 m358

theorem z167_conservation (d : Digits) : z167 d = (666643) * (d 18) + (d 6) + 1048576 := by
  simp only [z167, z154_conservation] <;> ring

theorem z169_conservation (d : Digits) : z169 d = (470296) * (d 18) + (666643) * (d 19) + (d 7) + (z168 d) := by
  simp only [z169, z156_conservation] <;> ring

theorem z170_conservation (d : Digits) : z170 d = (2097152) * (z168 d) := by
  have h : z170 d = 2097152 * z168 d := by
    rw [z170, m170, z168]
    have he := Int.emod_add_ediv_mul (z167 d) 2097152
    omega
  simp only [h] <;> ring

theorem z171_conservation (d : Digits) : z171 d = (666643) * (d 18) + (d 6) + (-2097152) * (z168 d) := by
  simp only [z171, z154_conservation, z170_conservation] <;> ring

theorem z172_conservation (d : Digits) : z172 d = (654183) * (d 18) + (470296) * (d 19) + (666643) * (d 20) + (d 8) + 1048576 := by
  simp only [z172, z158_conservation] <;> ring

theorem z174_conservation (d : Digits) : z174 d = (470296) * (d 20) + (d 9) := by
  simp only [z174, z136_conservation, z79_linear] <;> ring

theorem z175_conservation (d : Digits) : z175 d = (654183) * (d 19) + (470296) * (d 20) + (d 9) := by
  simp only [z175, z174_conservation, z145_conservation] <;> ring

theorem z176_conservation (d : Digits) : z176 d = (-997805) * (d 18) + (654183) * (d 19) + (470296) * (d 20) + (d 9) := by
  simp only [z176, z175_conservation, z159_conservation] <;> ring

theorem z177_conservation (d : Digits) : z177 d = (-997805) * (d 18) + (654183) * (d 19) + (470296) * (d 20) + (666643) * (d 21) + (d 9) := by
  simp only [z177, z176_conservation, z127_conservation] <;> ring

theorem z178_conservation (d : Digits) : z178 d = (-997805) * (d 18) + (654183) * (d 19) + (470296) * (d 20) + (666643) * (d 21) + (d 9) + (z173 d) := by
  simp only [z178, z177_conservation] <;> ring

theorem z179_conservation (d : Digits) : z179 d = (2097152) * (z173 d) := by
  have h : z179 d = 2097152 * z173 d := by
    rw [z179, m179, z173]
    have he := Int.emod_add_ediv_mul (z172 d) 2097152
    omega
  simp only [h] <;> ring

theorem z180_conservation (d : Digits) : z180 d = (654183) * (d 18) + (470296) * (d 19) + (666643) * (d 20) + (d 8) + (-2097152) * (z173 d) := by
  simp only [z180, z158_conservation, z179_conservation] <;> ring

theorem z181_conservation (d : Digits) : z181 d = (d 10) + (136657) * (d 18) + (-997805) * (d 19) + (654183) * (d 20) + (470296) * (d 21) + (666643) * (d 22) + 1048576 := by
  simp only [z181, z165_conservation] <;> ring

theorem z183_conservation (d : Digits) : z183 d = (d 11) + (-997805) * (d 20) + (666643) * (d 23) := by
  simp only [z183, z108_conservation, z138_conservation] <;> ring

theorem z184_conservation (d : Digits) : z184 d = (d 11) + (136657) * (d 19) + (-997805) * (d 20) + (666643) * (d 23) := by
  simp only [z184, z183_conservation, z147_conservation] <;> ring

theorem z185_conservation (d : Digits) : z185 d = (d 11) + (-683901) * (d 18) + (136657) * (d 19) + (-997805) * (d 20) + (666643) * (d 23) := by
  simp only [z185, z184_conservation, z166_conservation] <;> ring

theorem z186_conservation (d : Digits) : z186 d = (d 11) + (-683901) * (d 18) + (136657) * (d 19) + (-997805) * (d 20) + (470296) * (d 22) + (666643) * (d 23) := by
  simp only [z186, z185_conservation, z120_conservation] <;> ring

theorem z187_conservation (d : Digits) : z187 d = (d 11) + (-683901) * (d 18) + (136657) * (d 19) + (-997805) * (d 20) + (654183) * (d 21) + (470296) * (d 22) + (666643) * (d 23) := by
  simp only [z187, z186_conservation, z129_conservation] <;> ring

theorem z188_conservation (d : Digits) : z188 d = (d 11) + (-683901) * (d 18) + (136657) * (d 19) + (-997805) * (d 20) + (654183) * (d 21) + (470296) * (d 22) + (666643) * (d 23) + (z182 d) := by
  simp only [z188, z187_conservation] <;> ring

theorem z189_conservation (d : Digits) : z189 d = (2097152) * (z182 d) := by
  have h : z189 d = 2097152 * z182 d := by
    rw [z189, m189, z182]
    have he := Int.emod_add_ediv_mul (z181 d) 2097152
    omega
  simp only [h] <;> ring

theorem z190_conservation (d : Digits) : z190 d = (d 12) + (-683901) * (d 19) + (136657) * (d 20) + (-997805) * (d 21) + (654183) * (d 22) + (470296) * (d 23) + 1048576 := by
  simp only [z190, z152_conservation] <;> ring

theorem z192_conservation (d : Digits) : z192 d = (d 13) + (-683901) * (d 20) + (654183) * (d 23) := by
  simp only [z192, z112_conservation, z140_conservation] <;> ring

theorem z193_conservation (d : Digits) : z193 d = (d 13) + (-683901) * (d 20) + (-997805) * (d 22) + (654183) * (d 23) := by
  simp only [z193, z192_conservation, z122_conservation] <;> ring

theorem z194_conservation (d : Digits) : z194 d = (d 13) + (-683901) * (d 20) + (136657) * (d 21) + (-997805) * (d 22) + (654183) * (d 23) := by
  simp only [z194, z193_conservation, z131_conservation] <;> ring

theorem z195_conservation (d : Digits) : z195 d = (d 13) + (-683901) * (d 20) + (136657) * (d 21) + (-997805) * (d 22) + (654183) * (d 23) + (z191 d) := by
  simp only [z195, z194_conservation] <;> ring

theorem z196_conservation (d : Digits) : z196 d = (2097152) * (z191 d) := by
  have h : z196 d = 2097152 * z191 d := by
    rw [z196, m196, z191]
    have he := Int.emod_add_ediv_mul (z190 d) 2097152
    omega
  simp only [h] <;> ring

theorem z197_conservation (d : Digits) : z197 d = (d 12) + (-683901) * (d 19) + (136657) * (d 20) + (-997805) * (d 21) + (654183) * (d 22) + (470296) * (d 23) + (-2097152) * (z191 d) := by
  simp only [z197, z152_conservation, z196_conservation] <;> ring

theorem z198_conservation (d : Digits) : z198 d = (d 14) + (-683901) * (d 21) + (136657) * (d 22) + (-997805) * (d 23) + 1048576 := by
  simp only [z198, z133_conservation] <;> ring

theorem z200_conservation (d : Digits) : z200 d = (d 15) + (-683901) * (d 22) + (136657) * (d 23) + (z199 d) := by
  simp only [z200, z126_conservation] <;> ring

theorem z201_conservation (d : Digits) : z201 d = (2097152) * (z199 d) := by
  have h : z201 d = 2097152 * z199 d := by
    rw [z201, m201, z199]
    have he := Int.emod_add_ediv_mul (z198 d) 2097152
    omega
  simp only [h] <;> ring

theorem z202_conservation (d : Digits) : z202 d = (d 14) + (-683901) * (d 21) + (136657) * (d 22) + (-997805) * (d 23) + (-2097152) * (z199 d) := by
  simp only [z202, z133_conservation, z201_conservation] <;> ring

theorem z203_conservation (d : Digits) : z203 d = (d 16) + (-683901) * (d 23) + 1048576 := by
  simp only [z203, z118_conservation] <;> ring

theorem z205_conservation (d : Digits) : z205 d = (d 17) + (z204 d) := by
  simp only [z205, z95_linear] <;> ring

theorem z206_conservation (d : Digits) : z206 d = (2097152) * (z204 d) := by
  have h : z206 d = 2097152 * z204 d := by
    rw [z206, m206, z204]
    have he := Int.emod_add_ediv_mul (z203 d) 2097152
    omega
  simp only [h] <;> ring

theorem z207_conservation (d : Digits) : z207 d = (d 16) + (-683901) * (d 23) + (-2097152) * (z204 d) := by
  simp only [z207, z118_conservation, z206_conservation] <;> ring

theorem z208_conservation (d : Digits) : z208 d = (470296) * (d 18) + (666643) * (d 19) + (d 7) + 1048576 + (z168 d) := by
  simp only [z208, z169_conservation] <;> ring

theorem z210_conservation (d : Digits) : z210 d = (2097152) * (z209 d) := by
  have h : z210 d = 2097152 * z209 d := by
    rw [z210, m210, z209]
    have he := Int.emod_add_ediv_mul (z208 d) 2097152
    omega
  simp only [h] <;> ring

theorem z211_conservation (d : Digits) : z211 d = (-997805) * (d 18) + (654183) * (d 19) + (470296) * (d 20) + (666643) * (d 21) + (d 9) + 1048576 + (z173 d) := by
  simp only [z211, z178_conservation] <;> ring

theorem z213_conservation (d : Digits) : z213 d = (2097152) * (z212 d) := by
  have h : z213 d = 2097152 * z212 d := by
    rw [z213, m213, z212]
    have he := Int.emod_add_ediv_mul (z211 d) 2097152
    omega
  simp only [h] <;> ring

theorem z214_conservation (d : Digits) : z214 d = (d 11) + (-683901) * (d 18) + (136657) * (d 19) + (-997805) * (d 20) + (654183) * (d 21) + (470296) * (d 22) + (666643) * (d 23) + 1048576 + (z182 d) := by
  simp only [z214, z188_conservation] <;> ring

theorem z216_conservation (d : Digits) : z216 d = (d 12) + (-683901) * (d 19) + (136657) * (d 20) + (-997805) * (d 21) + (654183) * (d 22) + (470296) * (d 23) + (-2097152) * (z191 d) + (z215 d) := by
  simp only [z216, z197_conservation] <;> ring

theorem z217_conservation (d : Digits) : z217 d = (2097152) * (z215 d) := by
  have h : z217 d = 2097152 * z215 d := by
    rw [z217, m217, z215]
    have he := Int.emod_add_ediv_mul (z214 d) 2097152
    omega
  simp only [h] <;> ring

theorem z218_conservation (d : Digits) : z218 d = (d 11) + (-683901) * (d 18) + (136657) * (d 19) + (-997805) * (d 20) + (654183) * (d 21) + (470296) * (d 22) + (666643) * (d 23) + (z182 d) + (-2097152) * (z215 d) := by
  simp only [z218, z188_conservation, z217_conservation] <;> ring

theorem z219_conservation (d : Digits) : z219 d = (d 13) + (-683901) * (d 20) + (136657) * (d 21) + (-997805) * (d 22) + (654183) * (d 23) + 1048576 + (z191 d) := by
  simp only [z219, z195_conservation] <;> ring

theorem z221_conservation (d : Digits) : z221 d = (d 14) + (-683901) * (d 21) + (136657) * (d 22) + (-997805) * (d 23) + (-2097152) * (z199 d) + (z220 d) := by
  simp only [z221, z202_conservation] <;> ring

theorem z222_conservation (d : Digits) : z222 d = (2097152) * (z220 d) := by
  have h : z222 d = 2097152 * z220 d := by
    rw [z222, m222, z220]
    have he := Int.emod_add_ediv_mul (z219 d) 2097152
    omega
  simp only [h] <;> ring

theorem z223_conservation (d : Digits) : z223 d = (d 13) + (-683901) * (d 20) + (136657) * (d 21) + (-997805) * (d 22) + (654183) * (d 23) + (z191 d) + (-2097152) * (z220 d) := by
  simp only [z223, z195_conservation, z222_conservation] <;> ring

theorem z224_conservation (d : Digits) : z224 d = (d 15) + (-683901) * (d 22) + (136657) * (d 23) + 1048576 + (z199 d) := by
  simp only [z224, z200_conservation] <;> ring

theorem z226_conservation (d : Digits) : z226 d = (d 16) + (-683901) * (d 23) + (-2097152) * (z204 d) + (z225 d) := by
  simp only [z226, z207_conservation] <;> ring

theorem z227_conservation (d : Digits) : z227 d = (2097152) * (z225 d) := by
  have h : z227 d = 2097152 * z225 d := by
    rw [z227, m227, z225]
    have he := Int.emod_add_ediv_mul (z224 d) 2097152
    omega
  simp only [h] <;> ring

theorem z228_conservation (d : Digits) : z228 d = (d 15) + (-683901) * (d 22) + (136657) * (d 23) + (z199 d) + (-2097152) * (z225 d) := by
  simp only [z228, z200_conservation, z227_conservation] <;> ring

end Firedancer.Common.ScalarArithmetic.IntegerRegisters
