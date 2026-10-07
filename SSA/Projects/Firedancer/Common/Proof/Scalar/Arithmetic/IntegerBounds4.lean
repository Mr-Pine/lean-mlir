import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.IntegerBounds3

/-! Checked linear identities and interval certificates for the corresponding
numbered source arithmetic registers. Generated equations are verified by
`ring` and `omega`; no external arithmetic result is trusted. -/

namespace Firedancer.Common.ScalarArithmetic.IntegerRegisters

set_option maxHeartbeats 2000000

attribute [local irreducible] z61 z63 z65 z67 z69 z71 z73 z75 z77 z79 z81 z83 z85 z87 z89 z91 z93 z95 z97 z99 z101 z103 z105 z106 z107 z108 z109 z110 z111 z112 z113 z114 z115 z116 z117 z118 z119 z120 z121 z122 z123 z124 z125 z126 z127 z128 z129 z130 z131 z132 z133 z134 z135 z136 z137 z138 z139 z140 z141 z142 z143 z144 z145 z146 z147 z148 z149 z150 z151 z152 z153 z154 z155 z156 z157 z158 z159 z160 z161 z162 z163 z164 z165 z166 z167 z168 z169 z170 z171 z172 z173 z174 z175 z176 z177 z178 z179 z180 z181 z182 z183 z184 z185 z186 z187 z188 z189 z190 z191 z192 z193 z194 z195 z196 z197 z198 z199 z200 z201 z202 z203 z204 z205 z206 z207 z208 z209 z210 z211 z212 z213 z214 z215 z216 z217 z218 z219 z220 z221 z222 z223 z224 z225 z226 z227 z228 z229 z230 z231 z232 z233 z234 z235 z236 z237 z238 z239 z240 z241 z242 z243 z244 z245 z246 z247 z248 z249 z250 z251 z252 z253 z254 z255 z256 z257 z258 z259 z260 z261 z262 z263 z264 z265 z266 z267 z268 z269 z270 z271 z272 z273 z274 z275 z276 z277 z278 z279 z280 z281 z282 z283 z284 z285 z286 z287 z288 z289 z290 z291 z292 z293 z294 z295 z296 z297 z298 z299 z300 z301 z302 z303 z304 z305 z306 z307 z308 z309 z310 z311 z312 z313 z314 z315 z316 z317 z318 z319 z320 z321 z322 z323 z324 z325 z326 z327 z328 z329 z330 z331 z332 z333 z334 z335 z336 z337 z338 z339 z340 z341 z342 z343 z344 z345 z346 z347 z348 z349 z350 z351 z352 z353 z354 z355 z356 z357 z358 z359 z360 z361 z362 z363 z364 z365 z366 z367 z368 z369 z370 z371 z372 z373 z374 z375 z376 z377 z378 z379 z380 z381 z382 z383 z384 z385 z386 z387 z388 z389 z390 z391 z392 z393 z394 z395 z396 z397 z398 z399 z400 z401 z402 z403 z404 z405 z406 z407 z408 z409 z410 z411 z412 z413 z414 z415 z416 z417 z418 z419 z420 z421 z422 z423 z424 z425 z426 z427 z428 z429 z430 z431 z432 z433 z434 z435 z436 z437 z438 z439 z440 z441 z442 z443 z444 z445 z446 m170 m179 m189 m196 m201 m206 m210 m213 m217 m222 m227 m301 m306 m311 m321 m329 m334 m338 m341 m345 m349 m354 m358

theorem z367_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z367 d ∧ z367 d ≤ 9 := by
  have h := z361_bounds d hd
  rw [z367]
  omega

theorem z368_linear (d : Digits) : z368 d = (d 1) + (470296) * (m196 d) + (666643) * (m222 d) + -1192166948864 + (470296) * (z215 d) + (z299 d) + (470296) * (z357 d) := by
  simp only [z368, z362_linear, z300_linear] <;> ring

theorem z368_bounds (d : Digits) (hd : Bounded d) :
    (-1983067892038 : Int) ≤ z368 d ∧ z368 d ≤ 82046345047717 := by
  have h0 := hd 1
  norm_num at h0
  have h1 := m196_bounds d
  have h2 := m222_bounds d
  have h4 := z215_bounds d hd
  have h5 := z299_bounds d hd
  have h6 := z357_bounds d hd
  rw [z368_linear]
  omega

theorem z369_linear (d : Digits) : z369 d = (m338 d) + -1048576 + (470296) * (z357 d) := by
  simp only [z369, z368_linear, z338_linear] <;> ring

theorem z369_bounds (d : Digits) (hd : Bounded d) :
    (-1518872 : Int) ≤ z369 d ∧ z369 d ≤ 14216863 := by
  have h0 := m338_bounds d
  have h2 := z357_bounds d hd
  rw [z369_linear]
  omega

theorem z370_linear (d : Digits) : z370 d = (m338 d) + -1048576 + (470296) * (z357 d) + (z367 d) := by
  simp only [z370, z369_linear] <;> ring

theorem z370_bounds (d : Digits) (hd : Bounded d) :
    (-1518873 : Int) ≤ z370 d ∧ z370 d ≤ 14216872 := by
  have h0 := m338_bounds d
  have h2 := z357_bounds d hd
  have h3 := z367_bounds d hd
  rw [z370_linear]
  omega

theorem z371_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z371 d ∧ z371 d ≤ 2097151 := by
  rw [z371]
  omega

theorem z372_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z372 d ∧ z372 d ≤ 6 := by
  have h := z370_bounds d hd
  rw [z372]
  omega

theorem z373_linear (d : Digits) : z373 d = (m306 d) + -1048576 + (654183) * (z357 d) := by
  simp only [z373, z307_linear, z363_linear] <;> ring

theorem z373_bounds (d : Digits) (hd : Bounded d) :
    (-1702759 : Int) ≤ z373 d ∧ z373 d ≤ 19365699 := by
  have h0 := m306_bounds d
  have h2 := z357_bounds d hd
  rw [z373_linear]
  omega

theorem z374_linear (d : Digits) : z374 d = (m306 d) + -1048576 + (z337 d) + (654183) * (z357 d) := by
  simp only [z374, z373_linear] <;> ring

theorem z374_bounds (d : Digits) (hd : Bounded d) :
    (-2648359 : Int) ≤ z374 d ∧ z374 d ≤ 58488439 := by
  have h0 := m306_bounds d
  have h2 := z337_bounds d hd
  have h3 := z357_bounds d hd
  rw [z374_linear]
  omega

theorem z375_linear (d : Digits) : z375 d = (m306 d) + -1048576 + (z337 d) + (654183) * (z357 d) + (z372 d) := by
  simp only [z375, z374_linear] <;> ring

theorem z375_bounds (d : Digits) (hd : Bounded d) :
    (-2648360 : Int) ≤ z375 d ∧ z375 d ≤ 58488445 := by
  have h0 := m306_bounds d
  have h2 := z337_bounds d hd
  have h3 := z357_bounds d hd
  have h4 := z372_bounds d hd
  rw [z375_linear]
  omega

theorem z376_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z376 d ∧ z376 d ≤ 2097151 := by
  rw [z376]
  omega

theorem z377_bounds (d : Digits) (hd : Bounded d) :
    (-2 : Int) ≤ z377 d ∧ z377 d ≤ 27 := by
  have h := z375_bounds d hd
  rw [z377]
  omega

theorem z378_linear (d : Digits) : z378 d = (d 3) + (-997805) * (m196 d) + (470296) * (m201 d) + (654183) * (m222 d) + (666643) * (m227 d) + -831853166592 + (-997805) * (z215 d) + (470296) * (z220 d) + (z304 d) + (-997805) * (z357 d) := by
  simp only [z378, z305_linear, z364_linear] <;> ring

theorem z378_bounds (d : Digits) (hd : Bounded d) :
    (-175259707188119 : Int) ≤ z378 d ∧ z378 d ≤ 83427692129499 := by
  have h0 := hd 3
  norm_num at h0
  have h1 := m196_bounds d
  have h2 := m201_bounds d
  have h3 := m222_bounds d
  have h4 := m227_bounds d
  have h6 := z215_bounds d hd
  have h7 := z220_bounds d hd
  have h8 := z304_bounds d hd
  have h9 := z357_bounds d hd
  rw [z378_linear]
  omega

theorem z379_linear (d : Digits) : z379 d = (m341 d) + -1048576 + (-997805) * (z357 d) := by
  simp only [z379, z378_linear, z341_linear] <;> ring

theorem z379_bounds (d : Digits) (hd : Bounded d) :
    (-28987116 : Int) ≤ z379 d ∧ z379 d ≤ 2046380 := by
  have h0 := m341_bounds d
  have h2 := z357_bounds d hd
  rw [z379_linear]
  omega

theorem z380_linear (d : Digits) : z380 d = (m341 d) + -1048576 + (-997805) * (z357 d) + (z377 d) := by
  simp only [z380, z379_linear] <;> ring

theorem z380_bounds (d : Digits) (hd : Bounded d) :
    (-28987118 : Int) ≤ z380 d ∧ z380 d ≤ 2046407 := by
  have h0 := m341_bounds d
  have h2 := z357_bounds d hd
  have h3 := z377_bounds d hd
  rw [z380_linear]
  omega

theorem z381_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z381 d ∧ z381 d ≤ 2097151 := by
  rw [z381]
  omega

theorem z382_bounds (d : Digits) (hd : Bounded d) :
    (-14 : Int) ≤ z382 d ∧ z382 d ≤ 0 := by
  have h := z380_bounds d hd
  rw [z382]
  omega

theorem z383_linear (d : Digits) : z383 d = (m311 d) + -1048576 + (136657) * (z357 d) := by
  simp only [z383, z312_linear, z365_linear] <;> ring

theorem z383_bounds (d : Digits) (hd : Bounded d) :
    (-1185233 : Int) ≤ z383 d ∧ z383 d ≤ 4874971 := by
  have h0 := m311_bounds d
  have h2 := z357_bounds d hd
  rw [z383_linear]
  omega

theorem z384_linear (d : Digits) : z384 d = (m311 d) + -1048576 + (z340 d) + (136657) * (z357 d) := by
  simp only [z384, z383_linear] <;> ring

theorem z384_bounds (d : Digits) (hd : Bounded d) :
    (-84755560 : Int) ≤ z384 d ∧ z384 d ≤ 44656394 := by
  have h0 := m311_bounds d
  have h2 := z340_bounds d hd
  have h3 := z357_bounds d hd
  rw [z384_linear]
  omega

theorem z385_linear (d : Digits) : z385 d = (m311 d) + -1048576 + (z340 d) + (136657) * (z357 d) + (z382 d) := by
  simp only [z385, z384_linear] <;> ring

theorem z385_bounds (d : Digits) (hd : Bounded d) :
    (-84755574 : Int) ≤ z385 d ∧ z385 d ≤ 44656394 := by
  have h0 := m311_bounds d
  have h2 := z340_bounds d hd
  have h3 := z357_bounds d hd
  have h4 := z382_bounds d hd
  rw [z385_linear]
  omega

theorem z386_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z386 d ∧ z386 d ≤ 2097151 := by
  rw [z386]
  omega

theorem z387_bounds (d : Digits) (hd : Bounded d) :
    (-41 : Int) ≤ z387 d ∧ z387 d ≤ 21 := by
  have h := z385_bounds d hd
  rw [z387]
  omega

theorem z388_linear (d : Digits) : z388 d = (666643) * (d 17) + (d 5) + (-683901) * (m196 d) + (-997805) * (m201 d) + (470296) * (m206 d) + (136657) * (m222 d) + (654183) * (m227 d) + 440999608320 + (666643) * (z204 d) + (-683901) * (z215 d) + (-997805) * (z220 d) + (470296) * (z225 d) + (z309 d) + (-683901) * (z357 d) := by
  simp only [z388, z310_linear, z366_linear] <;> ring

theorem z388_bounds (d : Digits) (hd : Bounded d) :
    (-404939584753993 : Int) ≤ z388 d ∧ z388 d ≤ 23764983885037 := by
  have h0 := hd 17
  norm_num at h0
  have h1 := hd 5
  norm_num at h1
  have h2 := m196_bounds d
  have h3 := m201_bounds d
  have h4 := m206_bounds d
  have h5 := m222_bounds d
  have h6 := m227_bounds d
  have h8 := z204_bounds d hd
  have h9 := z215_bounds d hd
  have h10 := z220_bounds d hd
  have h11 := z225_bounds d hd
  have h12 := z309_bounds d hd
  have h13 := z357_bounds d hd
  rw [z388_linear]
  omega

theorem z389_linear (d : Digits) : z389 d = (m345 d) + -1048576 + (-683901) * (z357 d) := by
  simp only [z389, z388_linear, z345_linear] <;> ring

theorem z389_bounds (d : Digits) (hd : Bounded d) :
    (-20197804 : Int) ≤ z389 d ∧ z389 d ≤ 1732476 := by
  have h0 := m345_bounds d
  have h2 := z357_bounds d hd
  rw [z389_linear]
  omega

theorem z390_linear (d : Digits) : z390 d = (m345 d) + -1048576 + (-683901) * (z357 d) + (z387 d) := by
  simp only [z390, z389_linear] <;> ring

theorem z390_bounds (d : Digits) (hd : Bounded d) :
    (-20197845 : Int) ≤ z390 d ∧ z390 d ≤ 1732497 := by
  have h0 := m345_bounds d
  have h2 := z357_bounds d hd
  have h3 := z387_bounds d hd
  rw [z390_linear]
  omega

theorem z391_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z391 d ∧ z391 d ≤ 2097151 := by
  rw [z391]
  omega

theorem z392_bounds (d : Digits) (hd : Bounded d) :
    (-10 : Int) ≤ z392 d ∧ z392 d ≤ 0 := by
  have h := z390_bounds d hd
  rw [z392]
  omega

theorem z393_linear (d : Digits) : z393 d = (m321 d) + -1048576 + (z343 d) + (z392 d) := by
  simp only [z393, z344_linear] <;> ring

theorem z393_bounds (d : Digits) (hd : Bounded d) :
    (-194138818 : Int) ≤ z393 d ∧ z393 d ≤ 12380602 := by
  have h0 := m321_bounds d
  have h2 := z343_bounds d hd
  have h3 := z392_bounds d hd
  rw [z393_linear]
  omega

theorem z394_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z394 d ∧ z394 d ≤ 2097151 := by
  rw [z394]
  omega

theorem z395_bounds (d : Digits) (hd : Bounded d) :
    (-93 : Int) ≤ z395 d ∧ z395 d ≤ 5 := by
  have h := z393_bounds d hd
  rw [z395]
  omega

theorem z396_linear (d : Digits) : z396 d = (m349 d) + -1048576 + (z395 d) := by
  simp only [z396, z350_linear] <;> ring

theorem z396_bounds (d : Digits) (hd : Bounded d) :
    (-1048669 : Int) ≤ z396 d ∧ z396 d ≤ 1048580 := by
  have h0 := m349_bounds d
  have h2 := z395_bounds d hd
  rw [z396_linear]
  omega

theorem z397_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z397 d ∧ z397 d ≤ 2097151 := by
  rw [z397]
  omega

theorem z398_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z398 d ∧ z398 d ≤ 0 := by
  have h := z396_bounds d hd
  rw [z398]
  omega

theorem z399_linear (d : Digits) : z399 d = (m329 d) + -1048576 + (z347 d) + (z398 d) := by
  simp only [z399, z348_linear] <;> ring

theorem z399_bounds (d : Digits) (hd : Bounded d) :
    (-127875147 : Int) ≤ z399 d ∧ z399 d ≤ 3485823 := by
  have h0 := m329_bounds d
  have h2 := z347_bounds d hd
  have h3 := z398_bounds d hd
  rw [z399_linear]
  omega

theorem z400_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z400 d ∧ z400 d ≤ 2097151 := by
  rw [z400]
  omega

theorem z401_bounds (d : Digits) (hd : Bounded d) :
    (-61 : Int) ≤ z401 d ∧ z401 d ≤ 1 := by
  have h := z399_bounds d hd
  rw [z401]
  omega

theorem z402_linear (d : Digits) : z402 d = (m354 d) + -1048576 + (z401 d) := by
  simp only [z402, z355_linear] <;> ring

theorem z402_bounds (d : Digits) (hd : Bounded d) :
    (-1048637 : Int) ≤ z402 d ∧ z402 d ≤ 1048576 := by
  have h0 := m354_bounds d
  have h2 := z401_bounds d hd
  rw [z402_linear]
  omega

theorem z403_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z403 d ∧ z403 d ≤ 2097151 := by
  rw [z403]
  omega

theorem z404_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z404 d ∧ z404 d ≤ 0 := by
  have h := z402_bounds d hd
  rw [z404]
  omega

theorem z405_linear (d : Digits) : z405 d = (m334 d) + -1048576 + (z352 d) + (z404 d) := by
  simp only [z405, z353_linear] <;> ring

theorem z405_bounds (d : Digits) (hd : Bounded d) :
    (-24207877 : Int) ≤ z405 d ∧ z405 d ≤ 1750290 := by
  have h0 := m334_bounds d
  have h2 := z352_bounds d hd
  have h3 := z404_bounds d hd
  rw [z405_linear]
  omega

theorem z406_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z406 d ∧ z406 d ≤ 2097151 := by
  rw [z406]
  omega

theorem z407_bounds (d : Digits) (hd : Bounded d) :
    (-12 : Int) ≤ z407 d ∧ z407 d ≤ 0 := by
  have h := z405_bounds d hd
  rw [z407]
  omega

theorem z408_linear (d : Digits) : z408 d = (m358 d) + -1048576 + (z407 d) := by
  simp only [z408, z359_linear] <;> ring

theorem z408_bounds (d : Digits) (hd : Bounded d) :
    (-1048588 : Int) ≤ z408 d ∧ z408 d ≤ 1048575 := by
  have h0 := m358_bounds d
  have h2 := z407_bounds d hd
  rw [z408_linear]
  omega

theorem z409_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z409 d ∧ z409 d ≤ 2097151 := by
  rw [z409]
  omega

theorem z410_bounds (d : Digits) (hd : Bounded d) :
    (-1 : Int) ≤ z410 d ∧ z410 d ≤ 0 := by
  have h := z408_bounds d hd
  rw [z410]
  omega

theorem z411_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ z411 d ∧ z411 d ≤ 2097151 := by
  rw [z411]
  omega

end Firedancer.Common.ScalarArithmetic.IntegerRegisters
