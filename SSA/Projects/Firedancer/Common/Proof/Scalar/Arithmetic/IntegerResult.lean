import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.IntegerConservation5

/-! Universal arithmetic correctness of the source-aligned integer schedule.
LLVM flag safety, input extraction, and final bit packing are separate bridges. -/

namespace Firedancer.Common.ScalarArithmetic.IntegerRegisters
set_option maxHeartbeats 2000000

def inputValue (d : Digits) : Int :=
  1 * d 0 +
    2097152 * d 1 +
    4398046511104 * d 2 +
    9223372036854775808 * d 3 +
    19342813113834066795298816 * d 4 +
    40564819207303340847894502572032 * d 5 +
    85070591730234615865843651857942052864 * d 6 +
    178405961588244985132285746181186892047843328 * d 7 +
    374144419156711147060143317175368453031918731001856 * d 8 +
    784637716923335095479473677900958302012794430558004314112 * d 9 +
    1645504557321206042154969182557350504982735865633579863348609024 * d 10 +
    3450873173395281893717377931138512726225554486085193277581262111899648 * d 11 +
    7237005577332262213973186563042994240829374041602535252466099000494570602496 * d 12 +
    15177100720513508366558296147058741458143803430094840009779784451085189728165691392 * d 13 +
    31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584 * d 14 +
    66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768 * d 15 +
    139984046386112763159840142535527767382602843577165595931249318810236991948760059086304843329475444736 * d 16 +
    293567822846729153486185074598667128421960318613539983838411371441526128139326055432962374798096087878991872 * d 17 +
    615656346818663737691860001564743965704370926101022604186692084441339402679643915803347910232576806887603562348544 * d 18 +
    1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688 * d 19 +
    2707685248164858261307045101702230179137145581421695874189921465443966120903931272499975005961073806735733604454495675614232576 * d 20 +
    5678427533559428832416592249125035424637823130369672345949142181098744438385921275985867583701277855943457200048954515105739075223552 * d 21 +
    11908525658859223294760121268437066290850060053501019099651935423375594096449911575776314174894302258147533153997065059263030913083222523904 * d 22 +
    24973988402527937851052777838345330445988785141319769206873255677002973910558124960962448824507935769278615448971252983163583805434306282450321408 * d 23

def middleValue (d : Digits) : Int :=
  1 * z361 d +
    2097152 * z369 d +
    4398046511104 * z374 d +
    9223372036854775808 * z379 d +
    19342813113834066795298816 * z384 d +
    40564819207303340847894502572032 * z389 d +
    85070591730234615865843651857942052864 * z344 d +
    178405961588244985132285746181186892047843328 * z350 d +
    374144419156711147060143317175368453031918731001856 * z348 d +
    784637716923335095479473677900958302012794430558004314112 * z355 d +
    1645504557321206042154969182557350504982735865633579863348609024 * z353 d +
    3450873173395281893717377931138512726225554486085193277581262111899648 * z359 d

def lowValue (d : Digits) : Int :=
  1 * z371 d +
    2097152 * z376 d +
    4398046511104 * z381 d +
    9223372036854775808 * z386 d +
    19342813113834066795298816 * z391 d +
    40564819207303340847894502572032 * z394 d +
    85070591730234615865843651857942052864 * z397 d +
    178405961588244985132285746181186892047843328 * z400 d +
    374144419156711147060143317175368453031918731001856 * z403 d +
    784637716923335095479473677900958302012794430558004314112 * z406 d +
    1645504557321206042154969182557350504982735865633579863348609024 * z409 d +
    3450873173395281893717377931138512726225554486085193277581262111899648 * z411 d

def outputValue (d : Digits) : Int :=
  1 * z426 d +
    2097152 * (z425 d % 2097152) +
    4398046511104 * (z428 d % 2097152) +
    9223372036854775808 * (z430 d % 2097152) +
    19342813113834066795298816 * (z432 d % 2097152) +
    40564819207303340847894502572032 * (z434 d % 2097152) +
    85070591730234615865843651857942052864 * (z436 d % 2097152) +
    178405961588244985132285746181186892047843328 * (z438 d % 2097152) +
    374144419156711147060143317175368453031918731001856 * (z440 d % 2097152) +
    784637716923335095479473677900958302012794430558004314112 * (z442 d % 2097152) +
    1645504557321206042154969182557350504982735865633579863348609024 * (z444 d % 2097152) +
    3450873173395281893717377931138512726225554486085193277581262111899648 * z446 d

def foldQuotient (d : Digits) : Int :=
  (d 12) + (2097152) * (d 13) + (4398046511104) * (d 14) + (9223372036854775808) * (d 15) + (19342813113834066795298816) * (d 16) + (40564819207303340847894502572032) * (d 17) + (85070591730234615865843651857942052864) * (d 18) + (178405961588244985132285746181186892047159427) * (d 19) + (374144419156711147060143317175368453030484486788561) * (d 20) + (784637716923335095479473677900958302009786602437603280467) * (d 21) + (1645504557321206042154969182557350504976427992875224594838584167) * (d 22) + (3450873173395281893717377931138512726212325918114263009514926463462680) * (d 23) + (z215 d) + (z357 d)

theorem middle_identity (d : Digits) :
    middleValue d = inputValue d - foldQuotient d * (groupOrder : Int) := by
  simp only [middleValue, inputValue, foldQuotient, z361_conservation, z369_conservation, z374_conservation, z379_conservation, z384_conservation, z389_conservation, z344_conservation, z350_conservation, z348_conservation, z355_conservation, z353_conservation, z359_conservation]
  norm_num [groupOrder]
  ring

theorem first_carry_identity (d : Digits) :
    middleValue d = lowValue d + 7237005577332262213973186563042994240829374041602535252466099000494570602496 * z410 d := by
  simp only [middleValue, lowValue, z361_conservation, z369_conservation, z374_conservation, z379_conservation, z384_conservation, z389_conservation, z344_conservation, z350_conservation, z348_conservation, z355_conservation, z353_conservation, z359_conservation, z371_conservation, z376_conservation, z381_conservation, z386_conservation, z391_conservation, z394_conservation, z397_conservation, z400_conservation, z403_conservation, z406_conservation, z409_conservation, z411_conservation]
  ring

theorem middle_bounds (d : Digits) (hd : Bounded d) :
    (-7237005577332262213973186563042994240829374041602535252466099000494570602496 : Int) ≤ middleValue d ∧ middleValue d < 7237005577332262213973186563042994240829374041602535252466099000494570602496 := by
  have h361 := z361_bounds d hd
  have h369 := z369_bounds d hd
  have h374 := z374_bounds d hd
  have h379 := z379_bounds d hd
  have h384 := z384_bounds d hd
  have h389 := z389_bounds d hd
  have h344 := z344_bounds d hd
  have h350 := z350_bounds d hd
  have h348 := z348_bounds d hd
  have h355 := z355_bounds d hd
  have h353 := z353_bounds d hd
  have h359 := z359_bounds d hd
  unfold middleValue
  omega

theorem low_bounds (d : Digits) (hd : Bounded d) :
    (0 : Int) ≤ lowValue d ∧ lowValue d < 7237005577332262213973186563042994240829374041602535252466099000494570602496 := by
  have h371 := z371_bounds d hd
  have h376 := z376_bounds d hd
  have h381 := z381_bounds d hd
  have h386 := z386_bounds d hd
  have h391 := z391_bounds d hd
  have h394 := z394_bounds d hd
  have h397 := z397_bounds d hd
  have h400 := z400_bounds d hd
  have h403 := z403_bounds d hd
  have h406 := z406_bounds d hd
  have h409 := z409_bounds d hd
  have h411 := z411_bounds d hd
  unfold lowValue
  omega

theorem last_carry_quotient (d : Digits) (hd : Bounded d) :
    z410 d = middleValue d / 7237005577332262213973186563042994240829374041602535252466099000494570602496 := by
  have h := first_carry_identity d
  have hl := low_bounds d hd
  omega

theorem output_identity (d : Digits) :
    outputValue d = middleValue d - z410 d * (groupOrder : Int) := by
  have h425 : z425 d % 2097152 = z425 d - 2097152 * z427 d := by
    rw [z427]
    have h := Int.emod_add_ediv_mul (z425 d) 2097152
    omega
  have h428 : z428 d % 2097152 = z428 d - 2097152 * z429 d := by
    rw [z429]
    have h := Int.emod_add_ediv_mul (z428 d) 2097152
    omega
  have h430 : z430 d % 2097152 = z430 d - 2097152 * z431 d := by
    rw [z431]
    have h := Int.emod_add_ediv_mul (z430 d) 2097152
    omega
  have h432 : z432 d % 2097152 = z432 d - 2097152 * z433 d := by
    rw [z433]
    have h := Int.emod_add_ediv_mul (z432 d) 2097152
    omega
  have h434 : z434 d % 2097152 = z434 d - 2097152 * z435 d := by
    rw [z435]
    have h := Int.emod_add_ediv_mul (z434 d) 2097152
    omega
  have h436 : z436 d % 2097152 = z436 d - 2097152 * z437 d := by
    rw [z437]
    have h := Int.emod_add_ediv_mul (z436 d) 2097152
    omega
  have h438 : z438 d % 2097152 = z438 d - 2097152 * z439 d := by
    rw [z439]
    have h := Int.emod_add_ediv_mul (z438 d) 2097152
    omega
  have h440 : z440 d % 2097152 = z440 d - 2097152 * z441 d := by
    rw [z441]
    have h := Int.emod_add_ediv_mul (z440 d) 2097152
    omega
  have h442 : z442 d % 2097152 = z442 d - 2097152 * z443 d := by
    rw [z443]
    have h := Int.emod_add_ediv_mul (z442 d) 2097152
    omega
  have h444 : z444 d % 2097152 = z444 d - 2097152 * z445 d := by
    rw [z445]
    have h := Int.emod_add_ediv_mul (z444 d) 2097152
    omega
  simp only [outputValue, middleValue, h425, h428, h430, h432, h434, h436, h438, h440, h442, h444]
  simp only [z344_conservation, z348_conservation, z350_conservation, z353_conservation, z355_conservation, z359_conservation, z361_conservation, z369_conservation, z374_conservation, z379_conservation, z384_conservation, z389_conservation, z425_conservation, z426_conservation, z428_conservation, z430_conservation, z432_conservation, z434_conservation, z436_conservation, z438_conservation, z440_conservation, z442_conservation, z444_conservation, z446_conservation]
  norm_num [groupOrder]
  ring

theorem output_eq_finalFold (d : Digits) (hd : Bounded d) :
    outputValue d = finalFold (middleValue d) := by
  rw [output_identity, finalFold_identity, last_carry_quotient d hd]
  rfl

theorem output_bounds (d : Digits) (hd : Bounded d) :
    0 ≤ outputValue d ∧ outputValue d < (groupOrder : Int) := by
  obtain ⟨hlo, hhi⟩ := middle_bounds d hd
  have h := finalFold_canonical (middleValue d) hlo hhi
  rw [output_eq_finalFold d hd]
  exact ⟨h.1, h.2.1⟩

/-- The whole integer schedule returns the canonical residue of all 24 input
digits, for every bounded digit vector. -/
theorem output_exact (d : Digits) (hd : Bounded d) :
    outputValue d = inputValue d % (groupOrder : Int) := by
  obtain ⟨hlo, hhi⟩ := middle_bounds d hd
  have h := (finalFold_canonical (middleValue d) hlo hhi).2.2
  rw [output_eq_finalFold d hd, h, middle_identity]
  simp [Int.sub_emod, Int.mul_emod]

end Firedancer.Common.ScalarArithmetic.IntegerRegisters
