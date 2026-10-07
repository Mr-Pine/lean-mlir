import SSA.Projects.Agave.Ed25519.Proof.Encoding.ToBytesCorrectness
import SSA.Projects.Agave.Ed25519.Proof.Encoding.ToBytesSafety
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.Encoding.Decompress.Execution.ToBytes
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
open Agave.Ed25519.Encoding.RIR

theorem masked_shift_1 (x : BitVec 64) :
    (((x &&& 2251799813685247#64) <<< 1).sshiftRight 1 = (x &&& 2251799813685247#64)) ∧
    (((x &&& 2251799813685247#64) <<< 1) >>> 1 = (x &&& 2251799813685247#64)) := by
  constructor
  · exact shift_signed_safe _ 1 2251799813685247 (and_nat_le_right _ _) (by decide)
  · exact shift_unsigned_safe _ 1 2251799813685247 (and_nat_le_right _ _) (by decide)

theorem masked_shift_3 (x : BitVec 64) :
    (((x &&& 2251799813685247#64) <<< 3).sshiftRight 3 = (x &&& 2251799813685247#64)) ∧
    (((x &&& 2251799813685247#64) <<< 3) >>> 3 = (x &&& 2251799813685247#64)) := by
  constructor
  · exact shift_signed_safe _ 3 2251799813685247 (and_nat_le_right _ _) (by decide)
  · exact shift_unsigned_safe _ 3 2251799813685247 (and_nat_le_right _ _) (by decide)

theorem masked_shift_4 (x : BitVec 64) :
    (((x &&& 2251799813685247#64) <<< 4).sshiftRight 4 = (x &&& 2251799813685247#64)) ∧
    (((x &&& 2251799813685247#64) <<< 4) >>> 4 = (x &&& 2251799813685247#64)) := by
  constructor
  · exact shift_signed_safe _ 4 2251799813685247 (and_nat_le_right _ _) (by decide)
  · exact shift_unsigned_safe _ 4 2251799813685247 (and_nat_le_right _ _) (by decide)

theorem masked_shift_6 (x : BitVec 64) :
    (((x &&& 2251799813685247#64) <<< 6).sshiftRight 6 = (x &&& 2251799813685247#64)) ∧
    (((x &&& 2251799813685247#64) <<< 6) >>> 6 = (x &&& 2251799813685247#64)) := by
  constructor
  · exact shift_signed_safe _ 6 2251799813685247 (and_nat_le_right _ _) (by decide)
  · exact shift_unsigned_safe _ 6 2251799813685247 (and_nat_le_right _ _) (by decide)

theorem boundary_disjoint_3 (x y : BitVec 64) :
    ((x &&& 2251799813685247#64) <<< 3) &&& ((y >>> 48) &&& 7#64) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_ofNat]

theorem boundary_disjoint_6 (x y : BitVec 64) :
    ((x &&& 2251799813685247#64) <<< 6) &&& ((y &&& 2251799813685247#64) >>> 45) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_ofNat]

theorem boundary_disjoint_1 (x y : BitVec 64) :
    ((x &&& 2251799813685247#64) <<< 1) &&& ((y &&& 2251799813685247#64) >>> 50) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_ofNat]

theorem boundary_disjoint_4 (x y : BitVec 64) :
    ((x &&& 2251799813685247#64) <<< 4) &&& ((y &&& 2251799813685247#64) >>> 47) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_ofNat]

theorem last_byte_trunc (x : BitVec 64) :
    (((x &&& 2251799813685247#64) >>> 44).setWidth 8).setWidth 64 =
      (x &&& 2251799813685247#64) >>> 44 ∧
    (((x &&& 2251799813685247#64) >>> 44).setWidth 8).signExtend 64 =
      (x &&& 2251799813685247#64) >>> 44 := by
  let v := (x &&& 2251799813685247#64) >>> 44
  have hb : v.toNat ≤ 127 := shiftRight_bound _ 44 2251799813685247 (and_nat_le_right _ _)
  have hn : (v.setWidth 8).toNat = v.toNat := by
    simp only [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by omega)
  have hz : (v.setWidth 8).setWidth 64 = v := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth_of_le (by decide), hn]
  have hm : (v.setWidth 8).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, hn]
    omega
  exact ⟨hz, by rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]; exact hz⟩

theorem masked_shift_1_signed (x : BitVec 64) :
    (((x &&& 2251799813685247#64) <<< 1).sshiftRight 1) = (x &&& 2251799813685247#64) :=
  (masked_shift_1 x).1

theorem masked_shift_1_unsigned (x : BitVec 64) :
    (((x &&& 2251799813685247#64) <<< 1) >>> 1) = (x &&& 2251799813685247#64) :=
  (masked_shift_1 x).2

theorem masked_shift_3_signed (x : BitVec 64) :
    (((x &&& 2251799813685247#64) <<< 3).sshiftRight 3) = (x &&& 2251799813685247#64) :=
  (masked_shift_3 x).1

theorem masked_shift_3_unsigned (x : BitVec 64) :
    (((x &&& 2251799813685247#64) <<< 3) >>> 3) = (x &&& 2251799813685247#64) :=
  (masked_shift_3 x).2

theorem masked_shift_4_signed (x : BitVec 64) :
    (((x &&& 2251799813685247#64) <<< 4).sshiftRight 4) = (x &&& 2251799813685247#64) :=
  (masked_shift_4 x).1

theorem masked_shift_4_unsigned (x : BitVec 64) :
    (((x &&& 2251799813685247#64) <<< 4) >>> 4) = (x &&& 2251799813685247#64) :=
  (masked_shift_4 x).2

theorem masked_shift_6_signed (x : BitVec 64) :
    (((x &&& 2251799813685247#64) <<< 6).sshiftRight 6) = (x &&& 2251799813685247#64) :=
  (masked_shift_6 x).1

theorem masked_shift_6_unsigned (x : BitVec 64) :
    (((x &&& 2251799813685247#64) <<< 6) >>> 6) = (x &&& 2251799813685247#64) :=
  (masked_shift_6 x).2

theorem last_byte_trunc_unsigned (x : BitVec 64) :
    (((x &&& 2251799813685247#64) >>> 44).setWidth 8).setWidth 64 =
      (x &&& 2251799813685247#64) >>> 44 := (last_byte_trunc x).1

theorem last_byte_trunc_signed (x : BitVec 64) :
    (((x &&& 2251799813685247#64) >>> 44).setWidth 8).signExtend 64 =
      (x &&& 2251799813685247#64) >>> 44 := (last_byte_trunc x).2

/-- The compiler's carry order with the carry as the left addition operand. -/
def reverseCarry (w : Fin 5 → BitVec 64) (extra : BitVec 64) : Fin 5 → BitVec 64 :=
  let t0 := extra + w 0
  let t1 := (t0 >>> 51) + w 1
  let t2 := (t1 >>> 51) + w 2
  let t3 := (t2 >>> 51) + w 3
  let t4 := (t3 >>> 51) + w 4
  ![t0, t1, t2, t3, t4]

def quotientCarry (w : Fin 5 → BitVec 64) : Fin 5 → BitVec 64 :=
  let t0 := w 0 + 19
  let t1 := (t0 >>> 51) + w 1
  let t2 := (t1 >>> 51) + w 2
  let t3 := (t2 >>> 51) + w 3
  let t4 := (t3 >>> 51) + w 4
  ![t0, t1, t2, t3, t4]

theorem reverseCarry_eq (w : Fin 5 → BitVec 64) (extra : BitVec 64) :
    reverseCarry w extra = carriedWord w extra := by
  unfold reverseCarry carriedWord
  simp only [BitVec.add_comm]

theorem quotientCarry_eq (w : Fin 5 → BitVec 64) : quotientCarry w = carriedWord w 19 := by
  unfold quotientCarry carriedWord
  simp only [BitVec.add_comm]

/-- Exact carry schedule of the imported serializer, before its stores. -/
def carryMachine (a : Fin 5 → BitVec 64) : Fin 5 → BitVec 64 :=
  reverseCarry (weakWord a) ((quotientCarry (weakWord a) 4 >>> 51) * 19)

/-- Byte projections of the carried words, in emitted store order. -/
def rawBytes (c : Fin 5 → BitVec 64) : Fin 32 → BitVec 8 :=
  let v81 := c 0
  let v83 := c 1
  let v85 := c 2
  let v88 := c 3
  let v91 := c 4
  let v86 := v83 &&& 2251799813685247
  let v89 := v85 &&& 2251799813685247
  let v92 := v88 &&& 2251799813685247
  let v93 := v91 &&& 2251799813685247
  let v94 := v81.setWidth 8
  let v95 := v81 >>> 8
  let v97 := v95.setWidth 8
  let v98 := v81 >>> 16
  let v100 := v98.setWidth 8
  let v101 := v81 >>> 24
  let v103 := v101.setWidth 8
  let v104 := v81 >>> 32
  let v106 := v104.setWidth 8
  let v107 := v81 >>> 40
  let v109 := v107.setWidth 8
  let v110 := v81 >>> 48
  let v111 := v110 &&& 7#64
  let v112 := v86 <<< 3
  let v113 := v112 ||| v111
  let v115 := v113.setWidth 8
  let v116 := v83 >>> 5
  let v118 := v116.setWidth 8
  let v119 := v83 >>> 13
  let v121 := v119.setWidth 8
  let v122 := v83 >>> 21
  let v124 := v122.setWidth 8
  let v125 := v83 >>> 29
  let v127 := v125.setWidth 8
  let v128 := v83 >>> 37
  let v130 := v128.setWidth 8
  let v131 := v86 >>> 45
  let v132 := v89 <<< 6
  let v133 := v132 ||| v131
  let v135 := v133.setWidth 8
  let v136 := v85 >>> 2
  let v138 := v136.setWidth 8
  let v139 := v85 >>> 10
  let v141 := v139.setWidth 8
  let v142 := v85 >>> 18
  let v144 := v142.setWidth 8
  let v145 := v85 >>> 26
  let v147 := v145.setWidth 8
  let v148 := v85 >>> 34
  let v150 := v148.setWidth 8
  let v151 := v85 >>> 42
  let v153 := v151.setWidth 8
  let v154 := v89 >>> 50
  let v155 := v92 <<< 1
  let v156 := v155 ||| v154
  let v158 := v156.setWidth 8
  let v159 := v88 >>> 7
  let v161 := v159.setWidth 8
  let v162 := v88 >>> 15
  let v164 := v162.setWidth 8
  let v165 := v88 >>> 23
  let v167 := v165.setWidth 8
  let v168 := v88 >>> 31
  let v170 := v168.setWidth 8
  let v171 := v88 >>> 39
  let v173 := v171.setWidth 8
  let v174 := v92 >>> 47
  let v175 := v93 <<< 4
  let v176 := v175 ||| v174
  let v178 := v176.setWidth 8
  let v179 := v91 >>> 4
  let v181 := v179.setWidth 8
  let v182 := v91 >>> 12
  let v184 := v182.setWidth 8
  let v185 := v91 >>> 20
  let v187 := v185.setWidth 8
  let v188 := v91 >>> 28
  let v190 := v188.setWidth 8
  let v191 := v91 >>> 36
  let v193 := v191.setWidth 8
  let v194 := v93 >>> 44
  let v196 := v194.setWidth 8
  ![v94, v97, v100, v103, v106, v109, v115, v118, v121, v124, v127, v130, v135, v138, v141, v144, v147, v150, v153, v158, v161, v164, v167, v170, v173, v178, v181, v184, v187, v190, v193, v196]

/-- Exact byte-store values of the imported field_to_bytes region. -/
def machine (a : Fin 5 → BitVec 64) : Fin 32 → BitVec 8 := rawBytes (carryMachine a)

/-- Little-endian byte slices of five carried 51-bit limbs. -/
def emittedBytes (c : Fin 5 → BitVec 64) : Fin 32 → BitVec 8 :=
  ![(c 0 >>> 0).setWidth 8,
    (c 0 >>> 8).setWidth 8,
    (c 0 >>> 16).setWidth 8,
    (c 0 >>> 24).setWidth 8,
    (c 0 >>> 32).setWidth 8,
    (c 0 >>> 40).setWidth 8,
    (((c 0 >>> 48) &&& 7) ||| ((c 1 &&& 2251799813685247) <<< 3)).setWidth 8,
    (c 1 >>> 5).setWidth 8,
    (c 1 >>> 13).setWidth 8,
    (c 1 >>> 21).setWidth 8,
    (c 1 >>> 29).setWidth 8,
    (c 1 >>> 37).setWidth 8,
    (((c 1 >>> 45) &&& 63) ||| ((c 2 &&& 2251799813685247) <<< 6)).setWidth 8,
    (c 2 >>> 2).setWidth 8,
    (c 2 >>> 10).setWidth 8,
    (c 2 >>> 18).setWidth 8,
    (c 2 >>> 26).setWidth 8,
    (c 2 >>> 34).setWidth 8,
    (c 2 >>> 42).setWidth 8,
    (((c 2 >>> 50) &&& 1) ||| ((c 3 &&& 2251799813685247) <<< 1)).setWidth 8,
    (c 3 >>> 7).setWidth 8,
    (c 3 >>> 15).setWidth 8,
    (c 3 >>> 23).setWidth 8,
    (c 3 >>> 31).setWidth 8,
    (c 3 >>> 39).setWidth 8,
    (((c 3 >>> 47) &&& 15) ||| ((c 4 &&& 2251799813685247) <<< 4)).setWidth 8,
    (c 4 >>> 4).setWidth 8,
    (c 4 >>> 12).setWidth 8,
    (c 4 >>> 20).setWidth 8,
    (c 4 >>> 28).setWidth 8,
    (c 4 >>> 36).setWidth 8,
    ( (c 4 &&& 2251799813685247) >>> 44).setWidth 8]

set_option maxHeartbeats 2000000 in
theorem emittedBytes_pack (c : Fin 5 → BitVec 64) (i : Fin 32) :
    emittedBytes c i =
      (packedBytes (fun j => (c j).setWidth 51)).extractLsb' (8 * i.val) 8 := by
  rw [packedBytes_eq]
  fin_cases i <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;>
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] <;>
    interval_cases j <;>
    simp [emittedBytes, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
      BitVec.getLsbD_append, BitVec.getElem_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_ofNat, ← BitVec.getLsbD_eq_getElem, BitVec.or_comm, Nat.testBit]

theorem carryMachine_schedule (a : Fin 5 → BitVec 64) :
    carryMachine a = carriedWord (weakWord a) (19 * quotientWord a) := by
  rw [carryMachine, quotientCarry_eq, reverseCarry_eq, BitVec.mul_comm]
  rfl

set_option maxHeartbeats 2000000 in
theorem rawBytes_emitted (c : Fin 5 → BitVec 64) : rawBytes c = emittedBytes c := by
  funext i
  fin_cases i <;> simp [rawBytes, emittedBytes, BitVec.or_comm] <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;> interval_cases j <;>
    simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, Bool.or_comm]

theorem machine_schedule (a : Fin 5 → BitVec 64) :
    machine a = emittedBytes (carriedWord (weakWord a) (19 * quotientWord a)) := by
  rw [machine, carryMachine_schedule, rawBytes_emitted]

/-- Every stored byte is the matching slice of the already proved canonical serializer. -/
theorem machine_canonical (a : Fin 5 → BitVec 64) (i : Fin 32) :
    machine a i = (packedBytes (tightWords a)).extractLsb' (8 * i.val) 8 := by
  rw [machine_schedule, emittedBytes_pack]
  rfl

def storeBytes (m : MemoryState) (r : Pointer) (v : Fin 32 → BitVec 8) : MemoryState :=
  ((((((((((((((((((((((((((((((((m).storeAt (r.add 0#64) (v 0)).storeAt (r.add 1#64) (v 1)).storeAt (r.add 2#64) (v 2)).storeAt (r.add 3#64) (v 3)).storeAt (r.add 4#64) (v 4)).storeAt (r.add 5#64) (v 5)).storeAt (r.add 6#64) (v 6)).storeAt (r.add 7#64) (v 7)).storeAt (r.add 8#64) (v 8)).storeAt (r.add 9#64) (v 9)).storeAt (r.add 10#64) (v 10)).storeAt (r.add 11#64) (v 11)).storeAt (r.add 12#64) (v 12)).storeAt (r.add 13#64) (v 13)).storeAt (r.add 14#64) (v 14)).storeAt (r.add 15#64) (v 15)).storeAt (r.add 16#64) (v 16)).storeAt (r.add 17#64) (v 17)).storeAt (r.add 18#64) (v 18)).storeAt (r.add 19#64) (v 19)).storeAt (r.add 20#64) (v 20)).storeAt (r.add 21#64) (v 21)).storeAt (r.add 22#64) (v 22)).storeAt (r.add 23#64) (v 23)).storeAt (r.add 24#64) (v 24)).storeAt (r.add 25#64) (v 25)).storeAt (r.add 26#64) (v 26)).storeAt (r.add 27#64) (v 27)).storeAt (r.add 28#64) (v 28)).storeAt (r.add 29#64) (v 29)).storeAt (r.add 30#64) (v 30)).storeAt (r.add 31#64) (v 31)

@[mlir_mem, mlir_transport]
theorem smallRange_storeBytes (h : SmallRange m p n) (r : Pointer) (v : Fin 32 → BitVec 8) :
    SmallRange (storeBytes m r v) p n := by
  unfold storeBytes
  repeat apply SmallRange.storeAt
  exact h

@[mlir_mem, mlir_transport]
theorem fits_storeBytes (h : Fits m p w) (r : Pointer) (v : Fin 32 → BitVec 8) :
    Fits (storeBytes m r v) p w := by
  unfold storeBytes
  repeat apply Fits.storeAt
  exact h

@[mlir_mem, mlir_transport]
theorem wf_storeBytes {s : GlobalState} (h : s.WF) (r : Pointer) (v : Fin 32 → BitVec 8) :
    ({ s with mem := storeBytes s.mem r v } : GlobalState).WF := by
  simpa only [storeBytes, GlobalState.WF_storeAt] using h

@[mlir_mem, mlir_read]
theorem readAt_storeBytes_of_ne (m : MemoryState) (r p : Pointer)
    (v : Fin 32 → BitVec 8) (w : Nat) (h : r.id ≠ p.id) :
    (storeBytes m r v).readAt p w = m.readAt p w := by
  have hrw (mem : MemoryState) (k : BitVec 64) (x : BitVec 8) :
      (mem.storeAt (r.add k) x).readAt p w = mem.readAt p w :=
    MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne (by
      simpa only [Pointer.add_id] using h)) x
  simp only [storeBytes, hrw]

theorem byte_disjoint (h : SmallRange m r 32) (i j : Nat)
    (hi : i < 32) (hj : j < 32) (hne : i ≠ j) :
    (Range.of (r.add (BitVec.ofNat 64 i)) 8).Disjoint
      (Range.of (r.add (BitVec.ofNat 64 j)) 8) := by
  have hi64 : i < 2^64 := by omega
  have hj64 : j < 2^64 := by omega
  have hiOff := Pointer.offsetInBits_add (h.no_wrap (k := i) (by omega))
  have hjOff := Pointer.offsetInBits_add (h.no_wrap (k := j) (by omega))
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] at hiOff
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64] at hjOff
  simp only [Range.Disjoint, Range.of, Pointer.add_id, hiOff, hjOff]
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Every byte reads back exactly after all 32 stores. -/
theorem storeBytes_readAt (m : MemoryState) (r : Pointer) (v : Fin 32 → BitVec 8)
    (h : SmallRange m r 32) (i : Fin 32) :
    (storeBytes m r v).readAt (r.add (BitVec.ofNat 64 i.val)) 8 = v i := by
  fin_cases i
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 16 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 15 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 14 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 13 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 12 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 11 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 10 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 9 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 8 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 7 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 6 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 5 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 4 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 3 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 2 0 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 1 0 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 0) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 16 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 15 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 14 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 13 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 12 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 11 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 10 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 9 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 8 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 7 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 6 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 5 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 4 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 3 1 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 2 1 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 1) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 16 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 15 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 14 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 13 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 12 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 11 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 10 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 9 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 8 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 7 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 6 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 5 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 4 2 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 3 2 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 2) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 16 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 15 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 14 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 13 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 12 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 11 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 10 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 9 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 8 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 7 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 6 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 5 3 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 4 3 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 3) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 16 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 15 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 14 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 13 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 12 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 11 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 10 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 9 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 8 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 7 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 6 4 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 5 4 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 4) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 16 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 15 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 14 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 13 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 12 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 11 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 10 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 9 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 8 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 7 5 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 6 5 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 5) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 16 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 15 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 14 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 13 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 12 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 11 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 10 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 9 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 8 6 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 7 6 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 6) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 16 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 15 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 14 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 13 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 12 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 11 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 10 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 9 7 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 8 7 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 7) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 16 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 15 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 14 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 13 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 12 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 11 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 10 8 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 9 8 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 8) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 16 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 15 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 14 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 13 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 12 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 11 9 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 10 9 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 9) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 16 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 15 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 14 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 13 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 12 10 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 11 10 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 10) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 16 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 15 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 14 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 13 11 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 12 11 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 11) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 16 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 15 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 14 12 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 13 12 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 12) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 16 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 15 13 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 14 13 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 13) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 14 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 14 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 14 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 14 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 14 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 14 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 14 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 14 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 14 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 14 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 14 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 14 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 14 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 14 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 14 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 16 14 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 15 14 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 14) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 15 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 15 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 15 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 15 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 15 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 15 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 15 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 15 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 15 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 15 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 15 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 15 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 15 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 15 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 15 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 16 15 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 15) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 16 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 16 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 16 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 16 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 16 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 16 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 16 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 16 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 16 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 16 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 16 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 16 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 16 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 16 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 17 16 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 16) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 17 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 17 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 17 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 17 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 17 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 17 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 17 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 17 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 17 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 17 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 17 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 17 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 17 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 18 17 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 17) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 18 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 18 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 18 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 18 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 18 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 18 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 18 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 18 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 18 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 18 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 18 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 18 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 19 18 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 18) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 19 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 19 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 19 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 19 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 19 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 19 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 19 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 19 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 19 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 19 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 19 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 20 19 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 19) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 20 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 20 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 20 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 20 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 20 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 20 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 20 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 20 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 20 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 20 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 21 20 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 20) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 21 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 21 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 21 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 21 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 21 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 21 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 21 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 21 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 21 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 22 21 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 21) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 22 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 22 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 22 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 22 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 22 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 22 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 22 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 22 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 23 22 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 22) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 23 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 23 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 23 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 23 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 23 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 23 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 23 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 24 23 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 23) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 24 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 24 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 24 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 24 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 24 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 24 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 25 24 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 24) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 25 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 25 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 25 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 25 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 25 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 26 25 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 25) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 26 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 26 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 26 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 26 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 27 26 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 26) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 27 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 27 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 27 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 28 27 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 27) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 28 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 28 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 29 28 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 28) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 29 (by decide) (by decide) (by decide))]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 30 29 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 29) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    rw [MemoryState.readAt_storeAt_disjoint (byte_disjoint h 31 30 (by decide) (by decide) (by decide))]
    have hf := h.fits_add (k := 30) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _
  · simp only [storeBytes]
    have hf := h.fits_add (k := 31) (count := 1) (by decide)
    exact MemoryState.readAt_storeAt_self hf.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt _

theorem storeBytes_smallRange (h : SmallRange m r 32) (v : Fin 32 → BitVec 8) :
    SmallRange (storeBytes m r v) r 32 := by
  unfold storeBytes
  repeat apply SmallRange.storeAt
  exact h

/-- The complete 32-byte output is the canonical field encoding. -/
theorem storeBytes_read256 (m : MemoryState) (r : Pointer) (a : Fin 5 → BitVec 64)
    (h : SmallRange m r 32) :
    (storeBytes m r (machine a)).readAt r 256 = packedBytes (tightWords a) := by
  have hs := storeBytes_smallRange h (machine a)
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  let i : Fin 32 := ⟨k / 8, by omega⟩
  have hi : i.val < 18446744073709551616 := by omega
  have hr := MemoryState.readAt_add_of_readAt (w := 8) hs.fits
    (hs.no_wrap (k := i.val) (by omega))
    (by simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]; omega) rfl
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] at hr
  rw [storeBytes_readAt m r (machine a) h i, machine_canonical] at hr
  have hb := congrArg (fun x : BitVec 8 => x.getLsbD (k % 8)) hr
  have hmod : k % 8 < 8 := Nat.mod_lt _ (by decide)
  have hindex : k / 8 * 8 + k % 8 = k := by omega
  have hindex' : 8 * (k / 8) + k % 8 = k := by omega
  simpa [BitVec.getLsbD_extractLsb', hmod, i, hindex, hindex'] using hb.symm

theorem storeBytes_canonical_value (m : MemoryState) (r : Pointer)
    (a : Fin 5 → BitVec 64) (h : SmallRange m r 32) :
    ((storeBytes m r (machine a)).readAt r 256).toNat =
      Field.serialValue a % modulus := by
  rw [storeBytes_read256 m r a h]
  exact tightWords_canonical a


end Agave.Ed25519.Encoding.Decompress.Execution.ToBytes
