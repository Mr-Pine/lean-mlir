import SSA.Projects.Agave.Ed25519.Proof.Encoding.ToBytesPacking

namespace Agave.Ed25519.Encoding
set_option maxHeartbeats 2000000

theorem machine0_schedule (a : Field.Serial) :
    RIR.toBytesMachine0 (a 0) (a 1) (a 2) (a 3) (a 4) =
      carriedWord (weakWord a) (19 * quotientWord a) 0 + ((weakWord a 1) <<< 51) := by
  dsimp [RIR.toBytesMachine0, carriedWord, weakWord, quotientWord]
  simp only [BitVec.add_comm, BitVec.mul_comm]

theorem machine1_schedule (a : Field.Serial) :
    RIR.toBytesMachine1 (a 0) (a 1) (a 2) (a 3) (a 4) =
      emittedPack1 (carriedWord (weakWord a) (19 * quotientWord a) 1)
        (carriedWord (weakWord a) (19 * quotientWord a) 2) := by
  dsimp [RIR.toBytesMachine1, carriedWord, weakWord, quotientWord, emittedPack1]
  simp only [BitVec.add_comm, BitVec.mul_comm]

theorem machine2_schedule (a : Field.Serial) :
    RIR.toBytesMachine2 (a 0) (a 1) (a 2) (a 3) (a 4) =
      emittedPack2 (carriedWord (weakWord a) (19 * quotientWord a) 2)
        (carriedWord (weakWord a) (19 * quotientWord a) 3) := by
  dsimp [RIR.toBytesMachine2, carriedWord, weakWord, quotientWord, emittedPack2]
  simp only [BitVec.add_comm, BitVec.mul_comm]

theorem machine3_schedule (a : Field.Serial) :
    RIR.toBytesMachine3 (a 0) (a 1) (a 2) (a 3) (a 4) =
      emittedPack3 (carriedWord (weakWord a) (19 * quotientWord a) 3)
        (carriedWord (weakWord a) (19 * quotientWord a) 4) := by
  dsimp [RIR.toBytesMachine3, carriedWord, weakWord, quotientWord, emittedPack3]
  simp only [BitVec.add_comm, BitVec.mul_comm]

theorem machine0_pack (a : Field.Serial) :
    RIR.toBytesMachine0 (a 0) (a 1) (a 2) (a 3) (a 4) = packWords (tightWords a) 0 := by
  rw [machine0_schedule, first_word_pack]
  rfl

theorem machine1_pack (a : Field.Serial) :
    RIR.toBytesMachine1 (a 0) (a 1) (a 2) (a 3) (a 4) = packWords (tightWords a) 1 := by
  rw [machine1_schedule, emittedPack1_eq]
  rfl

theorem machine2_pack (a : Field.Serial) :
    RIR.toBytesMachine2 (a 0) (a 1) (a 2) (a 3) (a 4) = packWords (tightWords a) 2 := by
  rw [machine2_schedule, emittedPack2_eq]
  rfl

theorem machine3_pack (a : Field.Serial) :
    RIR.toBytesMachine3 (a 0) (a 1) (a 2) (a 3) (a 4) = packWords (tightWords a) 3 := by
  rw [machine3_schedule, emittedPack3_eq]
  rfl

/-- The complete 256-bit output determined by the four compiler observations. -/
def machineBytes (a : Field.Serial) : BitVec 256 :=
  RIR.toBytesMachine3 (a 0) (a 1) (a 2) (a 3) (a 4) ++
  RIR.toBytesMachine2 (a 0) (a 1) (a 2) (a 3) (a 4) ++
  RIR.toBytesMachine1 (a 0) (a 1) (a 2) (a 3) (a 4) ++
  RIR.toBytesMachine0 (a 0) (a 1) (a 2) (a 3) (a 4)

theorem machineBytes_canonical (a : Field.Serial) :
    (machineBytes a).toNat = Field.serialValue a % modulus := by
  unfold machineBytes
  rw [machine3_pack, machine2_pack, machine1_pack, machine0_pack]
  exact tightWords_canonical a

/-- Agreement of the exact compiler-produced serialization observations
with the canonical field encoding for all five-u64 inputs. -/
theorem machineBytes_eq_toBytes (a : Field.Serial) :
    machineBytes a = toBytes (fun i => (a i).toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [machineBytes_canonical, toBytes_toNat _ (fun i => (a i).isLt), value_eq_decode51]
  rfl

end Agave.Ed25519.Encoding
