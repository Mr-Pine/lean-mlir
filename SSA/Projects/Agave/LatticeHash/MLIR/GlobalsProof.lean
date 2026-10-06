/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.GeneratedGlobals
import SSA.Projects.Agave.LatticeHash.Compression
import SSA.Projects.Agave.LatticeHash.MLIR.LoadContract
import SSA.Projects.Firedancer.Proof.Globals

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open Blake3Compression

/-- Every entry of the actual compiler-emitted schedule agrees with the existing
BLAKE3 schedule. This finite proof is evaluated by the Lean kernel. -/
theorem scheduleGlobalWords_lookup : ∀ (r : Fin 7) (i : Fin 16),
    scheduleGlobalWords[16 * r.val + i.val]'(by omega) =
      BitVec.ofNat 64 (schedule r i).val := by decide

/-- The byte layout is the emitted little-endian array of 112 u64 entries. -/
theorem scheduleGlobalBits_lookup (r : Fin 7) (i : Fin 16) :
    scheduleGlobalBits.extractLsb' (64 * (16 * r.val + i.val)) 64 =
      BitVec.ofNat 64 (schedule r i).val := by
  rw [Nat.mul_comm 64 _, scheduleGlobalBits, BitVec.extractLsb'_packLanes]
  exact scheduleGlobalWords_lookup r i

/-- A normal initialized global starts at offset zero. This condition excludes
64-bit pointer-offset wraparound independently of the abstract block length. -/
def ScheduleGlobal (s : GlobalState) (p : Pointer) : Prop :=
  HoldsGlobal s scheduleGlobalName p scheduleGlobalBits ∧ p.offset = 0

def schedulePtr (p : Pointer) (r : Fin 7) (i : Fin 16) : Pointer :=
  p.withOffset (BitVec.ofNat 64 (8 * (16 * r.val + i.val)))

/-- Normalize the row GEP followed by the column GEP emitted in the round loop. -/
theorem schedulePtr_two_geps (p : Pointer) (r : Fin 7) (i : Fin 16) :
    (p.withOffset (BitVec.ofNat 64 r.val * 128)).withOffset (BitVec.ofNat 64 (8 * i.val)) =
      schedulePtr p r i := by
  simp only [Pointer.withOffset, schedulePtr]
  congr 1
  rw [BitVec.add_assoc]
  congr 1
  rw [show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl,
    ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  congr 1
  omega

theorem schedulePtr_offset (p : Pointer) (hzero : p.offset = 0)
    (r : Fin 7) (i : Fin 16) :
    (schedulePtr p r i).offsetInBits = 64 * (16 * r.val + i.val) := by
  have hsmall : 8 * (16 * r.val + i.val) < 2 ^ 64 := by omega
  simp [schedulePtr, Pointer.withOffset, Pointer.offsetInBits, hzero,
    BitVec.toNat_ofNat]
  omega

/-- All 112 schedule loads fit from one initialized-global premise. -/
theorem scheduleGlobal_fits {s : GlobalState} {p : Pointer} (h : ScheduleGlobal s p)
    (r : Fin 7) (i : Fin 16) : Fits s.mem (schedulePtr p r i) 64 := by
  obtain ⟨blk, hblk, hlen⟩ := h.1.2.1
  refine ⟨blk, hblk, ?_⟩
  rw [schedulePtr_offset p h.2]
  simp only [Pointer.offsetInBits, h.2] at hlen
  omega

/-- Every schedule cell contains the corresponding source-model index. -/
theorem scheduleGlobal_read {s : GlobalState} {p : Pointer} (h : ScheduleGlobal s p)
    (r : Fin 7) (i : Fin 16) :
    readWord? (schedulePtr p r i) 64 s.mem = some (BitVec.ofNat 64 (schedule r i).val) := by
  obtain ⟨hptr, hfit, hfull⟩ := h.1
  obtain ⟨blk, hblk, hlen⟩ := hfit
  have hfull' : blk.bytes.extractLsb' 0 7168 = scheduleGlobalBits := by
    simpa [readWord, readWord?, MemoryState.live?, hblk, Pointer.offsetInBits, h.2] using hfull
  have hslice := congrArg (fun v : BitVec 7168 => v.extractLsb' (64 * (16 * r.val + i.val)) 64) hfull'
  rw [BitVec.extractLsb'_extractLsb'_of_le (by omega), scheduleGlobalBits_lookup] at hslice
  have hlive : s.mem.live? p.id = some blk := by simp [MemoryState.live?, hblk]
  simp only [readWord?, show (schedulePtr p r i).id = p.id from rfl, hlive,
    Option.pure_def, schedulePtr_offset p h.2]
  exact congrArg some hslice

/-- The total `readWord` interface used by compression loop proofs. -/
theorem scheduleGlobal_readWord {s : GlobalState} {p : Pointer} (h : ScheduleGlobal s p)
    (r : Fin 7) (i : Fin 16) :
    readWord (scheduleGlobal_fits h r i) = BitVec.ofNat 64 (schedule r i).val :=
  readWord_eq_of (scheduleGlobal_read h r i)

/-- Actual SLLVM memory-load execution, with unchanged memory and no poison. -/
theorem scheduleGlobal_load {s : GlobalState} {p : Pointer} (h : ScheduleGlobal s p)
    (r : Fin 7) (i : Fin 16) :
    (load (.value (schedulePtr p r i)) (.bitvec (.concrete 64))).run s.mem =
      .value (.value (BitVec.ofNat 64 (schedule r i).val), s.mem) :=
  run_load_of_readWord (t := .bitvec (.concrete 64)) (scheduleGlobal_fits h r i)
    _ (scheduleGlobal_readWord h r i)

/-- Installing the emitted initializer establishes the entire schedule premise. -/
theorem scheduleGlobal_withGlobal (s : GlobalState) :
    ScheduleGlobal (s.withGlobal scheduleGlobalName scheduleGlobalBits)
      ⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ :=
  ⟨holdsGlobal_withGlobal s scheduleGlobalName scheduleGlobalBits, rfl⟩

end AgaveLatticeHash.MLIR
