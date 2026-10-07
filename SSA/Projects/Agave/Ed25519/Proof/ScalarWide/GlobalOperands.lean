import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperStartupMemory
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryWordCorrect

/-! Initialized R/RR globals instantiate the exact Montgomery operand contract.
All numerical certificates refer to the pinned byte initializers. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Bridge
open Agave.Ed25519.Reduce64.Execution (SmallRange)

def rWords : Fin 5 → BitVec 64 := fun i => montgomeryR.bytes.extractLsb' (64 * i.val) 64
def rrWords : Fin 5 → BitVec 64 := fun i => montgomeryRR.bytes.extractLsb' (64 * i.val) 64

theorem rWords_bound (i : Fin 5) : (rWords i).toNat < 2 ^ 52 := by
  fin_cases i <;> decide +kernel

theorem rrWords_bound (i : Fin 5) : (rrWords i).toNat < 2 ^ 52 := by
  fin_cases i <;> decide +kernel

theorem rWords_canonical : ScalarMontgomeryMul.limbValue (fun i => (rWords i).toNat) < subgroupOrder := by
  decide +kernel

theorem rrWords_canonical : ScalarMontgomeryMul.limbValue (fun i => (rrWords i).toNat) < subgroupOrder := by
  decide +kernel

theorem rWords_factor :
    ScalarMontgomeryMul.limbValue (fun i => (rWords i).toNat) % subgroupOrder =
      (1 * 2 ^ 260) % subgroupOrder := by
  decide +kernel

theorem rrWords_factor :
    ScalarMontgomeryMul.limbValue (fun i => (rrWords i).toNat) % subgroupOrder =
      ((2 ^ 260) * 2 ^ 260) % subgroupOrder := by
  decide +kernel

theorem constant_range (constant : ByteGlobal) (id : BlockId) (mem : MemoryState)
    (h : constant.Present id mem) (hlen : constant.length = 40) :
    SmallRange mem (constant.address id) 40 := by
  refine ⟨⟨constant.length, constant.bytes⟩, h, ?_, ?_⟩
  · simp [hlen]
  · simp [ByteGlobal.address, hlen]

theorem constant_read_words (constant : ByteGlobal) (id : BlockId) (mem : MemoryState)
    (h : constant.Present id mem) (hlen : constant.length = 40) (i : Fin 5) :
    mem.readAt ((constant.address id).add (BitVec.ofNat 64 (8 * i.val))) 64 =
      constant.bytes.extractLsb' (64 * i.val) 64 := by
  have hr := constant_range constant id mem h hlen
  have hi : 8 * i.val < 2 ^ 64 := by have := i.isLt; omega
  have hw : (BitVec.ofNat 64 (8 * i.val)).toNat * 8 + 64 ≤ 8 * constant.length := by
    simp only [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
    have := i.isLt
    omega
  have he := MemoryState.readAt_add_of_readAt
    (off := BitVec.ofNat 64 (8 * i.val)) h.fits (hr.no_wrap (by omega)) hw h.readAt
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] at he
  simpa only [show 8 * i.val * 8 = 64 * i.val by omega] using he

theorem ready_r_range (g : Globals) (state : GlobalState) (out : Pointer) (h : Ready g state out) :
    SmallRange state.mem g.address0 40 := by
  rw [h.1]
  exact constant_range _ _ _ h.2.2.1 rfl

theorem ready_rr_range (g : Globals) (state : GlobalState) (out : Pointer) (h : Ready g state out) :
    SmallRange state.mem g.address1 40 := by
  rw [h.2.1]
  exact constant_range _ _ _ h.2.2.2.1 rfl

theorem ready_r_read (g : Globals) (state : GlobalState) (out : Pointer)
    (h : Ready g state out) (i : Fin 5) :
    state.mem.readAt (g.address0.add (BitVec.ofNat 64 (8 * i.val))) 64 = rWords i := by
  rw [h.1]
  exact constant_read_words _ _ _ h.2.2.1 rfl i

theorem ready_rr_read (g : Globals) (state : GlobalState) (out : Pointer)
    (h : Ready g state out) (i : Fin 5) :
    state.mem.readAt (g.address1.add (BitVec.ofNat 64 (8 * i.val))) 64 = rrWords i := by
  rw [h.2.1]
  exact constant_read_words _ _ _ h.2.2.2.1 rfl i

end Agave.Ed25519.Verifier.Execution.ScalarWide
