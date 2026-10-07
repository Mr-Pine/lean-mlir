import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.PointRepresentation
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointMemory

/-! Exact 160-byte readback and output frame for a point result. This reuses
the existing twenty-store memory schedule and the constructor's byte layout;
there is no canonical-limb or output-byte-equality premise. -/
namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR SerialPoint.Execution
open Reduce64.Execution (SmallRange)
open Verifier.Execution.Dalek (ReadBytes OutputFrame)

def payloadWords (P : ConcretePoint) (i : Fin 20) : BitVec 64 :=
  coordinates P ⟨i.val / 5, by omega⟩ ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩

theorem payloadWords_extract (P : ConcretePoint) (i : Fin 20) :
    P.bytes.extractLsb' (64*i.val) 64 = payloadWords P i := by
  have he := payload_word P ⟨i.val / 5, by omega⟩
    ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩
  have hoff : 320*(i.val / 5) + 64*(i.val % 5) = 64*i.val := by omega
  simpa only [payloadWords, hoff] using he

theorem pointStore_read1280 (m : MemoryState) (r : Pointer) (P : ConcretePoint)
    (h : SmallRange m r 160) :
    (storePointWords m r (payloadWords P)).readAt r 1280 = P.bytes := by
  have hs := smallRange_storePointWords h r (payloadWords P)
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  let i : Fin 20 := ⟨k / 64, by omega⟩
  have hi : 8*i.val < 2^64 := by omega
  have hr := MemoryState.readAt_add_of_readAt (w := 64) hs.fits
    (hs.no_wrap (k := 8*i.val) (by omega))
    (by simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]; omega) rfl
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] at hr
  rw [storePointWords_readAt m r (payloadWords P) h i, ← payloadWords_extract P i] at hr
  have hb := congrArg (fun x : BitVec 64 => x.getLsbD (k % 64)) hr
  have hmod : k % 64 < 64 := Nat.mod_lt _ (by decide)
  have hindex : 64*(k/64) + k%64 = k := by omega
  have hindex' : 8*(k/64)*8 + k%64 = k := by omega
  simpa [BitVec.getLsbD_extractLsb', hmod, i, hindex, hindex'] using hb.symm

def pointStore (s : GlobalState) (r : Pointer) (P : ConcretePoint) (allocations : Nat) :
    GlobalState :=
  {alloc := ⟨s.alloc.nextFreeBlock + allocations⟩,
    mem := storePointWords s.mem r (payloadWords P)}

theorem pointStore_frame (s : GlobalState) (r : Pointer) (P : ConcretePoint)
    (allocations : Nat) (hwf : s.WF) (hr : SmallRange s.mem r 160) :
    OutputFrame s (pointStore s r P allocations) r 160 := by
  constructor
  · exact (wf_storePointWords s hwf r (payloadWords P)).add_blocks
  · intro q n hq
    exact smallRange_storePointWords hq r (payloadWords P)
  · intro q w hd
    exact readAt_storePointWords_frame s.mem r q (payloadWords P) w hr hd

theorem pointStore_readback (s : GlobalState) (r : Pointer) (P : ConcretePoint)
    (allocations : Nat) (hr : SmallRange s.mem r 160) :
    ReadBytes (pointStore s r P allocations) r 160 P.bytes :=
  ⟨smallRange_storePointWords hr r (payloadWords P), pointStore_read1280 s.mem r P hr⟩

end Agave.Ed25519.SmallOrder.Execution
