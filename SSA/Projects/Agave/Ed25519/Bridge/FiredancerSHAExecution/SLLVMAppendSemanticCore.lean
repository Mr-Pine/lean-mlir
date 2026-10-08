import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendSemantic
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageDirect
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreContract

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.Reduce64.Execution
open FinishObservation
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 400000
attribute [local irreducible] append core sourceRead sourceCounterMemory appendMessageFilledMemory
  Append.startState appendLow appendHigh Core.result

theorem observed_message_filled {m : MemoryState} {p data : Pointer} {s : RIR.GlobalState}
    {q qd : RIR.Pointer} (h : Observed m p s.mem q) (hd : Observed m data s.mem qd)
    (hs : p.id ≠ data.id) (hr : q.id ≠ qd.id) (n : BitVec 64) :
    Observed (appendMessageFilledMemory m p data n) p
      (Append.fillState (Append.startState s q n) q qd 64#64).mem q := by
  have hc := observed_counter h n
  have hi := observed_counter_data h hd hs hr n
  have hh := hc.splice 64#64 (sourceRead (sourceCounterMemory m p n) data 512)
  rw [hi.read] at hh
  have hm : appendMessageFilledMemory m p data n =
      (sourceCounterMemory m p n).splice (p.withOffset 64#64)
        (sourceRead (sourceCounterMemory m p n) data 512) := by
    unfold appendMessageFilledMemory sourceCounterMemory appendHigh appendLow
    rfl
  rw [hm, hi.read]
  change Observed ((sourceCounterMemory m p n).splice (p.withOffset 64#64)
    ((Append.startState s q n).mem.readAt qd 512)) p
    ((Append.startState s q n).mem.storeAt (q.add 64#64)
      ((Append.startState s q n).mem.readAt qd 512)) q
  exact hh

theorem core_readBits_eq (m : MemoryState) (p : Pointer) (w : Nat) :
    Core.readBits m p w = sourceRead m p w := by
  unfold Core.readBits readWord? sourceRead
  cases m.live? p.id <;> rfl

theorem observed_core_result {before : GlobalState} {p data : Pointer} {s : RIR.GlobalState}
    {q qd : RIR.Pointer} (h : Observed before.mem p s.mem q)
    (hd : Observed before.mem data s.mem qd) (n : BitVec 64)
    (hi : SmallRange s.mem qd (128*n.toNat)) :
    Core.result before (p.withOffset 128#64) data n =
      Agave.Ed25519.SHA512.Spec.run (s.mem.readAt (q.add 128#64) 512)
        (readBytes s.mem qd (128*n.toNat)) := by
  unfold Core.result Core.readBytes
  rw [core_readBits_eq, core_readBits_eq, (h.add 128#64).read, hd.read]
  rw [readBytes_eq_bytesOf _ _ _ hi]
  rfl

theorem observed_compression {before : GlobalState} {p data : Pointer} {s : RIR.GlobalState}
    {q qd : RIR.Pointer} (h : Observed before.mem p s.mem q)
    (hd : Observed before.mem data s.mem qd) (n : BitVec 64)
    (hi : SmallRange s.mem qd (128*n.toNat)) :
    Observed (before.mem.splice (p.withOffset 128#64)
      (Core.result before (p.withOffset 128#64) data n)) p
      (Append.compressionState s (q.add 128#64) qd n.toNat).mem q := by
  rw [observed_core_result h hd n hi]
  exact h.splice _ _

theorem observed_reset {m : MemoryState} {p : Pointer} {s : RIR.GlobalState}
    {q : RIR.Pointer} (h : Observed m p s.mem q) :
    Observed (m.splice (p.withOffset 200#64) (0#64)) p (Append.resetState s q).mem q :=
  h.splice _ _

theorem observed_direct_tail {m : MemoryState} {p rest : Pointer} {s : RIR.GlobalState}
    {q qd : RIR.Pointer} (h : Observed m p s.mem q) (hd : Observed m rest s.mem qd)
    (size : BitVec 64) :
    Observed (appendMessageDirectTailMemory m p rest size) p
      (Append.tailState s q qd size).mem q := by
  unfold appendMessageDirectTailMemory Append.tailState
  dsimp only
  split
  · rename_i hz
    simpa only [hz, ite_true] using h
  · rename_i hz
    simp only [hz, ite_false]
    have hi := (hd.add (size &&& 18446744073709551488#64)).read (8*(size &&& 127#64).toNat)
    have hh := (h.splice 0#64 (sourceRead m (rest.withOffset (size &&& 18446744073709551488#64))
      (8*(size &&& 127#64).toNat))).splice 200#64 (size &&& 127#64)
    rw [hi] at hh ⊢
    simpa only [Append.tailMemory, Append.copyMemory, Append.countMemory,
      Pointer.withOffset, RIR.Pointer.add, BitVec.add_zero] using hh

theorem short_tail_mask (size : BitVec 64) (h : size.toNat < 128) :
    size &&& 127#64 = size := by
  apply BitVec.eq_of_toNat_eq
  change (size &&& 127).toNat = size.toNat
  rw [append_remainder, Nat.mod_eq_of_lt h]

theorem short_tail_aligned (size : BitVec 64) (h : size.toNat < 128) :
    size &&& 18446744073709551488#64 = 0#64 := by
  have hz : size >>> (7 : Nat) = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      show 2^7 = 128 from rfl, BitVec.toNat_ofNat, Nat.zero_mod] using Nat.div_eq_of_lt h
  change size &&& (-128 : BitVec 64) = 0#64
  rw [append_aligned_mask, hz]
  rfl

theorem observed_message_tail {m : MemoryState} {p rest : Pointer} {s : RIR.GlobalState}
    {q qd : RIR.Pointer} (h : Observed m p s.mem q) (hd : Observed m rest s.mem qd)
    (hs : p.id ≠ rest.id) (hr : q.id ≠ qd.id) (tail : BitVec 64)
    (hn : 0 < tail.toNat) (hb : tail.toNat < 128) :
    Observed (appendMessageTailMemory m p rest tail) p
      (Append.tailState (Append.resetState s q) q qd tail).mem q := by
  have hc := observed_reset h
  have hi := observed_splice_other (p := p.withOffset 200#64) (q := q.add 200#64) hd hs hr (0#64)
  have hh := observed_direct_tail hc hi tail
  have hn0 : tail ≠ 0#64 := by intro he; subst tail; simp at hn
  have hm : appendMessageTailMemory m p rest tail =
      appendMessageDirectTailMemory (m.splice (p.withOffset 200#64) (0#64)) p rest tail := by
    simp only [appendMessageTailMemory, appendMessageDirectTailMemory,
      short_tail_mask tail hb, short_tail_aligned tail hb, hn0, ite_false,
      Pointer.withOffset, BitVec.add_zero]
    rw [short_tail_mask tail hb]
  rw [hm]
  exact hh

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
