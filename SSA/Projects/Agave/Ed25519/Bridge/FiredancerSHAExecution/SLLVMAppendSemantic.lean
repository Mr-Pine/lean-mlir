import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageShort
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMFinishObservation
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendSemantic

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.Reduce64.Execution
open FinishObservation
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
attribute [local irreducible] append core sourceRead Append.startState appendMessageShortMemory appendLow appendHigh

def sourceCounterMemory (m : MemoryState) (p : Pointer) (n : BitVec 64) : MemoryState :=
  let lo := sourceRead m (p.withOffset 208#64) 64
  let hi := sourceRead m (p.withOffset 216#64) 64
  (m.splice (p.withOffset 208#64) (appendLow lo n)).splice
    (p.withOffset 216#64) (appendHigh hi lo n)

attribute [local irreducible] sourceCounterMemory

theorem observed_splice_other {m : MemoryState} {p data : Pointer}
    {r : RIR.MemoryState} {q qd : RIR.Pointer} (h : Observed m data r qd)
    (hs : p.id ≠ data.id) (hr : q.id ≠ qd.id) (x : BitVec w) :
    Observed (m.splice p x) data (r.storeAt q x) qd := by
  refine ⟨?_, h.offset⟩
  rw [live?_splice_ne hs, RIR.MemoryState.getElem?_storeAt_ne hr.symm]
  exact h.block

theorem observed_counter {m : MemoryState} {p : Pointer} {s : RIR.GlobalState}
    {q : RIR.Pointer} (h : Observed m p s.mem q) (n : BitVec 64) :
    Observed (sourceCounterMemory m p n) p (Append.startState s q n).mem q := by
  unfold sourceCounterMemory Append.startState Append.counterMemory
  rw [(h.add 208#64).read, (h.add 216#64).read]
  exact (h.splice _ _).splice _ _

theorem observed_counter_data {m : MemoryState} {p data : Pointer} {s : RIR.GlobalState}
    {q qd : RIR.Pointer} (h : Observed m p s.mem q) (hd : Observed m data s.mem qd)
    (hs : p.id ≠ data.id) (hr : q.id ≠ qd.id) (n : BitVec 64) :
    Observed (sourceCounterMemory m p n) data (Append.startState s q n).mem qd := by
  unfold sourceCounterMemory Append.startState Append.counterMemory
  rw [(h.add 208#64).read, (h.add 216#64).read]
  exact observed_splice_other (p := p.withOffset 216#64) (q := q.add 216#64)
    (observed_splice_other (p := p.withOffset 208#64) (q := q.add 208#64) hd hs hr _) hs hr _

theorem observed_message_short {m : MemoryState} {p data : Pointer} {s : RIR.GlobalState}
    {q qd : RIR.Pointer} (h : Observed m p s.mem q) (hd : Observed m data s.mem qd)
    (hs : p.id ≠ data.id) (hr : q.id ≠ qd.id) (n : BitVec 64) :
    Observed (appendMessageShortMemory m p data n) p
      (Append.shortState (Append.startState s q n) q qd 64#64 n).mem q := by
  have hc := observed_counter h n
  have hi := observed_counter_data h hd hs hr n
  have hh := (hc.splice 64#64 (sourceRead (sourceCounterMemory m p n) data (8*n.toNat))).splice
    200#64 (64#64+n)
  rw [hi.read] at hh
  have hm : appendMessageShortMemory m p data n =
      ((sourceCounterMemory m p n).splice (p.withOffset 64#64)
        (sourceRead (sourceCounterMemory m p n) data (8*n.toNat))).splice
          (p.withOffset 200#64) (64#64+n) := by
    unfold appendMessageShortMemory sourceCounterMemory appendHigh appendLow
    rfl
  rw [hm, hi.read]
  simpa only [Append.shortState, Append.copyMemory, Append.countMemory] using hh

/-- The short third append preserves the stream invariant. This conclusion
comes from the actual source memory update and a per-allocation observation of
the independently proved RIR arithmetic model. No execution equality is a
premise. -/
theorem append_message_short_represents {m : MemoryState} {p data : Pointer}
    {s : RIR.GlobalState} {q qd : RIR.Pointer} (h : Observed m p s.mem q)
    (hd : Observed m data s.mem qd) (hs : p.id ≠ data.id) (hr : q.id ≠ qd.id)
    (n : BitVec 64) (hn : 0 < n.toNat) (hn64 : n.toNat < 64)
    (completed pending : List (BitVec 8)) (hp : ContextRepresents m p completed pending)
    (hc : SmallRange s.mem q 224) (hi : SmallRange s.mem qd n.toNat)
    (hcount : sourceRead m (p.withOffset 200#64) 64 = 64#64) :
    ContextRepresents (appendMessageShortMemory m p data n) p
      (completed ++ StreamSpec.complete (pending ++ sourceReadBytes m data n.toNat))
      (StreamSpec.pending (pending ++ sourceReadBytes m data n.toNat)) := by
  have hrep := h.context hc hp
  have hout := Append.Semantic.result_represents s q qd n completed pending hrep hi hr
  have hcnt : s.mem.readAt (q.add 200#64) 64 = 64#64 := ((h.add _).read _).symm.trans hcount
  have hn0 : n ≠ 0#64 := by intro hz; subst n; simp at hn
  have hshort : n.toNat < (128#64 - 64#64).toNat := hn64
  simp only [Append.resultState, hn0, ite_false, hcnt, show (64#64 = 0#64) = False by decide,
    hshort, ite_true] at hout
  have ho := observed_message_short h hd hs hr n
  have hf : Fits (appendMessageShortMemory m p data n) p (224*8) := by
    unfold appendMessageShortMemory
    exact fits_splice (fits_splice (fits_splice (fits_splice hp.live)))
  rw [← hd.bytes] at hout
  exact ho.context_back hf hp.noWrap hout

/-- Discharge the auxiliary RIR observation by constructing two fresh snapshot
blocks. Only source addressability and ordinary block-size bounds remain. -/
theorem append_message_short_represents_source (m : MemoryState) (p data : Pointer)
    (n : BitVec 64) (hn : 0 < n.toNat) (hn64 : n.toNat < 64)
    (completed pending : List (BitVec 8)) (hp : ContextRepresents m p completed pending)
    (hd : Fits m data (8*n.toNat)) (hs : p.id ≠ data.id)
    (hcsmall : ∀ b, m.live? p.id = some b → b.length < 2^63)
    (hdsmall : ∀ b, m.live? data.id = some b → b.length < 2^63)
    (hcount : sourceRead m (p.withOffset 200#64) 64 = 64#64) :
    ContextRepresents (appendMessageShortMemory m p data n) p
      (completed ++ StreamSpec.complete (pending ++ sourceReadBytes m data n.toNat))
      (StreamSpec.pending (pending ++ sourceReadBytes m data n.toNat)) := by
  obtain ⟨cb, hcb, hcl⟩ := hp.live
  obtain ⟨db, hdb, hdl⟩ := hd
  have hclive : m.live? p.id = some cb := by simp only [MemoryState.live?, hcb]
  have hdlive : m.live? data.id = some db := by simp only [MemoryState.live?, hdb]
  let cr : RIR.MemoryBlock := ⟨cb.length, cb.bytes⟩
  let dr : RIR.MemoryBlock := ⟨db.length, db.bytes⟩
  let rm : RIR.MemoryState := ⟨((∅ : Std.ExtHashMap RIR.BlockId RIR.MemoryBlock).insert ⟨0⟩ cr).insert ⟨1⟩ dr⟩
  let qp : RIR.Pointer := ⟨⟨0⟩, p.offset⟩
  let qd : RIR.Pointer := ⟨⟨1⟩, data.offset⟩
  have hgetp : rm[qp.id]? = some cr := by
    simp only [rm, qp, RIR.MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_insert,
      show ((⟨1⟩ : RIR.BlockId) == ⟨0⟩) = false by decide, beq_self_eq_true, ↓reduceIte]
    rfl
  have hgetd : rm[qd.id]? = some dr := by simp [rm, qd, RIR.MemoryState.getElem?_eq]
  have ho : Observed m p rm qp := ⟨by simpa only [hgetp, Option.map_some, ofRirBlock, cr] using hclive, rfl⟩
  have hdo : Observed m data rm qd := ⟨by simpa only [hgetd, Option.map_some, ofRirBlock, dr] using hdlive, rfl⟩
  have hrc : SmallRange rm qp 224 := by
    refine ⟨cr, hgetp, hcsmall cb hclive, ?_⟩
    change p.offset.toNat + 224 ≤ cb.length
    simp only [Pointer.offsetInBits, LiveBlock.lengthInBits] at hcl
    omega
  have hrd : SmallRange rm qd n.toNat := by
    refine ⟨dr, hgetd, hdsmall db hdlive, ?_⟩
    change data.offset.toNat + n.toNat ≤ db.length
    simp only [Pointer.offsetInBits, LiveBlock.lengthInBits] at hdl
    omega
  exact append_message_short_represents (s := ⟨⟨2⟩, rm⟩) ho hdo hs
    (by change (⟨0⟩ : RIR.BlockId) ≠ ⟨1⟩; decide : qp.id ≠ qd.id) n hn hn64 completed pending hp hrc hrd hcount

/-- Actual source call plus stream state and full caller frame for every third
append shorter than 64 bytes. Empty input is handled by `append_zero_represents`. -/
theorem append_message_short_call_represents (s : GlobalState) (p data : Pointer)
    (n : BitVec 64) (hwf : s.WF) (hn : 0 < n.toNat) (hn64 : n.toNat < 64)
    (completed pending : List (BitVec 8)) (hp : ContextRepresents s.mem p completed pending)
    (hd : Fits s.mem data (8*n.toNat)) (hs : p.id ≠ data.id)
    (hcsmall : ∀ b, s.mem.live? p.id = some b → b.length < 2^63)
    (hdsmall : ∀ b, s.mem.live? data.id = some b → b.length < 2^63)
    (hcount : sourceRead s.mem (p.withOffset 200#64) 64 = 64#64) :
    ∃ after : GlobalState,
      StateT.run (runFunction (append.denote
        (Ctxt.Valuation.ofHVector [.value n, .value data, .value p]ₕ))) s =
        .value ([.value p]ₕ, after) ∧
      after.WF ∧ after.alloc = s.alloc ∧ after.globals = s.globals ∧
      (∀ q, q ≠ p.id → after.mem.live? q = s.mem.live? q) ∧
      ContextRepresents after.mem p
        (completed ++ StreamSpec.complete (pending ++ sourceReadBytes s.mem data n.toNat))
        (StreamSpec.pending (pending ++ sourceReadBytes s.mem data n.toNat)) := by
  have hm := append_message_short_represents_source s.mem p data n hn hn64
    completed pending hp hd hs hcsmall hdsmall hcount
  obtain ⟨after, he, hw, ha, hg, hf, hb⟩ :=
    append_message_short_frame p data s n hwf hn hn64 hp.live hd hcount
  exact ⟨after, he, hw, ha, hg, hf, hm.of_live_eq hb.symm⟩

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
