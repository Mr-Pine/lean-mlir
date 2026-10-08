import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendSemantic
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendBuffered

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.Reduce64.Execution
open FinishObservation
set_option maxRecDepth 100000
set_option maxHeartbeats 400000
attribute [local irreducible] append core sourceRead sourceCounterMemory Append.startState

theorem counter32_eq (m : MemoryState) (p : Pointer) :
    sourceCounterMemory m p (32#64) =
      (m.splice (p.withOffset 208#64) (sourceRead m (p.withOffset 208#64) 64 + 256#64)).splice
      (p.withOffset 216#64) (sourceRead m (p.withOffset 216#64) 64 +
        (if sourceRead m (p.withOffset 208#64) 64 + 256#64 <ᵤ sourceRead m (p.withOffset 208#64) 64
          then 1#64 else 0#64)) := by
  unfold sourceCounterMemory appendHigh appendLow
  simp only [show (32#64 <<< (3 : Nat)) = 256#64 by decide,
    show (32#64 >>> (61 : Nat)) = 0#64 by decide, BitVec.add_zero]
  rfl

theorem observed_append32 {m : MemoryState} {p data : Pointer} {s : RIR.GlobalState}
    {q qd : RIR.Pointer} (h : Observed m p s.mem q) (hd : Observed m data s.mem qd)
    (hs : p.id ≠ data.id) (hr : q.id ≠ qd.id) :
    Observed (append32Memory m p data) p
      (Append.shortState (Append.startState s q (32#64)) q qd (0#64) (32#64)).mem q := by
  have hc := observed_counter h (32#64)
  have hi := observed_counter_data h hd hs hr (32#64)
  have hh := (hc.splice (0#64) (sourceRead (sourceCounterMemory m p (32#64)) data 256)).splice 200#64 (32#64)
  rw [hi.read] at hh
  have hm : append32Memory m p data =
      ((sourceCounterMemory m p (32#64)).splice p
        (sourceRead (sourceCounterMemory m p (32#64)) data 256)).splice (p.withOffset 200#64) (32#64) := by
    rw [counter32_eq]
    rfl
  rw [hm, hi.read]
  have hp0 : p.withOffset (0#64) = p := by cases p; simp [Pointer.withOffset]
  simp only [hp0] at hh
  convert hh using 1 <;> rfl

theorem observed_append32_buffered {m : MemoryState} {p data : Pointer} {s : RIR.GlobalState}
    {q qd : RIR.Pointer} (h : Observed m p s.mem q) (hd : Observed m data s.mem qd)
    (hs : p.id ≠ data.id) (hr : q.id ≠ qd.id) :
    Observed (append32BufferedMemory m p data) p
      (Append.shortState (Append.startState s q (32#64)) q qd (32#64) (32#64)).mem q := by
  have hc := observed_counter h (32#64)
  have hi := observed_counter_data h hd hs hr (32#64)
  have hh := (hc.splice (32#64) (sourceRead (sourceCounterMemory m p (32#64)) data 256)).splice 200#64 (64#64)
  rw [hi.read] at hh
  have hm : append32BufferedMemory m p data =
      ((sourceCounterMemory m p (32#64)).splice (p.withOffset 32#64)
        (sourceRead (sourceCounterMemory m p (32#64)) data 256)).splice (p.withOffset 200#64) (64#64) := by
    rw [counter32_eq]
    rfl
  rw [hm, hi.read]
  convert hh using 1 <;> rfl

theorem append32_represents {m : MemoryState} {p data : Pointer}
    {s : RIR.GlobalState} {q qd : RIR.Pointer} (h : Observed m p s.mem q)
    (hd : Observed m data s.mem qd) (hs : p.id ≠ data.id) (hr : q.id ≠ qd.id)
    (completed pending : List (BitVec 8)) (hp : ContextRepresents m p completed pending)
    (hc : SmallRange s.mem q 224) (hi : SmallRange s.mem qd 32)
    (hcount : sourceRead m (p.withOffset 200#64) 64 = 0#64) :
    ContextRepresents (append32Memory m p data) p
      (completed ++ StreamSpec.complete (pending ++ sourceReadBytes m data 32))
      (StreamSpec.pending (pending ++ sourceReadBytes m data 32)) := by
  have hrep := h.context hc hp
  have hout := Append.Semantic.result_represents s q qd (32#64) completed pending hrep hi hr
  have hcnt : s.mem.readAt (q.add 200#64) 64 = 0#64 := ((h.add _).read _).symm.trans hcount
  have he : (Append.resultState s q qd (32#64)).mem =
      (Append.shortState (Append.startState s q (32#64)) q qd (0#64) (32#64)).mem := by
    simp only [Append.resultState, hcnt, show (32#64 = 0#64) = False by decide,
      show (0#64 = 0#64) = True by decide,
      show (32#64).toNat < (128#64-32#64).toNat by decide, ite_false, ite_true]
    simp only [Append.directState, Append.tailState, show (32#64).toNat < 128 by decide,
      show (32#64 &&& 127#64) = 32#64 by decide,
      show (32#64 = 0#64) = False by decide, ite_true, ite_false]
    simp only [Append.tailMemory, Append.shortState, Append.copyMemory, Append.countMemory,
      show (32#64 &&& 127#64) = 32#64 by decide,
      show (32#64 &&& 18446744073709551488#64) = 0#64 by decide,
      RIR.Pointer.add, BitVec.add_zero, BitVec.zero_add]
    rfl
  rw [he] at hout
  have ho := observed_append32 h hd hs hr
  have hf : Fits (append32Memory m p data) p (224*8) := by
    unfold append32Memory
    exact fits_splice (fits_splice (fits_splice (fits_splice hp.live)))
  rw [← hd.bytes] at hout
  exact ho.context_back hf hp.noWrap hout

theorem append32_buffered_represents {m : MemoryState} {p data : Pointer}
    {s : RIR.GlobalState} {q qd : RIR.Pointer} (h : Observed m p s.mem q)
    (hd : Observed m data s.mem qd) (hs : p.id ≠ data.id) (hr : q.id ≠ qd.id)
    (completed pending : List (BitVec 8)) (hp : ContextRepresents m p completed pending)
    (hc : SmallRange s.mem q 224) (hi : SmallRange s.mem qd 32)
    (hcount : sourceRead m (p.withOffset 200#64) 64 = 32#64) :
    ContextRepresents (append32BufferedMemory m p data) p
      (completed ++ StreamSpec.complete (pending ++ sourceReadBytes m data 32))
      (StreamSpec.pending (pending ++ sourceReadBytes m data 32)) := by
  have hrep := h.context hc hp
  have hout := Append.Semantic.result_represents s q qd (32#64) completed pending hrep hi hr
  have hcnt : s.mem.readAt (q.add 200#64) 64 = 32#64 := ((h.add _).read _).symm.trans hcount
  have he : (Append.resultState s q qd (32#64)).mem =
      (Append.shortState (Append.startState s q (32#64)) q qd (32#64) (32#64)).mem := by
    simp only [Append.resultState, hcnt, show (32#64 = 0#64) = False by decide,
      show (0#64 = 0#64) = True by decide,
      show (32#64).toNat < (128#64-32#64).toNat by decide, ite_false, ite_true]
  rw [he] at hout
  have ho := observed_append32_buffered h hd hs hr
  have hf : Fits (append32BufferedMemory m p data) p (224*8) := by
    unfold append32BufferedMemory
    exact fits_splice (fits_splice (fits_splice (fits_splice hp.live)))
  rw [← hd.bytes] at hout
  exact ho.context_back hf hp.noWrap hout

theorem append32_represents_source (m : MemoryState) (p data : Pointer)
    (completed pending : List (BitVec 8)) (hp : ContextRepresents m p completed pending)
    (hd : Fits m data (8*32)) (hs : p.id ≠ data.id)
    (hcsmall : ∀ b, m.live? p.id = some b → b.length < 2^63)
    (hdsmall : ∀ b, m.live? data.id = some b → b.length < 2^63)
    (hcount : sourceRead m (p.withOffset 200#64) 64 = 0#64) :
    ContextRepresents (append32Memory m p data) p
      (completed ++ StreamSpec.complete (pending ++ sourceReadBytes m data 32))
      (StreamSpec.pending (pending ++ sourceReadBytes m data 32)) := by
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
  have hrd : SmallRange rm qd 32 := by
    refine ⟨dr, hgetd, hdsmall db hdlive, ?_⟩
    change data.offset.toNat + 32 ≤ db.length
    simp only [Pointer.offsetInBits, LiveBlock.lengthInBits] at hdl
    omega
  exact append32_represents (s := ⟨⟨2⟩, rm⟩) ho hdo hs
    (by change (⟨0⟩ : RIR.BlockId) ≠ ⟨1⟩; decide : qp.id ≠ qd.id) completed pending hp hrc hrd hcount

theorem append32_call_represents (s : GlobalState) (p data : Pointer)
    (hwf : s.WF)
    (completed pending : List (BitVec 8)) (hp : ContextRepresents s.mem p completed pending)
    (hd : Fits s.mem data (8*32)) (hs : p.id ≠ data.id)
    (hcsmall : ∀ b, s.mem.live? p.id = some b → b.length < 2^63)
    (hdsmall : ∀ b, s.mem.live? data.id = some b → b.length < 2^63)
    (hcount : sourceRead s.mem (p.withOffset 200#64) 64 = 0#64) :
    ∃ after : GlobalState,
      StateT.run (runFunction (append.denote
        (Ctxt.Valuation.ofHVector [.value (32#64), .value data, .value p]ₕ))) s =
        .value ([.value p]ₕ, after) ∧
      after.WF ∧ after.alloc = s.alloc ∧ after.globals = s.globals ∧
      (∀ q, q ≠ p.id → after.mem.live? q = s.mem.live? q) ∧
      ContextRepresents after.mem p
        (completed ++ StreamSpec.complete (pending ++ sourceReadBytes s.mem data 32))
        (StreamSpec.pending (pending ++ sourceReadBytes s.mem data 32)) := by
  have hm := append32_represents_source s.mem p data
    completed pending hp hd hs hcsmall hdsmall hcount
  obtain ⟨after, he, hw, ha, hg, hf, hb⟩ :=
    append32_frame p data s hwf hp.live hd hcount
  exact ⟨after, he, hw, ha, hg, hf, hm.of_live_eq hb.symm⟩

theorem append32_buffered_represents_source (m : MemoryState) (p data : Pointer)
    (completed pending : List (BitVec 8)) (hp : ContextRepresents m p completed pending)
    (hd : Fits m data (8*32)) (hs : p.id ≠ data.id)
    (hcsmall : ∀ b, m.live? p.id = some b → b.length < 2^63)
    (hdsmall : ∀ b, m.live? data.id = some b → b.length < 2^63)
    (hcount : sourceRead m (p.withOffset 200#64) 64 = 32#64) :
    ContextRepresents (append32BufferedMemory m p data) p
      (completed ++ StreamSpec.complete (pending ++ sourceReadBytes m data 32))
      (StreamSpec.pending (pending ++ sourceReadBytes m data 32)) := by
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
  have hrd : SmallRange rm qd 32 := by
    refine ⟨dr, hgetd, hdsmall db hdlive, ?_⟩
    change data.offset.toNat + 32 ≤ db.length
    simp only [Pointer.offsetInBits, LiveBlock.lengthInBits] at hdl
    omega
  exact append32_buffered_represents (s := ⟨⟨2⟩, rm⟩) ho hdo hs
    (by change (⟨0⟩ : RIR.BlockId) ≠ ⟨1⟩; decide : qp.id ≠ qd.id) completed pending hp hrc hrd hcount

theorem append32_buffered_call_represents (s : GlobalState) (p data : Pointer)
    (hwf : s.WF)
    (completed pending : List (BitVec 8)) (hp : ContextRepresents s.mem p completed pending)
    (hd : Fits s.mem data (8*32)) (hs : p.id ≠ data.id)
    (hcsmall : ∀ b, s.mem.live? p.id = some b → b.length < 2^63)
    (hdsmall : ∀ b, s.mem.live? data.id = some b → b.length < 2^63)
    (hcount : sourceRead s.mem (p.withOffset 200#64) 64 = 32#64) :
    ∃ after : GlobalState,
      StateT.run (runFunction (append.denote
        (Ctxt.Valuation.ofHVector [.value (32#64), .value data, .value p]ₕ))) s =
        .value ([.value p]ₕ, after) ∧
      after.WF ∧ after.alloc = s.alloc ∧ after.globals = s.globals ∧
      (∀ q, q ≠ p.id → after.mem.live? q = s.mem.live? q) ∧
      ContextRepresents after.mem p
        (completed ++ StreamSpec.complete (pending ++ sourceReadBytes s.mem data 32))
        (StreamSpec.pending (pending ++ sourceReadBytes s.mem data 32)) := by
  have hm := append32_buffered_represents_source s.mem p data
    completed pending hp hd hs hcsmall hdsmall hcount
  obtain ⟨after, he, hw, ha, hg, hf, hb⟩ :=
    append32_buffered_frame p data s hwf hp.live hd hcount
  exact ⟨after, he, hw, ha, hg, hf, hm.of_live_eq hb.symm⟩

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
