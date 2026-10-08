import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendSemanticCore
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageResult

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open FinishObservation
set_option maxRecDepth 100000
set_option maxHeartbeats 400000
attribute [local irreducible] append core sourceRead sourceCounterMemory Core.result
  Append.startState appendMessageFilledMemory

theorem rir_small_mono {m : RIR.MemoryState} {p : RIR.Pointer} {n k : Nat}
    (h : SmallRange m p n) (hk : k ≤ n) : SmallRange m p k := by
  obtain ⟨b, hb, hs, hl⟩ := h
  exact ⟨b, hb, hs, by omega⟩

theorem rir_small_add {m : RIR.MemoryState} {p : RIR.Pointer} {n k len : Nat}
    (h : SmallRange m p n) (hk : k+len ≤ n) :
    SmallRange m (p.add (BitVec.ofNat 64 k)) len := by
  have hf := h.fits_add hk
  obtain ⟨b, hb, hs, hl⟩ := h
  obtain ⟨b', hb', hfit⟩ := hf
  have he : b' = b := Option.some.inj (hb'.symm.trans hb)
  subst b'
  refine ⟨b, hb', hs, ?_⟩
  simp only [RIR.Pointer.offsetInBits, RIR.MemoryBlock.lengthInBits] at hfit
  omega

theorem observed_other_frames {m m' : MemoryState} {p : Pointer}
    {r r' : RIR.MemoryState} {q : RIR.Pointer} (h : Observed m p r q)
    (hs : m'.live? p.id = m.live? p.id) (hr : r'[q.id]? = r[q.id]?) : Observed m' p r' q := by
  exact ⟨by rw [hs, hr]; exact h.block, h.offset⟩

/-- Every concrete third-append branch has the same context block as the proved
RIR append model. Only observations and ordinary address ranges are premises. -/
theorem observed_message_result {before : GlobalState} {p data : Pointer} {s : RIR.GlobalState}
    {q qd : RIR.Pointer} (h : Observed before.mem p s.mem q)
    (hd : Observed before.mem data s.mem qd) (hs : p.id ≠ data.id) (hr : q.id ≠ qd.id)
    (n : BitVec 64) (hc : SmallRange s.mem q 224) (hi : SmallRange s.mem qd n.toNat)
    (hcount : sourceRead before.mem (p.withOffset 200#64) 64 = 64#64) :
    Observed (MessageExecution.resultState before p data n).mem p
      (Append.resultState s q qd n).mem q := by
  have hcnt : s.mem.readAt (q.add 200#64) 64 = 64#64 := ((h.add _).read _).symm.trans hcount
  by_cases hz : n = 0#64
  · simp only [MessageExecution.resultState, Append.resultState, hz, ite_true]
    exact h
  by_cases hshort : n.toNat < 64
  · simpa only [MessageExecution.resultState, Append.resultState, hz, ite_false, hshort, ite_true,
      hcnt, show (64#64 = 0#64) = False by decide, show 128#64 - 64#64 = 64#64 by decide,
      show (64#64).toNat=64 from rfl]
      using observed_message_short h hd hs hr n
  let filled : GlobalState := {before with mem := appendMessageFilledMemory before.mem p data n}
  let rfilled := Append.fillState (Append.startState s q n) q qd 64#64
  let first := MessageExecution.coreState filled p p (1#64)
  let rfirst := Append.compressionState rfilled (q.add 128#64) q 1
  have hw : Append.BlockWrites q.id s.mem rfilled.mem := by
    have hw0 : Append.BlockWrites q.id s.mem (Append.startState s q n).mem := by
      unfold Append.startState
      exact Append.counter_writes _ _ _ _ _
    exact hw0.trans (Append.fill_writes (Append.startState s q n) q qd 64#64)
  have hf : Observed filled.mem p rfilled.mem q := observed_message_filled h hd hs hr n
  have hfc : SmallRange rfilled.mem q 224 := hw.live hc
  have hfirst : Observed first.mem p rfirst.mem q := by
    dsimp only [first, MessageExecution.coreState, rfirst]
    exact observed_compression hf hf (1#64) (rir_small_mono hfc (by decide))
  have hfd : Observed filled.mem data rfilled.mem qd := observed_other_frames hd
    (MessageExecution.filledMemory_other before.mem p data n data.id hs.symm) (hw.other qd.id hr.symm)
  have hfirstd : Observed first.mem data rfirst.mem qd := by
    refine observed_other_frames hfd ?_ ((Append.compression_writes rfilled q q 1).other qd.id hr.symm)
    dsimp only [first, MessageExecution.coreState]
    exact live?_splice_ne hs
  have hrst := observed_reset hfirst
  have hrstd := observed_splice_other (p := p.withOffset 200#64) (q := q.add 200#64) hfirstd hs hr (0#64)
  have hrest := hrstd.add 64#64
  have hbase : (Append.resultState s q qd n) =
      Append.directState (Append.resetState rfirst q) q (qd.add 64#64) (n-64#64) := by
    simp only [Append.resultState, hz, ite_false, hcnt,
      show (64#64 = 0#64) = False by decide, show 128#64-64#64=64#64 by decide,
      show (64#64).toNat=64 from rfl, hshort]
    rfl
  rw [hbase]
  by_cases heq : n = 64#64
  · subst n
    simp only [MessageExecution.resultState, show (64#64 = 0#64) = False by decide,
      show ¬(64#64).toNat < 64 by decide, ite_false, ite_true]
    change Observed (first.mem.splice (p.withOffset 200#64) (0#64)) p
      (Append.directState (Append.resetState rfirst q) q (qd.add 64#64) (64#64-64#64)).mem q
    convert hrst using 1
    simp only [show 64#64-64#64=0#64 by decide, Append.directState,
      show (0#64).toNat<128 by decide, ite_true, Append.tailState,
      show (0#64 &&& 127#64)=0#64 by decide]
  have hn64 : 64 ≤ n.toNat := by omega
  have hrem : (n-64#64).toNat = n.toNat-64 := by
    exact BitVec.toNat_sub_of_le (show (64#64).toNat ≤ n.toNat from hn64)
  by_cases htail : n.toNat < 192
  · have htpos : 0 < (n-64#64).toNat := by
      have hnne : n.toNat ≠ 64 := by intro hh; apply heq; apply BitVec.eq_of_toNat_eq; exact hh
      omega
    have htbound : (n-64#64).toNat < 128 := by omega
    have hh := observed_message_tail hfirst (hfirstd.add 64#64) hs hr (n-64#64) htpos htbound
    simpa only [MessageExecution.resultState, hz, hshort, heq, htail, ite_false, ite_true,
      Append.directState, htbound] using hh
  · let reset : GlobalState := {first with mem := first.mem.splice (p.withOffset 200#64) (0#64)}
    let rreset := Append.resetState rfirst q
    let count := (n-64#64) >>> (7 : Nat)
    have hni : 64 + 128*count.toNat ≤ n.toNat := by
      simp only [count, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show 2^7=128 from rfl, hrem]
      have := Nat.div_mul_le_self (n.toNat-64) 128
      omega
    have hri : SmallRange rreset.mem (qd.add 64#64) (128*count.toNat) := by
      have hh := rir_small_add hi hni
      exact (Append.reset_writes rfirst q).live ((Append.compression_writes rfilled q q 1).live (hw.live hh))
    have hbulk := observed_compression (before := reset) hrst hrest count hri
    have hbulkd : Observed
        (reset.mem.splice (p.withOffset 128#64) (Core.result reset (p.withOffset 128#64) (data.withOffset 64#64) count))
        (data.withOffset 64#64)
        (Append.compressionState rreset (q.add 128#64) (qd.add 64#64) count.toNat).mem (qd.add 64#64) :=
      observed_other_frames hrest (live?_splice_ne hs)
        ((Append.compression_writes rreset q (qd.add 64#64) count.toNat).other qd.id hr.symm)
    have hh := observed_direct_tail hbulk hbulkd (n-64#64)
    have htbound : ¬(n-64#64).toNat < 128 := by omega
    simp only [MessageExecution.resultState, hz, hshort, heq, htail, ite_false,
      Append.directState, htbound]
    exact hh

theorem observed_source_fits {m : MemoryState} {p : Pointer} {r : RIR.MemoryState}
    {q : RIR.Pointer} {n : Nat} (h : Observed m p r q) (hr : SmallRange r q n) :
    Fits m p (8*n) := by
  obtain ⟨b, hb, _, hl⟩ := hr
  have hm : m.live? p.id = some (ofRirBlock b) := by
    simpa only [hb, Option.map_some] using h.block
  refine ⟨ofRirBlock b, getElem?_of_live? hm, ?_⟩
  simp only [Pointer.offsetInBits, LiveBlock.lengthInBits, ofRirBlock, h.offset]
  omega

theorem append_message_result_represents {s : GlobalState} {p data : Pointer}
    {r : RIR.GlobalState} {q qd : RIR.Pointer} (h : Observed s.mem p r.mem q)
    (hd : Observed s.mem data r.mem qd) (hs : p.id ≠ data.id) (hr : q.id ≠ qd.id)
    (n : BitVec 64) (completed pending : List (BitVec 8))
    (hp : ContextRepresents s.mem p completed pending)
    (hc : SmallRange r.mem q 224) (hi : SmallRange r.mem qd n.toNat)
    (hcount : sourceRead s.mem (p.withOffset 200#64) 64 = 64#64) :
    ContextRepresents (MessageExecution.resultState s p data n).mem p
      (completed ++ StreamSpec.complete (pending ++ sourceReadBytes s.mem data n.toNat))
      (StreamSpec.pending (pending ++ sourceReadBytes s.mem data n.toNat)) := by
  have hrep := h.context hc hp
  have hout := Append.Semantic.result_represents r q qd n completed pending hrep hi hr
  have ho := observed_message_result h hd hs hr n hc hi hcount
  rw [← hd.bytes] at hout
  exact ho.context_back (observed_source_fits ho ((Append.result_writes r q qd n).live hc)) hp.noWrap hout

theorem append_message_result_represents_source (s : GlobalState) (p data : Pointer)
    (n : BitVec 64)
    (completed pending : List (BitVec 8)) (hp : ContextRepresents s.mem p completed pending)
    (hd : Fits s.mem data (8*n.toNat)) (hs : p.id ≠ data.id)
    (hcsmall : ∀ b, s.mem.live? p.id = some b → b.length < 2^63)
    (hdsmall : ∀ b, s.mem.live? data.id = some b → b.length < 2^63)
    (hcount : sourceRead s.mem (p.withOffset 200#64) 64 = 64#64) :
    ContextRepresents ((MessageExecution.resultState s p data n).mem) p
      (completed ++ StreamSpec.complete (pending ++ sourceReadBytes s.mem data n.toNat))
      (StreamSpec.pending (pending ++ sourceReadBytes s.mem data n.toNat)) := by
  obtain ⟨cb, hcb, hcl⟩ := hp.live
  obtain ⟨db, hdb, hdl⟩ := hd
  have hclive : s.mem.live? p.id = some cb := by simp only [MemoryState.live?, hcb]
  have hdlive : s.mem.live? data.id = some db := by simp only [MemoryState.live?, hdb]
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
  have ho : Observed s.mem p rm qp := ⟨by simpa only [hgetp, Option.map_some, ofRirBlock, cr] using hclive, rfl⟩
  have hdo : Observed s.mem data rm qd := ⟨by simpa only [hgetd, Option.map_some, ofRirBlock, dr] using hdlive, rfl⟩
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
  exact append_message_result_represents (r := ⟨⟨2⟩, rm⟩) ho hdo hs
    (by change (⟨0⟩ : RIR.BlockId) ≠ ⟨1⟩; decide : qp.id ≠ qd.id) n completed pending hp hrc hrd hcount

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
