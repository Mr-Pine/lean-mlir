import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendModel

/-! Full actual append execution from its public pointer/size ABI. No append
execution fact is assumed: the only call premise is the contextual positive
compression contract, and every source control-flow path is composed here. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

structure Resources (id : BlockId) (s : GlobalState) (context data : Pointer) (size : Word) : Prop where
  wf : s.WF
  contextLive : SmallRange s.mem context 224
  inputLive : SmallRange s.mem data size.toNat
  constants : constantsGlobal.Present id s.mem
  distinct : context.id ≠ data.id
  immutable : context.id ≠ id

variable {id : BlockId} {s t : GlobalState} {context data : Pointer} {size : Word}

theorem Resources.transport (h : Resources id s context data size)
    (hw : BlockWrites context.id s.mem t.mem)
    (ha : s.alloc.nextFreeBlock ≤ t.alloc.nextFreeBlock) : Resources id t context data size := by
  refine ⟨?_, hw.live h.contextLive, hw.live h.inputLive,
    hw.present constantsGlobal id (Ne.symm h.immutable) h.constants, h.distinct, h.immutable⟩
  have hm := hw.wf s.alloc h.wf
  intro j hj
  exact (hm j hj).trans_le ha

theorem Resources.start (h : Resources id s context data size) :
    Resources id (startState s context size) context data size :=
  h.transport (counter_writes _ _ _ _ _) (Nat.le_refl _)

theorem Resources.fill (h : Resources id s context data size) (used : Word) :
    Resources id (fillState s context data used) context data size :=
  h.transport (fill_writes s context data used) (Nat.le_refl _)

theorem Resources.compress (h : Resources id s context data size) (src : Pointer) (n : Nat) :
    Resources id (compressionState s (context.add 128#64) src n) context data size :=
  h.transport (compression_writes s context src n) (Nat.le_succ _)

theorem Resources.reset (h : Resources id s context data size) :
    Resources id (resetState s context) context data size :=
  h.transport (reset_writes s context) (Nat.le_refl _)

theorem Resources.advance (h : Resources id s context data size) (n : Word)
    (hn : n.toNat ≤ size.toNat) :
    Resources id s context (data.add n) (size - n) := by
  have hs : (size - n).toNat = size.toNat - n.toNat :=
    BitVec.toNat_sub_of_le (by exact hn)
  refine ⟨h.wf, h.contextLive, ?_, h.constants, h.distinct, h.immutable⟩
  have hr := smallRange_add h.inputLive
    (k := n.toNat) (count := (size - n).toNat) (by omega)
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hr

theorem direct_run (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (id : BlockId) (hcore : CoreCallContract core id)
    (E : Env program.Γ) (s : GlobalState) (context data : Pointer) (size : Word)
    (hr : Resources id s context data size) (h : CommonReady E context)
    (hd : E.read (%36) = .value data) (hs : E.read (%37) = .value size) :
    (program core).runFrom E 6 s = .value (.cons (.value context) .nil, directState s context data size) := by
  by_cases hshort : size.toNat < 128
  · simpa only [directState, hshort, ↓reduceIte] using
      direct_short_run core E s context data size h hd hs hr.contextLive hr.inputLive hr.distinct hshort
  · have hlong : 128 ≤ size.toNat := by omega
    have hn := (append_core_count size hlong).1
    have hblocks : 128 * (size >>> 7).toNat ≤ size.toNat := by
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega
    have hchain : SmallRange s.mem (context.add 128#64) 64 :=
      smallRange_add hr.contextLive (by decide)
    have hc := hcore s (context.add 128#64) data (size >>> 7) hr.wf hchain
      (smallRange_mono hr.inputLive hblocks) hr.constants hn hr.immutable (Or.inl hr.distinct)
    have ha := hr.compress data (size >>> 7).toNat
    simpa only [directState, hshort, ↓reduceIte] using
      direct_blocks_run core E s _ context data size h hd hs ha.contextLive ha.inputLive hr.distinct hlong hc

theorem run (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (id : BlockId) (hcore : CoreCallContract core id)
    (s : GlobalState) (context data : Pointer) (size : Word)
    (hr : Resources id s context data size)
    (hused : (s.mem.readAt (context.add 200#64) 64).toNat < 128) :
    (program core).run (program.args (.value context) (.value data) (.value size)) s =
      .value (.cons (.value context) .nil, resultState s context data size) := by
  by_cases hz : size = 0#64
  · subst size
    simpa only [resultState, ↓reduceIte] using zero_run core (.value context) (.value data) s
  · obtain ⟨E, hE, hdata, hsize, hu, hdirect, he⟩ := entry_nonempty core s context data size hz hr.contextLive
    rw [he]
    let used := s.mem.readAt (context.add 200#64) 64
    have huEq : s.mem.readAt (context.add 200#64) 64 = used := rfl
    let t := startState s context size
    have ht : Resources id t context data size := hr.start
    by_cases hu0 : used = 0#64
    · have hd := hdirect hu0
      simpa only [resultState, huEq, hz, hu0, ↓reduceIte] using
        direct_run core id hcore E t context data size ht hE hd.1 hd.2
    · by_cases hshort : size.toNat < (128#64 - used).toNat
      · simpa only [resultState, huEq, hz, hu0, hshort, ↓reduceIte] using
          buffer_short_run core E t context data used size hE hdata hsize hu
            ht.contextLive ht.inputLive hused hshort hr.distinct
      · have hlong : (128#64 - used).toNat ≤ size.toNat := by omega
        let filled := fillState t context data used
        let after := compressionState filled (context.add 128#64) context 1
        have hf : Resources id filled context data size := ht.fill used
        have ha : Resources id after context data size := hf.compress context 1
        have hchain : SmallRange filled.mem (context.add 128#64) 64 :=
          smallRange_add hf.contextLive (by decide)
        have hinput : SmallRange filled.mem context (128 * (1#64).toNat) :=
          smallRange_mono hf.contextLive (by decide)
        have hdis : (Range.of (context.add 128#64) 512).Disjoint (Range.of context 1024) := by
          simpa using smallRange_disjoint_offsets hf.contextLive
            (i := 128) (countI := 64) (j := 0) (countJ := 128)
            (by decide) (by decide) (Or.inr (by decide))
        have hc := hcore filled (context.add 128#64) context 1#64 hf.wf hchain
          hinput hf.constants (by decide) hr.immutable hdis
        change core (.cons (.value (context.add 128#64)) (.cons (.value context)
          (.cons (.value 1#64) .nil))) filled = .value (.nil, after) at hc
        obtain ⟨F, hF, hdF, hsF, hb⟩ := buffer_fill_run core E t after context data used size
          hE hdata hsize hu ht.contextLive ht.inputLive ha.contextLive hused hlong hr.distinct hc
        have hnext := (ha.reset).advance (128#64 - used) hlong
        have hout := direct_run core id hcore F (resetState after context) context
          (data.add (128#64 - used)) (size - (128#64 - used)) hnext hF hdF hsF
        simpa only [resultState, huEq, hz, hu0, hshort, ↓reduceIte] using hb.trans hout

theorem call (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (id : BlockId) (hcore : CoreCallContract core id)
    (s : GlobalState) (context data : Pointer) (size : Word)
    (hr : Resources id s context data size)
    (hused : (s.mem.readAt (context.add 200#64) 64).toNat < 128) :
    (program core).call (program.args (.value context) (.value data) (.value size)) s =
      .value (.cons (.value context) .nil, resultState s context data size) := by
  have h := Func.call_of_run (run core id hcore s context data size hr hused)
  simpa only [result_erase s context data size hr.wf] using h

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
