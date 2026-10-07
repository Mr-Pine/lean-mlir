import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendSemanticFill

/-! The exact append memory specification refines the independent pure stream
transition for every branch and every chunk represented by a live input slice. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

theorem result_rep (s : GlobalState) (p data : Pointer) (size : Word) (q : StreamSpec.Context)
    (h : MemRep s.mem p q) (hi : SmallRange s.mem data size.toNat) (hne : p.id ≠ data.id) :
    MemRep (resultState s p data size).mem p
      (StreamSpec.append q (readBytes s.mem data size.toNat)) := by
  by_cases hz : size = 0#64
  · subst size
    have hnil : readBytes s.mem data (0#64).toNat = [] := rfl
    rw [hnil, StreamSpec.append_short q [] (by simpa using h.bound)]
    simpa only [resultState, ↓reduceIte, List.append_nil, List.length_nil,
      Nat.mul_zero, BitVec.add_zero] using h
  · let used := s.mem.readAt (p.add 200#64) 64
    let t := startState s p size
    let chunk := readBytes s.mem data size.toNat
    let qT : StreamSpec.Context := ⟨q.chain, q.buffer, q.bitCount + BitVec.ofNat 128 (8 * size.toNat)⟩
    have hused : used.toNat = q.buffer.length := h.used
    have hfill : (128#64 - used).toNat = 128 - q.buffer.length := by
      rw [BitVec.toNat_sub_of_le (by change used.toNat ≤ 128; have := h.bound; omega), hused]
      rfl
    have hstart : MemRep t.mem p qT := start_rep s p q size h
    have hw : BlockWrites p.id s.mem t.mem := counter_writes _ _ _ _ _
    have hiT : SmallRange t.mem data size.toNat := hw.live hi
    have hchunk : readBytes t.mem data size.toNat = chunk := writes_bytes p.id s.mem t.mem hw data size.toNat hne
    simp only [resultState, hz, ↓reduceIte]
    change MemRep
      (if used = 0#64 then directState t p data size else
       if size.toNat < (128#64 - used).toNat then shortState t p data used size else
       directState (filledResult t p data used) p (data.add (128#64 - used)) (size - (128#64 - used))).mem
      p (StreamSpec.append q chunk)
    by_cases hu0 : used = 0#64
    · simp only [hu0, ↓reduceIte]
      have hbuf : q.buffer = [] := List.length_eq_zero_iff.mp (by rw [← hused, hu0]; rfl)
      rw [StreamSpec.append_empty_buffer q chunk hbuf]
      have hr := direct_rep t p data qT size hstart hbuf hiT hne
      simpa only [qT, hchunk, chunk, readBytes_length] using hr
    · simp only [hu0, ↓reduceIte]
      by_cases hshort : size.toNat < (128#64 - used).toNat
      · simp only [hshort, ↓reduceIte]
        have hb : q.buffer.length + size.toNat < 128 := by omega
        rw [StreamSpec.append_short q chunk (by simpa only [chunk, readBytes_length] using hb)]
        have hr := short_rep t p data qT used size hstart hused hiT hb
        simpa only [qT, hchunk, chunk, readBytes_length] using hr
      · simp only [hshort, ↓reduceIte]
        have hlong : (128#64 - used).toNat ≤ size.toNat := by omega
        have hfull : 128 - q.buffer.length ≤ size.toNat := by omega
        let first := filledResult t p data used
        let qF : StreamSpec.Context :=
          ⟨Spec.compressBlockBytes q.chain (StreamSpec.filledBlock q.buffer chunk), [],
           q.bitCount + BitVec.ofNat 128 (8 * size.toNat)⟩
        have hfirst : MemRep first.mem p qF := by
          have hf := filled_rep t p data qT used size hstart hused hiT hfull
          simpa only [qT, hchunk] using hf
        have hins := filled_input_live t p data used size hiT hlong
        have hsuffix : readBytes first.mem (data.add (128#64 - used)) (size - (128#64 - used)).toNat =
            chunk.drop (128 - q.buffer.length) := by
          rw [filled_suffix t p data used size hne hlong, hchunk, hfill]
        have hr := direct_rep first p (data.add (128#64 - used)) qF (size - (128#64 - used))
          hfirst rfl hins hne
        rw [StreamSpec.append_filled q chunk h.bound (by simpa only [chunk, readBytes_length] using hfull)]
        simpa only [qF, hsuffix, chunk, readBytes_length] using hr

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.Semantic
