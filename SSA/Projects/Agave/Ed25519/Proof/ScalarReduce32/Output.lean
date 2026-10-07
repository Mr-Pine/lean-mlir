import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Stores
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekIdentityMemory
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekScalarCanonical

/-!
Frame and readback for the actual scalar output-store phase, followed by the
Dalek adapter. The adapter's exact call equation is an explicit remaining
obligation, not a theorem asserting execution of the entire reducer.
-/
namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open Verifier.Execution.Dalek

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- Each source-order output store preserves all previously live ranges. -/
theorem storeBytes_live (m : MemoryState) (out q : Pointer) (bytes : Bytes)
    (count : Nat) (h : SmallRange m q count) :
    SmallRange (storeBytes m out bytes) q count := by
  have h0 := h.storeAt out (bytes 0)
  have h1 := h0.storeAt (out.add 1#64) (bytes 1)
  have h2 := h1.storeAt (out.add 2#64) (bytes 2)
  have h3 := h2.storeAt (out.add 3#64) (bytes 3)
  have h4 := h3.storeAt (out.add 4#64) (bytes 4)
  have h5 := h4.storeAt (out.add 5#64) (bytes 5)
  have h6 := h5.storeAt (out.add 6#64) (bytes 6)
  have h7 := h6.storeAt (out.add 7#64) (bytes 7)
  have h8 := h7.storeAt (out.add 8#64) (bytes 8)
  have h9 := h8.storeAt (out.add 9#64) (bytes 9)
  have h10 := h9.storeAt (out.add 10#64) (bytes 10)
  have h11 := h10.storeAt (out.add 11#64) (bytes 11)
  have h12 := h11.storeAt (out.add 12#64) (bytes 12)
  have h13 := h12.storeAt (out.add 13#64) (bytes 13)
  have h14 := h13.storeAt (out.add 14#64) (bytes 14)
  have h15 := h14.storeAt (out.add 15#64) (bytes 15)
  have h16 := h15.storeAt (out.add 16#64) (bytes 16)
  have h17 := h16.storeAt (out.add 17#64) (bytes 17)
  have h18 := h17.storeAt (out.add 18#64) (bytes 18)
  have h19 := h18.storeAt (out.add 19#64) (bytes 19)
  have h20 := h19.storeAt (out.add 20#64) (bytes 20)
  have h21 := h20.storeAt (out.add 21#64) (bytes 21)
  have h22 := h21.storeAt (out.add 22#64) (bytes 22)
  have h23 := h22.storeAt (out.add 23#64) (bytes 23)
  have h24 := h23.storeAt (out.add 24#64) (bytes 24)
  have h25 := h24.storeAt (out.add 25#64) (bytes 25)
  have h26 := h25.storeAt (out.add 26#64) (bytes 26)
  have h27 := h26.storeAt (out.add 27#64) (bytes 27)
  have h28 := h27.storeAt (out.add 28#64) (bytes 28)
  have h29 := h28.storeAt (out.add 29#64) (bytes 29)
  have h30 := h29.storeAt (out.add 30#64) (bytes 30)
  have h31 := h30.storeAt (out.add 31#64) (bytes 31)
  exact h31

/-- The 32 actual byte stores change only the allocated output range. -/
theorem storeBytes_frame (s : GlobalState) (out : Pointer) (bytes : Bytes)
    (hwf : s.WF) (hr : SmallRange s.mem out 32) :
    OutputFrame s {s with mem := storeBytes s.mem out bytes} out 32 := by
  constructor
  · simpa only [storeBytes,
      GlobalState.WF_storeAt] using hwf
  · intro q n hq
    exact storeBytes_live s.mem out q bytes n hq
  · intro q w hd
    have hd0 := disjoint_add_subrange hr hd (k := 0) (count := 1) (by decide)
    have hd1 := disjoint_add_subrange hr hd (k := 1) (count := 1) (by decide)
    have hd2 := disjoint_add_subrange hr hd (k := 2) (count := 1) (by decide)
    have hd3 := disjoint_add_subrange hr hd (k := 3) (count := 1) (by decide)
    have hd4 := disjoint_add_subrange hr hd (k := 4) (count := 1) (by decide)
    have hd5 := disjoint_add_subrange hr hd (k := 5) (count := 1) (by decide)
    have hd6 := disjoint_add_subrange hr hd (k := 6) (count := 1) (by decide)
    have hd7 := disjoint_add_subrange hr hd (k := 7) (count := 1) (by decide)
    have hd8 := disjoint_add_subrange hr hd (k := 8) (count := 1) (by decide)
    have hd9 := disjoint_add_subrange hr hd (k := 9) (count := 1) (by decide)
    have hd10 := disjoint_add_subrange hr hd (k := 10) (count := 1) (by decide)
    have hd11 := disjoint_add_subrange hr hd (k := 11) (count := 1) (by decide)
    have hd12 := disjoint_add_subrange hr hd (k := 12) (count := 1) (by decide)
    have hd13 := disjoint_add_subrange hr hd (k := 13) (count := 1) (by decide)
    have hd14 := disjoint_add_subrange hr hd (k := 14) (count := 1) (by decide)
    have hd15 := disjoint_add_subrange hr hd (k := 15) (count := 1) (by decide)
    have hd16 := disjoint_add_subrange hr hd (k := 16) (count := 1) (by decide)
    have hd17 := disjoint_add_subrange hr hd (k := 17) (count := 1) (by decide)
    have hd18 := disjoint_add_subrange hr hd (k := 18) (count := 1) (by decide)
    have hd19 := disjoint_add_subrange hr hd (k := 19) (count := 1) (by decide)
    have hd20 := disjoint_add_subrange hr hd (k := 20) (count := 1) (by decide)
    have hd21 := disjoint_add_subrange hr hd (k := 21) (count := 1) (by decide)
    have hd22 := disjoint_add_subrange hr hd (k := 22) (count := 1) (by decide)
    have hd23 := disjoint_add_subrange hr hd (k := 23) (count := 1) (by decide)
    have hd24 := disjoint_add_subrange hr hd (k := 24) (count := 1) (by decide)
    have hd25 := disjoint_add_subrange hr hd (k := 25) (count := 1) (by decide)
    have hd26 := disjoint_add_subrange hr hd (k := 26) (count := 1) (by decide)
    have hd27 := disjoint_add_subrange hr hd (k := 27) (count := 1) (by decide)
    have hd28 := disjoint_add_subrange hr hd (k := 28) (count := 1) (by decide)
    have hd29 := disjoint_add_subrange hr hd (k := 29) (count := 1) (by decide)
    have hd30 := disjoint_add_subrange hr hd (k := 30) (count := 1) (by decide)
    have hd31 := disjoint_add_subrange hr hd (k := 31) (count := 1) (by decide)
    simp only [Pointer.add_zero] at hd0
    let m0 := s.mem
    let m1 := m0.storeAt out (bytes 0)
    let m2 := m1.storeAt (out.add 1#64) (bytes 1)
    let m3 := m2.storeAt (out.add 2#64) (bytes 2)
    let m4 := m3.storeAt (out.add 3#64) (bytes 3)
    let m5 := m4.storeAt (out.add 4#64) (bytes 4)
    let m6 := m5.storeAt (out.add 5#64) (bytes 5)
    let m7 := m6.storeAt (out.add 6#64) (bytes 6)
    let m8 := m7.storeAt (out.add 7#64) (bytes 7)
    let m9 := m8.storeAt (out.add 8#64) (bytes 8)
    let m10 := m9.storeAt (out.add 9#64) (bytes 9)
    let m11 := m10.storeAt (out.add 10#64) (bytes 10)
    let m12 := m11.storeAt (out.add 11#64) (bytes 11)
    let m13 := m12.storeAt (out.add 12#64) (bytes 12)
    let m14 := m13.storeAt (out.add 13#64) (bytes 13)
    let m15 := m14.storeAt (out.add 14#64) (bytes 14)
    let m16 := m15.storeAt (out.add 15#64) (bytes 15)
    let m17 := m16.storeAt (out.add 16#64) (bytes 16)
    let m18 := m17.storeAt (out.add 17#64) (bytes 17)
    let m19 := m18.storeAt (out.add 18#64) (bytes 18)
    let m20 := m19.storeAt (out.add 19#64) (bytes 19)
    let m21 := m20.storeAt (out.add 20#64) (bytes 20)
    let m22 := m21.storeAt (out.add 21#64) (bytes 21)
    let m23 := m22.storeAt (out.add 22#64) (bytes 22)
    let m24 := m23.storeAt (out.add 23#64) (bytes 23)
    let m25 := m24.storeAt (out.add 24#64) (bytes 24)
    let m26 := m25.storeAt (out.add 25#64) (bytes 25)
    let m27 := m26.storeAt (out.add 26#64) (bytes 26)
    let m28 := m27.storeAt (out.add 27#64) (bytes 27)
    let m29 := m28.storeAt (out.add 28#64) (bytes 28)
    let m30 := m29.storeAt (out.add 29#64) (bytes 29)
    let m31 := m30.storeAt (out.add 30#64) (bytes 30)
    let m32 := m31.storeAt (out.add 31#64) (bytes 31)
    change m32.readAt q w = m0.readAt q w
    calc
      m32.readAt q w = m31.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m31) (v := 8) hd31.symm (bytes 31)
      _ = m30.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m30) (v := 8) hd30.symm (bytes 30)
      _ = m29.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m29) (v := 8) hd29.symm (bytes 29)
      _ = m28.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m28) (v := 8) hd28.symm (bytes 28)
      _ = m27.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m27) (v := 8) hd27.symm (bytes 27)
      _ = m26.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m26) (v := 8) hd26.symm (bytes 26)
      _ = m25.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m25) (v := 8) hd25.symm (bytes 25)
      _ = m24.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m24) (v := 8) hd24.symm (bytes 24)
      _ = m23.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m23) (v := 8) hd23.symm (bytes 23)
      _ = m22.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m22) (v := 8) hd22.symm (bytes 22)
      _ = m21.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m21) (v := 8) hd21.symm (bytes 21)
      _ = m20.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m20) (v := 8) hd20.symm (bytes 20)
      _ = m19.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m19) (v := 8) hd19.symm (bytes 19)
      _ = m18.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m18) (v := 8) hd18.symm (bytes 18)
      _ = m17.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m17) (v := 8) hd17.symm (bytes 17)
      _ = m16.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m16) (v := 8) hd16.symm (bytes 16)
      _ = m15.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m15) (v := 8) hd15.symm (bytes 15)
      _ = m14.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m14) (v := 8) hd14.symm (bytes 14)
      _ = m13.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m13) (v := 8) hd13.symm (bytes 13)
      _ = m12.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m12) (v := 8) hd12.symm (bytes 12)
      _ = m11.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m11) (v := 8) hd11.symm (bytes 11)
      _ = m10.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m10) (v := 8) hd10.symm (bytes 10)
      _ = m9.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m9) (v := 8) hd9.symm (bytes 9)
      _ = m8.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m8) (v := 8) hd8.symm (bytes 8)
      _ = m7.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m7) (v := 8) hd7.symm (bytes 7)
      _ = m6.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m6) (v := 8) hd6.symm (bytes 6)
      _ = m5.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m5) (v := 8) hd5.symm (bytes 5)
      _ = m4.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m4) (v := 8) hd4.symm (bytes 4)
      _ = m3.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m3) (v := 8) hd3.symm (bytes 3)
      _ = m2.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m2) (v := 8) hd2.symm (bytes 2)
      _ = m1.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m1) (v := 8) hd1.symm (bytes 1)
      _ = m0.readAt q w :=
        MemoryState.readAt_storeAt_disjoint (m := m0) (v := 8) hd0.symm (bytes 0)

/-- Execute the exact source store slice and observe every canonical byte. -/
theorem store_phase_output (E : Env program.Γ) (out : Pointer)
    (s : GlobalState) (bits : BitVec 256) (hwf : s.WF)
    (hr : SmallRange s.mem out 32) (hout : E.read (%arg0) = .value out) :
    ∃ after,
      storeProgram.runFrom (storeEnv E (fun i => bits.extractLsb' (8 * i.val) 8)) 0 s =
        .value (.nil, after) ∧
      OutputFrame s after out 32 ∧ ReadBytes after out 32 bits := by
  refine ⟨{s with mem := storeBytes s.mem out (fun i => bits.extractLsb' (8 * i.val) 8)},
    store_run E out _ s hr hout, storeBytes_frame s out _ hwf hr, ?_⟩
  exact ⟨storeBytes_live s.mem out out (fun i => bits.extractLsb' (8 * i.val) 8) 32 hr,
    storeBytes_read s.mem out bits hr⟩

/-- Observable memory shape expected after private frame reclamation. -/
def resultState (s : GlobalState) (out : Pointer) (bits : BitVec 256)
    (allocations : Nat) : GlobalState :=
  { s with
    mem := storeBytes s.mem out (fun i => bits.extractLsb' (8 * i.val) 8)
    alloc := ⟨s.alloc.nextFreeBlock + allocations⟩ }

theorem resultState_frame (s : GlobalState) (out : Pointer) (bits : BitVec 256)
    (allocations : Nat) (hwf : s.WF) (hr : SmallRange s.mem out 32) :
    OutputFrame s (resultState s out bits allocations) out 32 := by
  have hf := storeBytes_frame s out (fun i => bits.extractLsb' (8 * i.val) 8) hwf hr
  exact ⟨hf.wellFormed.add_blocks, hf.live, hf.read⟩

theorem resultState_read (s : GlobalState) (out : Pointer) (bits : BitVec 256)
    (allocations : Nat) (hr : SmallRange s.mem out 32) :
    ReadBytes (resultState s out bits allocations) out 32 bits :=
  ⟨storeBytes_live s.mem out out (fun i => bits.extractLsb' (8 * i.val) 8) 32 hr, storeBytes_read s.mem out bits hr⟩

/-- Once the exact imported call equation is established, no extra output,
frame, canonicality, or caller adaptation premise is required. There are 33
private reducer allocations and one private allocation in black_box. -/
theorem contract_of_call_equation (layout : Layout Point Scalar Result)
    (hlayout : ∀ bits, layout.reduce bits = reduceScalarBytes bits)
    (hexec : ∀ (out input : Pointer) (state : GlobalState) (bits : BitVec 256),
      state.WF → SmallRange state.mem out 32 → ReadBytes state input 32 bits →
      (Range.of out 256).Disjoint (Range.of input 256) →
      program.call (args2 out input) state =
        .value (.nil, resultState state out (reduceScalarBytes bits) 34)) :
    ScalarReduceContract program.call layout := by
  intro out input state bits hwf hr hb hd
  refine ⟨resultState state out (reduceScalarBytes bits) 34,
    hexec out input state bits hwf hr hb hd,
    resultState_frame state out (reduceScalarBytes bits) 34 hwf hr, ?_⟩
  rw [hlayout]
  exact resultState_read state out (reduceScalarBytes bits) 34 hr

end Agave.Ed25519.ScalarReduce32.Execution
