import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialLadderRound
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialLadderLinked

/-! Inclusive descending serial ladder and exact verifier output. The loop
induction executes every round and the real non-underflowing backedge. The
concrete specialization discharges every arithmetic-helper premise. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open Verifier.Execution
set_option maxRecDepth 10000

variable {p : SerialCFG.Primitives} {g : SerialCFG.Globals} {slots : Fin 7 → Pointer}
  {tableA tableB da db : Pointer} {a b : Nat} {A B V : GroupPoint}
  {E : ⟪serialKernel.Γ⟫} {s : GlobalState}

theorem serial_ladder_backedge_ready (n : Nat) (hn : n + 1 < 256)
    (hr : SerialLadderRegisters slots tableA tableB da db E)
    (hi : E.read (%131) = .value (BitVec.ofNat 64 (n + 1))) :
    ∃ E', (serialKernel p g).runFrom E 35 s = (serialKernel p g).runFrom E' 18 s ∧
      SerialLadderRegisters slots tableA tableB da db E' ∧
      E'.read (%131) = .value (BitVec.ofNat 64 n) ∧ E'.args = E.args := by
  have he : backedgeInput E ⟨n, by omega⟩ = E := by
    unfold backedgeInput
    rw [Env.write_of_read E (%19) hr.r19, Env.write_of_read E (%131) hi]
  have hrun := serial_ladder_backedge p g E ⟨n, by omega⟩ s
  rw [he] at hrun
  have hf : PrefixEq E (E[%160 := .value (BitVec.ofNat 64 n),
      %131 := .value (BitVec.ofNat 64 n)]) 131 := by
    iterate 2 apply PrefixEq.write (hi := by decide)
    exact PrefixEq.refl _ _
  exact ⟨_, hrun, hr.of_frame hf, by simp [mlir_env], hf.1⟩

/-- All source digits from the selected starting index through zero execute.
The only call contracts are the independently proved local point primitives. -/
theorem serial_ladder_run (hh : SerialLadderHelpers p) (n : Nat) (hn : n < 256)
    (hr : SerialLadderRegisters slots tableA tableB da db E)
    (hi : E.read (%131) = .value (BitVec.ofNat 64 n))
    (hm : SerialLadderMemory slots tableA tableB da db a b A B s)
    (hP : SerialProjectiveAt slots s V) :
    ∃ E' s', (serialKernel p g).runFrom E 18 s = (serialKernel p g).runFrom E' 34 s' ∧
      SerialLadderRegisters slots tableA tableB da db E' ∧
      E'.read (%131) = .value 0#64 ∧
      SerialLadderMemory slots tableA tableB da db a b A B s' ∧
      SerialScratchFrame slots s s' ∧
      SerialProjectiveAt slots s' (groupLadder A B V (nafDigits 5 a) (nafDigits 8 b) n) ∧
      E'.args = E.args := by
  induction n generalizing E s V with
  | zero =>
      obtain ⟨ER, sr, hrun, hr', hi', hm', hf, hp', ha⟩ :=
        serial_ladder_round (g := g) hh hr (i := ⟨0, hn⟩) hi hm hP
      refine ⟨ER, sr, ?_, hr', hi', hm', hf, ?_, ha⟩
      · simpa only [Fin.val_zero, ite_true] using hrun
      · simpa only [groupLadder_zero] using hp'
  | succ n ih =>
      obtain ⟨ER, sr, hrun, hr', hi', hm', hf, hp', ha⟩ :=
        serial_ladder_round (g := g) hh hr (i := ⟨n + 1, hn⟩) hi hm hP
      have hrun' : (serialKernel p g).runFrom E 18 s = (serialKernel p g).runFrom ER 35 sr := by
        simpa only [Fin.val_mk, Nat.add_one_ne_zero, ite_false] using hrun
      obtain ⟨EN, hback, hrN, hiN, haN⟩ := serial_ladder_backedge_ready (g := g) n hn hr' hi'
      obtain ⟨EF, sf, hrest, hrF, hiF, hmF, hfF, hpF, haF⟩ := ih (by omega) hrN hiN hm' hp'
      refine ⟨EF, sf, hrun'.trans (hback.trans hrest), hrF, hiF, hmF, hf.trans hfF, ?_,
        haF.trans (haN.trans ha)⟩
      simpa only [groupLadder_succ] using hpF

/-- The complete descending ladder and final return block, including exact
noncanonical output bytes and a frame over all caller allocations. -/
theorem serial_ladder_run_validPoint (hh : SerialLadderHelpers p) (n : Nat) (hn : n < 256)
    (hr : SerialLadderRegisters slots tableA tableB da db E)
    (hi : E.read (%131) = .value (BitVec.ofNat 64 n))
    (hm : SerialLadderMemory slots tableA tableB da db a b A B s)
    (hP : SerialProjectiveAt slots s V) (out : Pointer) (hout : Buffer s.mem out 160)
    (hop : out.id ≠ (slots 6).id) (harg : E.read (%arg0) = .value out) :
    ∃ (P : ValidPoint) (final : GlobalState),
      (serialKernel p g).runFrom E 18 s = .value (.nil, final) ∧ final.WF ∧
      s.alloc.nextFreeBlock ≤ final.alloc.nextFreeBlock ∧
      (∀ id : BlockId, (final.mem[id]?).map MemoryBlock.length = (s.mem[id]?).map MemoryBlock.length) ∧
      P.curve = groupLadder A B V (nafDigits 5 a) (nafDigits 8 b) n ∧
      Dalek.ReadBytes final out 160 P.bytes ∧
      (∀ q bits, (∀ i, (slots i).id ≠ q.id) →
        (Range.of q bits).Disjoint (Range.of out 1280) →
        final.mem.readAt q bits = s.mem.readAt q bits) := by
  obtain ⟨ER, sr, hrun, hr', _, hm', hf, hp', hargs⟩ := serial_ladder_run (g := g) hh n hn hr hi hm hP
  have harg' : ER.read (%arg0) = .value out := by
    have he : ER.read (%arg0) = E.read (%arg0) := by simp only [Env.read, hargs]
    exact he.trans harg
  have hprojective : Buffer sr.mem (slots 6) 120 := by simpa [serialScratchBytes] using hm'.scratch 6
  obtain ⟨P, hret, hframe, hcurve, hbytes⟩ := serial_return_run_validPoint p g hh.multiply hh.square
    ER out (slots 6) sr hm'.wellFormed (hf.buffer hout) hprojective hop harg'
    (SerialPoint.pointTight_bounded _ hp'.tight) _ hp'.represents
  rw [serialReturnInput_of_registers hr'] at hret
  refine ⟨P, _, hrun.trans hret, hframe.wellFormed,
    hf.allocationMonotone.trans hframe.allocationMonotone,
    fun id => (hframe.allocationShape id).trans (hf.allocationShape id), hcurve, hbytes, ?_⟩
  intro q bits hq hd
  exact (hframe.readFrame q bits hd).trans (hf.readFrame q bits hq)

/-- Closed arithmetic specialization for the exact linked serial function.
Input assumptions are the loop-entry register/memory/table/point invariant,
the ordinary output range and the source 255-bit scalar bounds. No helper,
round, ladder, success or output-representation premise is accepted. -/
theorem serialLinked_ladder_run_validPoint (g : SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : SerialPanic)
    (hr : SerialLadderRegisters slots tableA tableB da db E)
    (hi : E.read (%131) = .value (BitVec.ofNat 64
      (startIndex (nafDigits 5 a) (nafDigits 8 b) 255)))
    (hm : SerialLadderMemory slots tableA tableB da db a b A B s)
    (hP : SerialProjectiveAt slots s 0) (ha : a < 2^255) (hb : b < 2^255)
    (out : Pointer) (hout : Buffer s.mem out 160) (hop : out.id ≠ (slots 6).id)
    (harg : E.read (%arg0) = .value out) :
    ∃ (P : ValidPoint) (final : GlobalState),
      (serialLinkedKernel g d2 panic).runFrom E (18 : Fin 36) s = .value (.nil, final) ∧ final.WF ∧
      s.alloc.nextFreeBlock ≤ final.alloc.nextFreeBlock ∧
      (∀ id : BlockId, (final.mem[id]?).map MemoryBlock.length = (s.mem[id]?).map MemoryBlock.length) ∧
      P.curve = (a : Int) • A + (b : Int) • B ∧
      Dalek.ReadBytes final out 160 P.bytes ∧
      (∀ q bits, (∀ i, (slots i).id ≠ q.id) →
        (Range.of q bits).Disjoint (Range.of out 1280) →
        final.mem.readAt q bits = s.mem.readAt q bits) := by
  have hn : startIndex (nafDigits 5 a) (nafDigits 8 b) 255 < 256 :=
    lt_of_le_of_lt (startIndex_le _ _ _) (by decide)
  simpa only [serialLinkedKernel, groupLadder_naf A B a b ha hb] using
    serial_ladder_run_validPoint (g := g) (serialLinked_ladderHelpers d2 panic) _ hn hr hi hm hP
      out hout hop harg

end Agave.Ed25519.DoubleBase.RIR
