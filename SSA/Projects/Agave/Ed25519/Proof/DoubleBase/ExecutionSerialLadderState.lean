import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialLadderRegisters
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.ResidualRepresentation

/-! Concrete live-memory invariant of the serial descending loop. Table
invariants describe bounded cached odd multiples; digit bytes are the source
NAF digits. The frame admits writes only in the seven allocated scratch objects. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open SerialContracts (WritesOnly readField readCached readAffineCached)

structure SerialLadderHelpers (p : SerialCFG.Primitives) : Prop where
  double : SerialContracts.UnaryPointContract p.call1 120
    SerialContracts.readProjective SerialPoint.doubleCompleted
  multiply : p.call2 = SerialFieldMul.kernel.call
  cachedSub : SerialContracts.BinaryPointContract p.call3 160 readCached SerialPoint.cachedSubCompleted
  cachedAdd : SerialContracts.BinaryPointContract p.call5 160 readCached SerialPoint.cachedAddCompleted
  affineSub : SerialContracts.BinaryPointContract p.call6 120 readAffineCached
    (fun P C => SerialPoint.affineSubCompleted P C.X C.Y C.T)
  affineAdd : SerialContracts.BinaryPointContract p.call7 120 readAffineCached
    (fun P C => SerialPoint.affineAddCompleted P C.X C.Y C.T)
  square : p.call8 = Encoding.Decompress.Execution.Pow2k.program.call

structure SerialScratchFrame (slots : Fin 7 → Pointer) (before after : GlobalState) : Prop where
  wellFormed : after.WF
  allocationMonotone : before.alloc.nextFreeBlock ≤ after.alloc.nextFreeBlock
  allocationShape : ∀ id : BlockId,
    (after.mem[id]?).map MemoryBlock.length = (before.mem[id]?).map MemoryBlock.length
  readFrame : ∀ q bits, (∀ i, (slots i).id ≠ q.id) →
    after.mem.readAt q bits = before.mem.readAt q bits

variable {slots : Fin 7 → Pointer}

theorem SerialScratchFrame.refl (hwf : s.WF) : SerialScratchFrame slots s s :=
  ⟨hwf, le_refl _, fun _ => rfl, fun _ _ _ => rfl⟩

theorem SerialScratchFrame.trans (h₁ : SerialScratchFrame slots s₀ s₁)
    (h₂ : SerialScratchFrame slots s₁ s₂) : SerialScratchFrame slots s₀ s₂ :=
  ⟨h₂.wellFormed, h₁.allocationMonotone.trans h₂.allocationMonotone,
    fun id => (h₂.allocationShape id).trans (h₁.allocationShape id),
    fun q bits hd => (h₂.readFrame q bits hd).trans (h₁.readFrame q bits hd)⟩

theorem SerialScratchFrame.of_writesOnly (i : Fin 7)
    (h : WritesOnly (slots i) bytes s t) : SerialScratchFrame slots s t :=
  ⟨h.wellFormed, h.allocationMonotone, h.allocationShape,
    fun q bits hd => h.readFrame q bits (Range.disjoint_of_id_ne (hd i).symm)⟩

theorem SerialScratchFrame.buffer (h : SerialScratchFrame slots s t)
    (hr : Buffer s.mem q bytes) : Buffer t.mem q bytes := by
  obtain ⟨b, hb, hs, hz⟩ := hr
  have he := h.allocationShape q.id
  rw [hb] at he
  cases ht : t.mem[q.id]? with
  | none => simp [ht] at he
  | some b' =>
      have hlen : b'.length = b.length := by simpa [ht] using he
      exact ⟨b', ht, by omega, by omega⟩

theorem SerialScratchFrame.readField (h : SerialScratchFrame slots s t)
    (hq : ∀ i, (slots i).id ≠ q.id) : readField t q = readField s q := by
  funext i
  change (t.mem.readAt (q.add (BitVec.ofNat 64 (8*i.val))) 64).toNat =
    (s.mem.readAt (q.add (BitVec.ofNat 64 (8*i.val))) 64).toNat
  rw [h.readFrame _ _ (by simpa only [Pointer.add_id] using hq)]

theorem SerialScratchFrame.readCached (h : SerialScratchFrame slots s t)
    (hq : ∀ i, (slots i).id ≠ q.id) : readCached t q = readCached s q := by
  apply PointArithmetic.Extended.ext
  all_goals exact h.readField (by simpa only [Pointer.add_id] using hq)

theorem SerialScratchFrame.readAffineCached (h : SerialScratchFrame slots s t)
    (hq : ∀ i, (slots i).id ≠ q.id) : readAffineCached t q = readAffineCached s q := by
  apply PointArithmetic.Extended.ext
  all_goals first | rfl | exact h.readField (by simpa only [Pointer.add_id] using hq)

def serialScratchBytes (i : Fin 7) : Nat := if i = 0 ∨ i = 6 then 120 else 160

structure SerialLadderMemory (slots : Fin 7 → Pointer) (tableA tableB da db : Pointer)
    (a b : Nat) (A B : GroupPoint) (s : GlobalState) : Prop where
  wellFormed : s.WF
  scratch : ∀ i, Buffer s.mem (slots i) (serialScratchBytes i)
  tableABuffer : Buffer s.mem tableA 1280
  tableBBuffer : Buffer s.mem tableB 7680
  digitsA : Buffer s.mem da 256
  digitsB : Buffer s.mem db 256
  separate : ∀ i j, i ≠ j → (slots i).id ≠ (slots j).id
  separateA : ∀ i, (slots i).id ≠ tableA.id
  separateB : ∀ i, (slots i).id ≠ tableB.id
  separateDigitsA : ∀ i, (slots i).id ≠ da.id
  separateDigitsB : ∀ i, (slots i).id ≠ db.id
  readA : ∀ i : Fin 256, s.mem.readAt (da.add (BitVec.ofNat 64 i.val)) 8 =
    BitVec.ofInt 8 (NAF.sourceDigits 5 a i)
  readB : ∀ i : Fin 256, s.mem.readAt (db.add (BitVec.ofNat 64 i.val)) 8 =
    BitVec.ofInt 8 (NAF.sourceDigits 8 b i)
  cachedA : ∀ k : Fin 8,
    SerialPoint.PointBounded (readCached s (tableA.add (BitVec.ofNat 64 (160 * k.val)))) ∧
    ∃ Q, Tables.Represents Q ((2*k.val+1) • A) ∧
      SerialPoint.pointValue (readCached s (tableA.add (BitVec.ofNat 64 (160*k.val)))) =
        PointArithmetic.serialCache _root_.Ed25519.d Q
  cachedB : ∀ k : Fin 64,
    SerialPoint.PointBounded (readAffineCached s (tableB.add (BitVec.ofNat 64 (120 * k.val)))) ∧
    ∃ Q, Tables.Represents Q ((2*k.val+1) • B) ∧
      SerialPoint.affineCacheValue (readAffineCached s (tableB.add (BitVec.ofNat 64 (120*k.val)))) =
        PointArithmetic.serialCache _root_.Ed25519.d Q

theorem SerialLadderMemory.preserve
    (h : SerialLadderMemory slots tableA tableB da db a b A B s)
    (hf : SerialScratchFrame slots s t) :
    SerialLadderMemory slots tableA tableB da db a b A B t := by
  refine ⟨hf.wellFormed, fun i => hf.buffer (h.scratch i), hf.buffer h.tableABuffer,
    hf.buffer h.tableBBuffer, hf.buffer h.digitsA, hf.buffer h.digitsB,
    h.separate, h.separateA, h.separateB, h.separateDigitsA, h.separateDigitsB, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hf.readFrame _ _ (by simpa only [Pointer.add_id] using h.separateDigitsA)]
    exact h.readA i
  · intro i
    rw [hf.readFrame _ _ (by simpa only [Pointer.add_id] using h.separateDigitsB)]
    exact h.readB i
  · intro k
    rw [hf.readCached (by simpa only [Pointer.add_id] using h.separateA)]
    exact h.cachedA k
  · intro k
    rw [hf.readAffineCached (by simpa only [Pointer.add_id] using h.separateB)]
    exact h.cachedB k

theorem projectiveRoundState_scratchFrame (s : GlobalState) (slots : Fin 7 → Pointer)
    (hwf : s.WF) : SerialScratchFrame slots s (projectiveRoundState s (slots 0) (slots 5) (slots 6)) := by
  refine ⟨projectiveRoundState_wf _ _ _ _ hwf, le_refl _, ?_, ?_⟩
  · intro id
    simp only [projectiveRoundState, projectiveState, fieldState,
      SerialPoint.Execution.storeLimbs_allocationShape, SerialPoint.Execution.storeAt_allocationShape]
  · intro q bits hd
    exact projectiveRoundState_readFrame s _ _ _ q bits (hd 0) (hd 6)

end Agave.Ed25519.DoubleBase.RIR
