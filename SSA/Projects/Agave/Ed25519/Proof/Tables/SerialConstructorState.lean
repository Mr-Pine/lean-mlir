import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialCacheMemory
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialMemory
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SerialContractsLink

namespace Agave.Ed25519.Tables.SerialConstructorState
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open DoubleBase.SerialContracts (WritesOnly readField readPoint readCached readProjective)
open DoubleBase.RIR (range_disjoint_subrange)
open SerialConstructorContext (GlobalsReady)

abbrev Slots := Fin 7 → Pointer
variable {slots : Slots} {table : Pointer}

def bytes (i : Fin 7) : Nat := if i = 0 then 120 else 160

structure Frame (slots : Slots) (table : Pointer) (before after : GlobalState) : Prop where
  wellFormed : after.WF
  allocationMonotone : before.alloc.nextFreeBlock ≤ after.alloc.nextFreeBlock
  allocationShape : ∀ id : BlockId,
    (after.mem[id]?).map MemoryBlock.length = (before.mem[id]?).map MemoryBlock.length
  readFrame : ∀ q bits, (∀ i, (slots i).id ≠ q.id) → table.id ≠ q.id →
    after.mem.readAt q bits = before.mem.readAt q bits

theorem Frame.refl (hwf : s.WF) : Frame slots table s s :=
  ⟨hwf, le_refl _, fun _ => rfl, fun _ _ _ _ => rfl⟩

theorem Frame.trans (h₁ : Frame slots table s u) (h₂ : Frame slots table u t) :
    Frame slots table s t :=
  ⟨h₂.wellFormed, h₁.allocationMonotone.trans h₂.allocationMonotone,
    fun id => (h₂.allocationShape id).trans (h₁.allocationShape id),
    fun q bits hs ht => (h₂.readFrame q bits hs ht).trans (h₁.readFrame q bits hs ht)⟩

theorem Frame.slot (i : Fin 7) (h : WritesOnly (slots i) count s t) : Frame slots table s t :=
  ⟨h.wellFormed, h.allocationMonotone, h.allocationShape,
    fun q bits hs _ => h.readFrame q bits (Range.disjoint_of_id_ne (hs i).symm)⟩

theorem Frame.tableWrite (h : WritesOnly out count s t) (hid : out.id = table.id) :
    Frame slots table s t :=
  ⟨h.wellFormed, h.allocationMonotone, h.allocationShape,
    fun q bits _ ht => h.readFrame q bits (Range.disjoint_of_id_ne (by rw [hid]; exact ht.symm))⟩

theorem Frame.buffer (h : Frame slots table s t) (hq : Buffer s.mem q count) :
    Buffer t.mem q count := by
  obtain ⟨b, hb, hs, hz⟩ := hq
  have he := h.allocationShape q.id
  rw [hb] at he
  cases ht : t.mem[q.id]? with
  | none => simp [ht] at he
  | some b' =>
      have hl : b'.length = b.length := by simpa [ht] using he
      exact ⟨b', ht, by omega, by omega⟩

theorem field_read_ne (h : WritesOnly out count s t) (hne : out.id ≠ q.id) :
    readField t q = readField s q := by
  funext i
  unfold readField SerialFieldMul.unsigned SerialFieldMul.readLimbs
  rw [h.readFrame _ _ (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hne.symm))]

theorem point_read_ne (h : WritesOnly out count s t) (hne : out.id ≠ q.id) :
    readPoint t q = readPoint s q := by
  apply PointArithmetic.Extended.ext
  all_goals apply field_read_ne h; simpa only [Pointer.add_id] using hne

theorem cached_read_ne (h : WritesOnly out count s t) (hne : out.id ≠ q.id) :
    readCached t q = readCached s q := by
  apply PointArithmetic.Extended.ext
  all_goals apply field_read_ne h; simpa only [Pointer.add_id] using hne

theorem cached_read_frame (h : WritesOnly out count s t) (hq : Buffer s.mem q 160)
    (hd : (Range.of q 1280).Disjoint (Range.of out (8*count))) :
    readCached t q = readCached s q := by
  have hw (c : Fin 4) (i : Fin 5) :
      t.mem.readAt (q.add (BitVec.ofNat 64 (40*c.val + 8*i.val))) 64 =
        s.mem.readAt (q.add (BitVec.ofNat 64 (40*c.val + 8*i.val))) 64 := by
    exact h.readFrame _ _
      (range_disjoint_subrange hq hd.symm (k := 40*c.val+8*i.val) (count := 8)
        (by have := c.isLt; have := i.isLt; omega)).symm
  have hf (c : Fin 4) : readField t (q.add (BitVec.ofNat 64 (40*c.val))) =
      readField s (q.add (BitVec.ofNat 64 (40*c.val))) := by
    funext i
    simp only [readField, SerialFieldMul.unsigned, SerialFieldMul.readLimbs,
      Pointer.add_add, ← BitVec.ofNat_add, hw]
  apply PointArithmetic.Extended.ext
  · exact hf 1
  · simpa [readCached] using hf 0
  · exact hf 2
  · exact hf 3

structure Ready (g : SerialConstructor.Globals) (slots : Slots) (table : Pointer)
    (s : GlobalState) : Prop where
  wf : s.WF
  scratch : ∀ i, Buffer s.mem (slots i) (bytes i)
  tableBuffer : Buffer s.mem table 1280
  globalReady : GlobalsReady g s
  separate : ∀ i j, i ≠ j → (slots i).id ≠ (slots j).id
  separateTable : ∀ i, (slots i).id ≠ table.id

theorem Ready.point (h : Ready g slots table s) (i : Fin 7) (hi : i ≠ 0) :
    Buffer s.mem (slots i) 160 := by simpa only [bytes, if_neg hi] using h.scratch i

theorem Ready.globalSeparate (h : Ready g slots table s) (i : Fin 7) :
    (slots i).id ≠ g.address0.id := h.globalReady.separate (h.scratch i) (by unfold bytes; split <;> decide)

theorem Ready.preserve (h : Ready g slots table s) (hf : Frame slots table s t) :
    Ready g slots table t := by
  refine ⟨hf.wellFormed, fun i => hf.buffer (h.scratch i), hf.buffer h.tableBuffer,
    ⟨h.globalReady.offsetZero, ?_⟩, h.separate, h.separateTable⟩
  have hs := hf.allocationShape g.address0.id
  rw [h.globalReady.present] at hs
  cases hb : t.mem[g.address0.id]? with
  | none => simp [hb] at hs
  | some b =>
      have hl : b.length = 40 := by simpa [hb, serialD2Global] using hs
      cases b with
      | mk n value =>
          dsimp only at hl
          subst n
          have hr := hf.readFrame g.address0 320 h.globalSeparate
            (h.globalReady.separate h.tableBuffer (by decide))
          have hbefore : s.mem.readAt g.address0 320 = serialD2Bytes := by
            rw [h.globalReady.address]
            exact h.globalReady.present.readAt
          have hafter : t.mem.readAt g.address0 320 = value := by
            simp [MemoryState.readAt, hb, Pointer.offsetInBits, h.globalReady.offsetZero]
          rw [hbefore, hafter] at hr
          subst value
          exact hb

/-- A physical record transfer, used by the broadcast and loop store. -/
def copyRecord (s : GlobalState) (out input : Pointer) : GlobalState :=
  {s with mem := s.mem.storeAt out (s.mem.readAt input 1280)}

theorem copyRecord_frame (hwf : s.WF) : WritesOnly out 160 s (copyRecord s out input) :=
  ⟨hwf.storeAt, le_refl _, SerialPoint.Execution.storeAt_allocationShape s.mem out _ ,
    fun _ _ hd => MemoryState.readAt_storeAt_disjoint hd.symm _⟩

theorem copyRecord_readCached (s : GlobalState) (out input : Pointer)
    (ho : Buffer s.mem out 160) (hi : Buffer s.mem input 160) :
    readCached (copyRecord s out input) out = readCached s input := by
  have hw (c : Fin 4) (i : Fin 5) :
      (copyRecord s out input).mem.readAt (out.add (BitVec.ofNat 64 (40*c.val+8*i.val))) 64 =
        s.mem.readAt (input.add (BitVec.ofNat 64 (40*c.val+8*i.val))) 64 := by
    have hk : 40*c.val+8*i.val < 2^64 := by omega
    have hb : (BitVec.ofNat 64 (40*c.val+8*i.val)).toNat*8+64 ≤ 1280 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]; omega
    unfold copyRecord
    rw [MemoryState.readAt_storeAt_add ho.fits
      (Reduce64.Execution.SmallRange.no_wrap ho (k := 40*c.val+8*i.val) (by omega)) hb]
    exact (MemoryState.readAt_add_of_readAt hi.fits
      (Reduce64.Execution.SmallRange.no_wrap hi (k := 40*c.val+8*i.val) (by omega)) hb rfl).symm
  have hf (c : Fin 4) : readField (copyRecord s out input) (out.add (BitVec.ofNat 64 (40*c.val))) =
      readField s (input.add (BitVec.ofNat 64 (40*c.val))) := by
    funext i
    simp only [readField, SerialFieldMul.unsigned, SerialFieldMul.readLimbs,
      Pointer.add_add, ← BitVec.ofNat_add, hw]
  apply PointArithmetic.Extended.ext
  · exact hf 1
  · simpa [readCached] using hf 0
  · exact hf 2
  · exact hf 3

end Agave.Ed25519.Tables.SerialConstructorState
