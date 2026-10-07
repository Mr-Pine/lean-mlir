import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorStack
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorState

/-! Pointer-indexed scratch readiness and the private-memory frame for the
AVX2 constructor. No global or successful-execution premise is used. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.State
open LeanMLIR.RIR NAF.Memory
abbrev Slots := Fin 8 → Pointer

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

theorem Frame.buffer (h : Frame slots table s t) (hq : Buffer s.mem q count) :
    Buffer t.mem q count := by
  obtain ⟨b,hb,hs,hz⟩ := hq
  have he := h.allocationShape q.id
  rw [hb] at he
  cases ht : t.mem[q.id]? with
  | none => simp [ht] at he
  | some b' =>
    have hl : b'.length = b.length := by simpa [ht] using he
    exact ⟨b',ht,by omega,by omega⟩

structure Ready (slots : Slots) (table : Pointer) (s : GlobalState) : Prop where
  wf : s.WF
  scratch : ∀ i, Buffer s.mem (slots i) 160
  tableBuffer : Buffer s.mem table 1280
  separate : ∀ i j, i ≠ j → (slots i).id ≠ (slots j).id
  separateTable : ∀ i, (slots i).id ≠ table.id

theorem Ready.preserve (h : Ready slots table s) (hf : Frame slots table s t) :
    Ready slots table t :=
  ⟨hf.wellFormed,fun i => hf.buffer (h.scratch i),hf.buffer h.tableBuffer,
    h.separate,h.separateTable⟩

def slots (s : GlobalState) : Slots := fun i => Stack.pointer s i.val

theorem stack_ready (s : GlobalState) (hwf : s.WF) :
    Ready (slots s) (Stack.pointer s 8) (Stack.state s 9) := by
  refine ⟨Stack.wf hwf 9,?_,?_,?_,?_⟩
  · intro i
    have hi := i.isLt
    have hb := Stack.buffer hwf i.val 9 (by omega)
    simpa [Stack.size,slots,show i.val ≠ 8 by omega] using hb
  · simpa [Stack.size] using Stack.buffer hwf 8 9 (by decide)
  · intro i j hij
    apply Stack.separate
    intro he
    exact hij (Fin.ext he)
  · intro i
    apply Stack.separate
    have := i.isLt
    omega

end Agave.Ed25519.Tables.Avx2Constructor.State
