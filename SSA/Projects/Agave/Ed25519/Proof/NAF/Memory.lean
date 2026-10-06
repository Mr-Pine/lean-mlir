import SSA.Projects.RIR.Run.Memory
import SSA.Projects.Agave.Ed25519.Proof.NAF.WordWindow
import Mathlib

/-!
# The NAF array and five-word buffer in RIR memory

The memory hypotheses are object bounds at the caller boundary. All interior
load/store bounds and nonwrapping offsets follow from them and the bounded
source position. Fresh stack arrays satisfy the object hypothesis directly.
No value or digit-correctness premise is included in `Buffer`.
-/
namespace Agave.Ed25519.NAF.Memory

open LeanMLIR.RIR

def Buffer (m : MemoryState) (p : Pointer) (bytes : Nat) : Prop :=
  ∃ block, m[p.id]? = some block ∧ block.length < 2 ^ 63 ∧
    p.offset.toNat + bytes ≤ block.length

theorem Buffer.fits (h : Buffer m p bytes) : Fits m p (8 * bytes) := by
  obtain ⟨block, hlive, _, hsize⟩ := h
  refine ⟨block, hlive, ?_⟩
  simpa only [Pointer.offsetInBits, MemoryBlock.lengthInBits, Nat.mul_add] using
    Nat.mul_le_mul_left 8 hsize

theorem Buffer.noWrap (h : Buffer m p bytes) : p.offset.toNat + bytes < 2 ^ 64 := by
  obtain ⟨_, _, hsmall, hsize⟩ := h
  norm_num at hsmall ⊢
  omega

theorem Buffer.alloca (s : GlobalState) (bytes : Nat) (hb : bytes < 2 ^ 63) :
    Buffer (s.alloca bytes).mem s.allocaPtr bytes := by
  refine ⟨⟨bytes, 0⟩, ?_, hb, ?_⟩
  · simp [GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq]
  · simp [GlobalState.allocaPtr]

@[mlir_mem, mlir_transport]
theorem Buffer.storeAt (h : Buffer m p bytes) (q : Pointer) (value : BitVec w) :
    Buffer (m.storeAt q value) p bytes := by
  obtain ⟨block, hlive, hsmall, hsize⟩ := h
  by_cases heq : p.id = q.id
  · have hliveq : m[q.id]? = some block := heq ▸ hlive
    refine ⟨{block with bytes := LeanMLIR.RIR.Memory.spliceBits block.bytes q.offsetInBits value},
      ?_, hsmall, hsize⟩
    simpa only [heq] using MemoryState.getElem?_storeAt_self (x := value) hliveq
  · exact ⟨block, by rw [MemoryState.getElem?_storeAt_ne heq]; exact hlive, hsmall, hsize⟩

@[mlir_mem, mlir_transport]
theorem Buffer.alloca_existing {s : GlobalState} (h : Buffer s.mem p bytes) (hwf : s.WF) (size : Nat) :
    Buffer (s.alloca size).mem p bytes := by
  have hne := GlobalState.ne_allocaPtr_of_fits hwf h.fits
  obtain ⟨block, hlive, hsmall, hsize⟩ := h
  refine ⟨block, ?_, hsmall, hsize⟩
  rw [GlobalState.getElem?_alloca hne]
  exact hlive

theorem Buffer.offset_noOverflow (h : Buffer m p bytes) (offset : Nat) (ho : offset ≤ bytes) :
    ¬p.offset.uaddOverflow (BitVec.ofNat 64 offset) := by
  have hwrap := h.noWrap
  have hb : offset < 2 ^ 64 := by omega
  simp only [BitVec.uaddOverflow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb,
    Bool.not_eq_true, decide_eq_false_iff_not]
  omega

theorem Buffer.fits_at (h : Buffer m p bytes) (offset length : Nat)
    (ho : offset + length ≤ bytes) :
    Fits m (p.add (BitVec.ofNat 64 offset)) (8 * length) := by
  have hwrap := h.noWrap
  have hb : offset < 2 ^ 64 := by omega
  apply Fits.add_of_le (h.offset_noOverflow offset (by omega)) _ h.fits
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  omega

/-- An interior object view retains the same live small allocation. -/
theorem Buffer.slice (h : Buffer m p bytes) (offset length : Nat)
    (ho : offset + length ≤ bytes) :
    Buffer m (p.add (BitVec.ofNat 64 offset)) length := by
  have hov := h.offset_noOverflow offset (by omega)
  have ho64 : offset < 2 ^ 64 := by have := h.noWrap; omega
  obtain ⟨block, hlive, hsmall, hsize⟩ := h
  refine ⟨block, hlive, hsmall, ?_⟩
  change (p.offset + BitVec.ofNat 64 offset).toNat + length ≤ block.length
  rw [BitVec.toNat_add_of_not_uaddOverflow hov, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho64]
  omega

/-- The exact emitted inbounds/nusw/nuw address operation is defined throughout
the live buffer. Its size bound comes from the allocation, not a digit premise. -/
theorem Buffer.gep (h : Buffer m p bytes) (offset : Nat) (ho : offset ≤ bytes) :
    Operation.gepInboundsLive m (.value p) [.value (offset : Int)] =
      .value (p.add (BitVec.ofNat 64 offset)) := by
  obtain ⟨block, hlive, hsmall, hsize⟩ := h
  have hwithin : (p.offset.toNat : Int) + (offset : Int) ≤ block.length := by omega
  have hsafe := Operation.gepInboundsOffsets_singleton hsmall (Int.ofNat_nonneg offset) hwithin
  simpa using Operation.gepInboundsLive_eq (offsets := [(offset : Int)]) hlive hsmall hsafe

/-- Slot bytes are the actual eight-bit values read by both compiler loops. -/
def slot (digits : BitVec 2048) (i : Nat) : BitVec 8 := digits.extractLsb' (8 * i) 8

def writeSlot (digits : BitVec 2048) (i : Nat) (digit : BitVec 8) : BitVec 2048 :=
  LeanMLIR.RIR.Memory.spliceBits digits (8 * i) digit

theorem slot_writeSlot (digits : BitVec 2048) (i j : Fin 256) (digit : BitVec 8) :
    slot (writeSlot digits i.val digit) j.val = if j = i then digit else slot digits j.val := by
  by_cases h : j = i
  · subst j
    simp only [slot, writeSlot, if_true]
    exact LeanMLIR.RIR.Memory.extractLsb'_spliceBits_self _ _ _ (by omega)
  · rw [if_neg h]
    exact LeanMLIR.RIR.Memory.extractLsb'_spliceBits_of_disjoint _ _ _ _ (by
      have hi := i.isLt
      have hj := j.isLt
      have hne : j.val ≠ i.val := by intro he; exact h (Fin.ext he)
      omega)

/-- Reading any array position is justified by the one outer object contract. -/
theorem read_slot (h : Buffer m p 256) (digits : BitVec 2048)
    (hd : m.readAt p 2048 = digits) (i : Fin 256) :
    m.readAt (p.add (BitVec.ofNat 64 i.val)) 8 = slot digits i.val := by
  have hov := h.offset_noOverflow i.val (by omega)
  have hi : i.val < 2 ^ 64 := by omega
  have hn : (BitVec.ofNat 64 i.val).toNat * 8 + 8 ≤ 2048 := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
    omega
  have hread := MemoryState.readAt_add_of_readAt h.fits hov hn hd
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mul_comm, slot] using hread

/-- A real RIR store changes the captured array by precisely one byte splice. -/
theorem write_slot (h : Buffer m p 256) (digits : BitVec 2048)
    (hd : m.readAt p 2048 = digits) (i : Fin 256) (digit : BitVec 8) :
    (m.storeAt (p.add (BitVec.ofNat 64 i.val)) digit).readAt p 2048 =
      writeSlot digits i.val digit := by
  have hov := h.offset_noOverflow i.val (by omega)
  have hi : i.val < 2 ^ 64 := by omega
  have hn : (BitVec.ofNat 64 i.val).toNat * 8 + 8 ≤ 2048 := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
    omega
  rw [MemoryState.readAt_add_storeAt h.fits hov hn, hd]
  simp only [writeSlot, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mul_comm]

theorem load_slot (h : Buffer s.mem p 256) (digits : BitVec 2048)
    (hd : s.mem.readAt p 2048 = digits) (i : Fin 256)
    (dst : Dst Γ (.bv 8)) (env : ⟪Γ⟫) :
    Operation.load dst (.value (p.add (BitVec.ofNat 64 i.val))) env s =
      .value (env[dst := .value (slot digits i.val)], s) := by
  apply run_load (h.fits_at i.val 1 (by omega))
  change PoisonOr.value (s.mem.readAt _ 8) = _
  rw [read_slot h digits hd i]

theorem store_slot (h : Buffer s.mem p 256) (i : Fin 256)
    (digit : BitVec 8) (env : ⟪Γ⟫) :
    Operation.store (.value (p.add (BitVec.ofNat 64 i.val)))
      (τ := .bv 8) (.value digit) env s =
      .value (env, {s with mem := s.mem.storeAt (p.add (BitVec.ofNat 64 i.val)) digit}) := by
  exact run_store (h.fits_at i.val 1 (by omega)) rfl

/-- The two possible window loads stay inside the five-u64 buffer. -/
theorem word_loads_fit (h : Buffer m p 40) (pos : Fin 256) :
    Fits m (p.add (BitVec.ofNat 64 (8 * (pos.val / 64)))) 64 ∧
    Fits m (p.add (BitVec.ofNat 64 (8 * (pos.val / 64 + 1)))) 64 := by
  constructor
  · exact h.fits_at _ 8 (by have := pos.isLt; omega)
  · exact h.fits_at _ 8 (by have := pos.isLt; omega)

theorem read_word (h : Buffer m p 40) (bits : BitVec 320)
    (hd : m.readAt p 320 = bits) (index : Fin 5) :
    m.readAt (p.add (BitVec.ofNat 64 (8 * index.val))) 64 = WordWindow.word bits index.val := by
  have hi : 8 * index.val < 2 ^ 64 := by omega
  have hov := h.offset_noOverflow (8 * index.val) (by omega)
  have hn : (BitVec.ofNat 64 (8 * index.val)).toNat * 8 + 64 ≤ 320 := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
    omega
  have hread := MemoryState.readAt_add_of_readAt h.fits hov hn hd
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] at hread
  simpa only [WordWindow.word, show 8 * index.val * 8 = 64 * index.val by omega] using hread

/-- The initial emitted memset establishes every unwritten digit as zero. -/
theorem zero_digits (h : Buffer s.mem p 256) (env : ⟪Γ⟫) :
    Operation.memset (.value p) (.value 0#8) (.value 256#64) env s =
      .value (env, {s with mem := s.mem.storeAt p (0 : BitVec 2048)}) := by
  have hr : (0#8).replicate 256 = (0 : BitVec 2048) := by decide +kernel
  have hfits : Fits s.mem p 2048 := h.fits
  change ((do
    let state : GlobalState ← get
    throwUBIf (¬Fits state.mem p 2048)
    set {state with mem := state.mem.storeAt p ((0#8).replicate 256)}
    pure env) : EffectM ⟪Γ⟫) s = _
  simp only [EffectM.bind_eq, EffectM.get_eq, PoisonOr.value_bind, hfits,
    not_true_eq_false, throwUBIf, if_false, EffectM.pure_eq, hr, EffectM.set_eq]

/-- A fresh five-word stack object is zero before its first write. -/
theorem fresh_words_zero (s : GlobalState) :
    (s.alloca 40).mem.readAt s.allocaPtr 320 = 0 := by
  simp [MemoryState.readAt, GlobalState.alloca, GlobalState.allocaPtr,
    MemoryState.getElem?_eq, Pointer.offsetInBits]

/-- Copying all 256 scalar bits into a zero-padded five-word object establishes
the precise buffer value used by the window arithmetic proof. -/
theorem copy_scalar_words (h : Buffer m p 40) (hzero : m.readAt p 320 = 0)
    (scalar : BitVec 256) :
    (m.storeAt p scalar).readAt p 320 = WordWindow.scalarBuffer scalar := by
  have hov : ¬p.offset.uaddOverflow (0#64) := h.offset_noOverflow 0 (by omega)
  have hcopy := MemoryState.readAt_add_storeAt (off := 0#64) h.fits hov
    (by decide : (0#64).toNat * 8 + 256 ≤ 320) scalar
  simpa [hzero, WordWindow.scalarBuffer, LeanMLIR.RIR.Memory.spliceBits] using hcopy

end Agave.Ed25519.NAF.Memory
