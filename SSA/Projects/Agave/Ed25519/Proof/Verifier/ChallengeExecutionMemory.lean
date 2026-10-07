import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionState

namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge

variable {m : MemoryState} {p dst : Pointer} {state before after : GlobalState}
variable {n k count i j countI countJ bytes width : Nat} {value : BitVec width}

theorem smallRange_mono (h : SmallRange m p n) (hk : k ≤ n) : SmallRange m p k := by
  obtain ⟨b, hb, hsmall, hsize⟩ := h
  exact ⟨b, hb, hsmall, by omega⟩

theorem smallRange_length_lt (h : SmallRange m p n) : n < 2 ^ 63 := by
  obtain ⟨b, _, hs, hn⟩ := h
  omega

theorem range_disjoint_of_ne (p q : Pointer) (n k : Nat) (h : p.id ≠ q.id) :
    (Range.of p n).Disjoint (Range.of q k) := Or.inl h

theorem readAt_storeAt_of_id_ne (m : MemoryState) (dst src : Pointer)
    (value : BitVec width) (count : Nat) (h : dst.id ≠ src.id) :
    (m.storeAt dst value).readAt src count = m.readAt src count :=
  MemoryState.readAt_storeAt_disjoint (range_disjoint_of_ne dst src width count h) value

theorem smallRange_add (h : SmallRange m p n) (hk : k + count ≤ n) :
    SmallRange m (p.add (BitVec.ofNat 64 k)) count := by
  have hn := h.no_wrap (k := k) (by omega)
  have hk64 : k < 2 ^ 64 := by have := h.offset_lt; norm_num at *; omega
  obtain ⟨b, hb, hsmall, hsize⟩ := h
  refine ⟨b, hb, hsmall, ?_⟩
  simp only [Pointer.add, BitVec.toNat_add_of_not_uaddOverflow hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  omega

theorem context_count_fits (h : SmallRange m p 208) : Fits m (p.add 127) 8 :=
  h.fits_add (k := 127) (count := 1) (by decide)

theorem context_chain_fits (h : SmallRange m p 208) : Fits m (p.add 128) 512 :=
  h.fits_add (k := 128) (count := 64) (by decide)

theorem context_blocks_fits (h : SmallRange m p 208) : Fits m (p.add 192) 128 :=
  h.fits_add (k := 192) (count := 16) (by decide)

@[mlir_transport] theorem smallRange_alloca (hwf : state.WF)
    (h : SmallRange state.mem p n) : SmallRange (state.alloca bytes).mem p n := by
  have hne := GlobalState.ne_allocaPtr_of_fits hwf h.fits
  obtain ⟨b, hb, hsmall, hsize⟩ := h
  exact ⟨b, (GlobalState.getElem?_alloca hne).trans hb, hsmall, hsize⟩

theorem smallRange_alloca_self (state : GlobalState) (bytes : Nat) (h : bytes < 2 ^ 63) :
    SmallRange (state.alloca bytes).mem state.allocaPtr bytes := by
  refine ⟨⟨bytes, 0⟩, ?_, h, ?_⟩
  · simp [GlobalState.alloca, GlobalState.allocaPtr, MemoryState.getElem?_eq]
  · simp [GlobalState.allocaPtr]

theorem smallRange_disjoint_offsets (h : SmallRange m p n)
    (hi : i + countI ≤ n) (hj : j + countJ ≤ n)
    (hdisjoint : i + countI ≤ j ∨ j + countJ ≤ i) :
    (Range.of (p.add (BitVec.ofNat 64 i)) (8 * countI)).Disjoint
      (Range.of (p.add (BitVec.ofNat 64 j)) (8 * countJ)) := by
  have hi64 : i < 2 ^ 64 := by have := h.offset_lt; norm_num at *; omega
  have hj64 : j < 2 ^ 64 := by have := h.offset_lt; norm_num at *; omega
  have hoi := Pointer.offsetInBits_add (h.no_wrap (k := i) (by omega))
  have hoj := Pointer.offsetInBits_add (h.no_wrap (k := j) (by omega))
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] at hoi
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64] at hoj
  simp only [Range.Disjoint, Range.of, Pointer.add_id, hoi, hoj]
  omega

theorem readBytes_storeAt_disjoint (m : MemoryState) (src dst : Pointer)
    (bytes : Nat) (value : BitVec width) (hr : SmallRange m src bytes)
    (hd : (Range.of dst width).Disjoint (Range.of src (8 * bytes))) :
    readBytes (m.storeAt dst value) src bytes = readBytes m src bytes := by
  unfold readBytes
  congr 1
  funext i
  apply MemoryState.readAt_storeAt_disjoint
  have hi64 : i.val < 2 ^ 64 := by have := hr.offset_lt; have := i.isLt; norm_num at *; omega
  have hoff := Pointer.offsetInBits_add (hr.no_wrap (k := i.val) (by omega))
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] at hoff
  simp only [Range.Disjoint, Range.of, Pointer.add_id, hoff] at hd ⊢
  have := i.isLt
  rcases hd with hid | hbefore | hafter
  · exact Or.inl hid
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

theorem readBytes_copy (m : MemoryState) (src dst : Pointer) (bytes : Nat)
    (hsrc : SmallRange m src bytes) (hdst : SmallRange m dst bytes) :
    readBytes (m.storeAt dst (m.readAt src (8 * bytes))) dst bytes =
      readBytes m src bytes := by
  unfold readBytes
  congr 1
  funext i
  exact copy_readAt_offset m src dst bytes i.val 1 hsrc hdst (by omega)

theorem readBytes_copy_prefix (m : MemoryState) (src dst : Pointer) (bytes count : Nat)
    (hsrc : SmallRange m src bytes) (hdst : SmallRange m dst bytes)
    (hc : count ≤ bytes) :
    readBytes (m.storeAt dst (m.readAt src (8 * bytes))) dst count =
      readBytes m src count := by
  unfold readBytes
  congr 1
  funext i
  exact copy_readAt_offset m src dst bytes i.val 1 hsrc hdst (by omega)

theorem readBytes_copy_append (m : MemoryState) (src dst : Pointer) (old count : Nat)
    (hsrc : SmallRange m src count) (hdst : SmallRange m dst (old + count)) :
    readBytes (m.storeAt (dst.add (BitVec.ofNat 64 old))
      (m.readAt src (8 * count))) dst (old + count) =
        readBytes m dst old ++ readBytes m src count := by
  rw [readBytes_append, readBytes_copy _ _ _ _ hsrc (smallRange_add hdst (by omega))]
  congr 1
  apply readBytes_storeAt_disjoint _ _ _ _ _ (smallRange_mono hdst (by omega))
  simpa using smallRange_disjoint_offsets hdst
    (i := old) (countI := count) (j := 0) (countJ := old)
    (by omega) (by omega) (Or.inr (by omega))

theorem readBytes_take (m : MemoryState) (p : Pointer) (n k : Nat) (hk : k ≤ n) :
    (readBytes m p n).take k = readBytes m p k := by
  have hn : n = k + (n - k) := by omega
  rw [hn, readBytes_append]
  simp

theorem readBytes_drop (m : MemoryState) (p : Pointer) (n k : Nat) (hk : k ≤ n) :
    (readBytes m p n).drop k = readBytes m (p.add (BitVec.ofNat 64 k)) (n - k) := by
  have hn : n = k + (n - k) := by omega
  conv_lhs => rw [hn, readBytes_append]
  simp

theorem readBytes_alloca (state : GlobalState) (p : Pointer) (bytes count : Nat)
    (hwf : state.WF) (hr : SmallRange state.mem p count) :
    readBytes (state.alloca bytes).mem p count = readBytes state.mem p count := by
  unfold readBytes
  congr 1
  funext i
  exact MemoryState.readAt_alloca hwf (hr.fits_add (k := i.val) (count := 1) (by omega))

theorem StoreEffect.smallRange (he : StoreEffect before after dst value)
    (hr : SmallRange before.mem p n) : SmallRange after.mem p n := by
  rw [he.memory]
  exact hr.storeAt _ _

theorem StoreEffect.read (he : StoreEffect before after dst value)
    (hd : (Range.of dst width).Disjoint (Range.of p count)) :
    after.mem.readAt p count = before.mem.readAt p count := by
  rw [he.memory]
  exact MemoryState.readAt_storeAt_disjoint hd value

theorem StoreEffect.readBytes (he : StoreEffect before after dst value)
    (hr : SmallRange before.mem p n)
    (hd : (Range.of dst width).Disjoint (Range.of p (8 * n))) :
    readBytes after.mem p n = readBytes before.mem p n := by
  rw [he.memory]
  exact readBytes_storeAt_disjoint _ _ _ _ _ hr hd

/-- An internal stack write disappears under the RIR function-frame cleanup. -/
theorem erase_internal_store (m base : MemoryState) (mark : Nat) (dst : Pointer)
    (value : BitVec width) (hframe : m.eraseFrom mark = base)
    (hid : mark ≤ dst.id.id) : (m.storeAt dst value).eraseFrom mark = base := by
  rw [MemoryState.eraseFrom_storeAt, MemoryState.storeAt_eraseFrom_of_le hid, hframe]

theorem StoreEffect.erase_internal (he : StoreEffect before after dst value)
    (mark : Nat) (base : MemoryState) (hframe : before.mem.eraseFrom mark = base)
    (hid : mark ≤ dst.id.id) : after.mem.eraseFrom mark = base := by
  rw [he.memory]
  exact erase_internal_store _ _ _ _ _ hframe hid

end Agave.Ed25519.Verifier.Execution.Challenge
