import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-!
Address alignment is an additional source-refinement condition, not a property
of RIR's allocation identifiers. These lemmas isolate that condition without
changing the execution semantics or assuming an LLVM execution theorem.
`base` is the physical byte address assigned to each allocation in a separate
machine-memory realization. Address-range validity and nonoverlap of that
realization remain separate obligations.
-/
namespace Agave.Ed25519.SourceMemoryAudit
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution

def AddressAligned (base : BlockId → Nat) (p : Pointer) (alignment : Nat) : Prop :=
  alignment ∣ base p.id + p.offset.toNat

theorem alignment_one (base : BlockId → Nat) (p : Pointer) :
    AddressAligned base p 1 := by
  exact Nat.one_dvd _

theorem alignment_weaken (h : AddressAligned base p a) (hdiv : b ∣ a) :
    AddressAligned base p b := hdiv.trans h

theorem alignment_add (h : AddressAligned base p a)
    (hoff : a ∣ off.toNat) (hwrap : ¬p.offset.uaddOverflow off) :
    AddressAligned base (p.add off) a := by
  unfold AddressAligned at *
  simp only [Pointer.add, BitVec.toNat_add_of_not_uaddOverflow hwrap]
  simpa only [Nat.add_assoc] using Nat.dvd_add h hoff

theorem alignment_smallRange_add (h : AddressAligned base p a)
    (hr : SmallRange m p bytes) (hk : k ≤ bytes) (hdiv : a ∣ k) :
    AddressAligned base (p.add (BitVec.ofNat 64 k)) a := by
  have hk64 : k < 2^64 := by have := hr.offset_lt; omega
  apply alignment_add h _ (hr.no_wrap hk)
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] using hdiv

/-- Stack allocation's offset zero does not supply its machine base alignment. -/
theorem alloca_alignment_iff (base : BlockId → Nat) (s : GlobalState) :
    AddressAligned base s.allocaPtr a ↔ a ∣ base s.allocaPtr.id := by
  simp [AddressAligned, GlobalState.allocaPtr]

/-- A concrete counterexample: an in-bounds eight-byte RIR access at offset one
need not satisfy LLVM's `align 8`, even with a 128-byte-aligned allocation base. -/
theorem fits_does_not_imply_alignment (s : GlobalState) :
    Fits (s.alloca 16).mem (s.allocaPtr.add 1#64) 64 ∧
      ¬AddressAligned (fun _ => 128) (s.allocaPtr.add 1#64) 8 := by
  constructor
  · rw [Fits.alloca_allocaPtr_add]
    decide
  · simp [AddressAligned, Pointer.add, GlobalState.allocaPtr]

/-- The actual live-range premise used by Firedancer Init can hold while its
first LLVM store violates align 128. This is a model-boundary counterexample,
not a claim that a correctly constructed `fd_sha512_t` has this address. -/
theorem firedancer_init_range_does_not_imply_alignment (s : GlobalState) :
    SmallRange (s.alloca 256).mem (s.allocaPtr.add 1#64) 224 ∧
      ¬AddressAligned (fun _ => 128) ((s.allocaPtr.add 1#64).add 128#64) 128 := by
  constructor
  · refine ⟨⟨256, 0⟩, ?_, by decide, ?_⟩
    simp [GlobalState.alloca, GlobalState.allocaPtr, Pointer.add,
      MemoryState.getElem?_eq]
    simp [GlobalState.allocaPtr, Pointer.add]
  · simp [AddressAligned, Pointer.add, GlobalState.allocaPtr]

/-- Exact `(byte offset, alignment)` pairs for the eight ordinary initialization
stores in `generated/fd_sha512_init.ll`; the memset at offset 200 is separate. -/
def firedancerInitStores : List (Nat × Nat) :=
  [(128, 128), (136, 8), (144, 16), (152, 8),
   (160, 32), (168, 8), (176, 16), (184, 8)]

theorem firedancer_init_stores_aligned (h : AddressAligned base context 128)
    (hr : SmallRange m context 224) :
    ∀ entry ∈ firedancerInitStores,
      AddressAligned base (context.add (BitVec.ofNat 64 entry.1)) entry.2 := by
  intro entry he
  simp only [firedancerInitStores, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact alignment_smallRange_add (alignment_weaken h (by decide)) hr
      (by decide) (by decide)

/-- The align-16 counter access in Append and Finish is context+208. -/
theorem firedancer_counter_aligned (h : AddressAligned base context 128)
    (hr : SmallRange m context 224) :
    AddressAligned base (context.add 208#64) 16 := by
  exact alignment_smallRange_add (alignment_weaken h (by decide)) hr
    (k := 208) (by decide) (by decide)

/-- Eight state/output words. Applies to Firedancer Core's state, Finish's
output, and Agave scalar/AVX2 SHA chaining state; input bytes only need align 1. -/
theorem sha_words_aligned (h : AddressAligned base p 8)
    (hr : SmallRange m p bytes) (hi : 8 * i ≤ bytes) :
    AddressAligned base (p.add (BitVec.ofNat 64 (8 * i))) 8 := by
  exact alignment_smallRange_add h hr hi (dvd_mul_right 8 i)

/-- Agave AVX2 bb9's initial scratch/cache stores are at offsets 16*i. -/
theorem avx2_initial_pair_store_aligned (h : AddressAligned base p 16)
    (hr : SmallRange m p bytes) (hi : 16 * i ≤ bytes) :
    AddressAligned base (p.add (BitVec.ofNat 64 (16 * i))) 16 := by
  exact alignment_smallRange_add h hr hi (dvd_mul_right 16 i)

/-- Agave AVX2 cache group stores retain align 16 at 128*group + 16*pair. -/
theorem avx2_group_store_aligned (h : AddressAligned base p 16)
    (hr : SmallRange m p bytes) (hi : 128 * group + 16 * pair ≤ bytes) :
    AddressAligned base
      (p.add (BitVec.ofNat 64 (128 * group + 16 * pair))) 16 := by
  apply alignment_smallRange_add h hr hi
  exact Nat.dvd_add (dvd_mul_of_dvd_left (by decide : 16 ∣ 128) group)
    (dvd_mul_right 16 pair)

end Agave.Ed25519.SourceMemoryAudit
