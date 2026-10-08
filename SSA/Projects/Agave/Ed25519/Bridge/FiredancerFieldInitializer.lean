import SSA.Projects.Agave.Ed25519.Bridge.FiredancerBaseTableLoader

/-! Exact scalar field-constant loader boundary. The seven five-limb literals
are extracted from the two C table files at Firedancer commit
292f89b338a634e23e9f45c3dfdd5383ddcae624; see field-initializer-manifest.json.
The extraction is a source correspondence boundary, not a claim that an
initializer program has executed. Lean checks all values and bounds below. -/
namespace Agave.Ed25519.Bridge.FiredancerFieldInitializer
open LeanMLIR SLLVM Firedancer Firedancer.Ref

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def symbol : Fin 7 → String :=
  !["fd_f25519_d", "fd_f25519_one", "fd_f25519_sqrtm1", "fd_ed25519_order8_point_y0", "fd_ed25519_order8_point_y1", "fd_f25519_k", "fd_f25519_zero"]

def limbs : Fin 7 → Fin 5 → BitVec 64 :=
  ![![0x00034dca135978a3, 0x0001a8283b156ebd, 0x0005e7a26001c029, 0x000739c663a03cbb, 0x00052036cee2b6ff],
    ![0x0000000000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    ![0x00061b274a0ea0b0, 0x0000d5a5fc8f189d, 0x0007ef5e9cbd0c60, 0x00078595a6804c9e, 0x0002b8324804fc1d],
    ![0x0007b2c28f95e826, 0x0006513e9868b604, 0x0006b37f57c263bf, 0x0004589c99e36982, 0x00005fc536d88023],
    ![0x00004d3d706a17c7, 0x0001aec1679749fb, 0x00014c80a83d9c40, 0x0003a763661c967d, 0x0007a03ac9277fdc],
    ![0x00069b9426b2f159, 0x00035050762add7a, 0x0003cf44c0038052, 0x0006738cc7407977, 0x0002406d9dc56dff],
    ![0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000]]

def bytes (k : Fin 7) : BitVec 320 := packLimbs (limbs k)

def value : Fin 7 → ZMod _root_.p :=
  ![Ed25519.d, 1, _root_.sqrtm1, Ed25519.order8_y0, Ed25519.order8_y1,
    2 * Ed25519.d, 0]

theorem limb_bounds (k : Fin 7) (i : Fin 5) : (limbs k i).toNat ≤ 0x8000000000000 := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem decode_value (k : Fin 7) :
    decodeFieldElem (fun i => (limbs k i).toNat) = value k := by
  fin_cases k <;> decide +kernel

/-- Only symbol lookup, zero offset, and exact 40-byte contents. -/
structure EntryLoaded (state : GlobalState) (k : Fin 7) (q : Pointer) : Prop where
  address : GlobalPtr state (symbol k) q
  offset : q.offset = 0#64
  contents : state.mem.live? q.id = some ⟨40, bytes k⟩

/-- The seven raw field-constant allocations; no mathematical-value premises. -/
def Loaded (state : GlobalState) : Prop := ∀ k, ∃ q, EntryLoaded state k q

theorem EntryLoaded.ptr (h : EntryLoaded state k q) : IsFieldElemPtr state.mem q := by
  refine ⟨⟨⟨40, bytes k⟩, getElem?_of_live? h.contents, ?_⟩, ?_⟩ <;>
    simp [Pointer.offsetInBits, h.offset, LiveBlock.lengthInBits]

theorem EntryLoaded.readLimb (h : EntryLoaded state k q) (i : Fin 5) :
    readLimb? q i state.mem = some (limbs k i).toNat := by
  unfold readLimb?
  rw [h.contents]
  change some (((bytes k).extractLsb' (q.offsetInBits + 64*i.val) 64).toNat) = _
  simp only [Pointer.offsetInBits, h.offset, BitVec.toNat_zero, Nat.mul_zero,
    Nat.zero_add, bytes]
  exact congrArg (fun x : BitVec 64 => some x.toNat)
    (Firedancer.Ref.extractLsb'_packLimbs (limbs k) i)

theorem EntryLoaded.fieldGlobal (h : EntryLoaded state k q) :
    FieldGlobal state (symbol k) q (value k) := by
  refine ⟨h.address, h.ptr, ?_, ?_⟩
  · apply readFieldElem_eq_of
    simp only [readFieldElem?, h.readLimb, Option.pure_def]
    have he : ![(limbs k 0).toNat, (limbs k 1).toNat, (limbs k 2).toNat,
        (limbs k 3).toNat, (limbs k 4).toNat] = (fun i => (limbs k i).toNat) := by
      funext i; fin_cases i <;> rfl
    change some (decodeFieldElem ![(limbs k 0).toNat, (limbs k 1).toNat,
      (limbs k 2).toNat, (limbs k 3).toNat, (limbs k 4).toNat]) = _
    rw [he, decode_value]
  · intro i
    simpa only [Firedancer.Ref.readLimb, h.readLimb, Option.get_some] using limb_bounds k i

/-- Raw constants plus ordinary allocation well-formedness and the pinned base
allocation establish the entire reference environment. -/
theorem Loaded.refWF (h : Loaded state) (hwf : state.WF)
    (hbase : FiredancerBaseInitializer.Loaded state table) : state.RefWF [] := by
  have hf (k : Fin 7) : Firedancer.Ref.Loaded state (symbol k) (value k) [] := by
    obtain ⟨q, hq⟩ := h k
    exact ⟨q, hq.fieldGlobal, by simp [Apart]⟩
  refine ⟨hwf, hf 0, hf 1, hf 2, hf 3, hf 4, hf 5, hf 6, ?_⟩
  refine ⟨table, ⟨hbase.address, ?_, ?_⟩, by simp [Apart]⟩
  · refine ⟨⟨20480, FiredancerBaseInitializer.bytes⟩, getElem?_of_live? hbase.contents, ?_⟩
    simp [Pointer.offsetInBits, hbase.offset, LiveBlock.lengthInBits]
  · simp [hbase.offset]

end Agave.Ed25519.Bridge.FiredancerFieldInitializer
