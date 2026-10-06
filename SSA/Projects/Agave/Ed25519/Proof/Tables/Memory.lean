import SSA.Projects.Agave.Ed25519.Proof.NAF.Memory
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Execution
import SSA.Projects.Agave.Ed25519.Proof.Tables.Static

/-!
# Concrete table addresses and static table reads

These contracts connect the compiler's signed-byte lookup computation to the
memory bounds of its eight-entry dynamic table and 64-entry basepoint tables.
The lookup range is derived from the NAF construction. Exact initializers in
`Static` determine every static-table limb read.

The dynamic constructor still needs to prove the contents of its 1280-byte
output; the address lemmas deliberately assert no dynamic-table values.
-/
namespace Agave.Ed25519.Tables.Memory

open LeanMLIR.RIR
open NAF.Memory (Buffer)
open DoubleBase DoubleBase.Execution

variable {id : BlockId} {mem : MemoryState}

def dynamicIndex (n i : Nat) : Fin 8 :=
  ⟨compiledLookup (nafByte 5 n i), by
    rw [nafByte_lookup 5 (Or.inl rfl)]
    exact nafDigits_lookup_index_safe 5 (Or.inl rfl) n i⟩

def baseIndex (n i : Nat) : Fin 64 :=
  ⟨compiledLookup (nafByte 8 n i), by
    rw [nafByte_lookup 8 (Or.inr rfl)]
    exact nafDigits_lookup_index_safe 8 (Or.inr rfl) n i⟩

/-- Scaling the actual signed-extended lookup register satisfies all of its
emitted index truncation and signed/unsigned multiplication promises. -/
theorem dynamic_scale : ∀ k : Fin 8,
    Operation.gepInboundsIndex 160 (.value (BitVec.ofNat 64 k.val)) =
      .value ((160 * k.val : Nat) : Int) := by
  decide +kernel

theorem serial_base_scale : ∀ k : Fin 64,
    Operation.gepInboundsIndex 120 (.value (BitVec.ofNat 64 k.val)) =
      .value ((120 * k.val : Nat) : Int) := by
  decide +kernel

theorem avx2_base_scale : ∀ k : Fin 64,
    Operation.gepInboundsIndex 160 (.value (BitVec.ofNat 64 k.val)) =
      .value ((160 * k.val : Nat) : Int) := by
  decide +kernel

/-- Both dynamic representations occupy eight 160-byte cache records. The
incoming scalar alone determines a valid complete record at every position. -/
theorem dynamic_gep (h : Buffer mem table 1280) (n i : Nat) :
    Operation.gepInboundsLive mem (.value table)
      [Operation.gepInboundsIndex 160 (.value (BitVec.ofNat 64 (dynamicIndex n i).val))] =
      .value (table.add (BitVec.ofNat 64 (160 * (dynamicIndex n i).val))) := by
  rw [dynamic_scale]
  exact h.gep _ (by have := (dynamicIndex n i).isLt; omega)

theorem dynamic_record_fits (h : Buffer mem table 1280) (n i : Nat) :
    Fits mem (table.add (BitVec.ofNat 64 (160 * (dynamicIndex n i).val))) 1280 := by
  exact h.fits_at _ 160 (by have := (dynamicIndex n i).isLt; omega)

theorem global_buffer (g : ByteGlobal) (h : g.Present id mem) (hsmall : g.length < 2 ^ 63) :
    Buffer mem (g.address id) g.length := by
  refine ⟨⟨g.length, g.bytes⟩, h, hsmall, ?_⟩
  change 0 + g.length ≤ g.length
  omega

theorem serial_base_buffer (h : serialBaseGlobal.Present id mem) :
    Buffer mem (serialBaseGlobal.address id) 7680 :=
  global_buffer serialBaseGlobal h (by decide)

theorem avx2_base_buffer (h : avx2BaseGlobal.Present id mem) :
    Buffer mem (avx2BaseGlobal.address id) 10240 :=
  global_buffer avx2BaseGlobal h (by decide)

theorem serial_base_gep (h : serialBaseGlobal.Present id mem) (n i : Nat) :
    Operation.gepInboundsLive mem (.value (serialBaseGlobal.address id))
      [Operation.gepInboundsIndex 120 (.value (BitVec.ofNat 64 (baseIndex n i).val))] =
      .value ((serialBaseGlobal.address id).add
        (BitVec.ofNat 64 (120 * (baseIndex n i).val))) := by
  rw [serial_base_scale]
  exact (serial_base_buffer h).gep _ (by have := (baseIndex n i).isLt; omega)

theorem avx2_base_gep (h : avx2BaseGlobal.Present id mem) (n i : Nat) :
    Operation.gepInboundsLive mem (.value (avx2BaseGlobal.address id))
      [Operation.gepInboundsIndex 160 (.value (BitVec.ofNat 64 (baseIndex n i).val))] =
      .value ((avx2BaseGlobal.address id).add
        (BitVec.ofNat 64 (160 * (baseIndex n i).val))) := by
  rw [avx2_base_scale]
  exact (avx2_base_buffer h).gep _ (by have := (baseIndex n i).isLt; omega)

theorem serial_base_record_fits (h : serialBaseGlobal.Present id mem) (n i : Nat) :
    Fits mem ((serialBaseGlobal.address id).add
      (BitVec.ofNat 64 (120 * (baseIndex n i).val))) 960 := by
  exact (serial_base_buffer h).fits_at _ 120 (by have := (baseIndex n i).isLt; omega)

theorem avx2_base_record_fits (h : avx2BaseGlobal.Present id mem) (n i : Nat) :
    Fits mem ((avx2BaseGlobal.address id).add
      (BitVec.ofNat 64 (160 * (baseIndex n i).val))) 1280 := by
  exact (avx2_base_buffer h).fits_at _ 160 (by have := (baseIndex n i).isLt; omega)

/-- The bytes loaded from a serial static record are the limb constants whose
curve and odd-multiple certificates have already been checked in `Static`. -/
theorem serial_base_word (h : serialBaseGlobal.Present id mem)
    (k : Fin 64) (coordinate : Fin 3) (limb : Fin 5) :
    (mem.readAt ((serialBaseGlobal.address id).add
      (BitVec.ofNat 64 (120 * k.val + 40 * coordinate.val + 8 * limb.val))) 64).toNat =
      serialBaseWord k coordinate limb := by
  let offset := 120 * k.val + 40 * coordinate.val + 8 * limb.val
  have hfit := serial_base_buffer h
  have ho : offset + 8 ≤ 7680 := by
    have := k.isLt; have := coordinate.isLt; have := limb.isLt
    dsimp [offset]
    omega
  have ho64 : offset < 2 ^ 64 := by omega
  have hr := MemoryState.readAt_add_of_readAt hfit.fits
    (hfit.offset_noOverflow offset (by omega))
    (w := 64) (by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho64]
      omega) h.readAt
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho64] at hr
  rw [hr]
  unfold serialBaseWord
  congr 2
  dsimp [offset]
  omega

/-- Packed SIMD records have five 32-byte vectors; their lane reads are the
same constants used in the static coordinate and cache-scaling theorem. -/
theorem avx2_base_word (h : avx2BaseGlobal.Present id mem)
    (k : Fin 64) (limb : Fin 5) (lane : Fin 8) :
    (mem.readAt ((avx2BaseGlobal.address id).add
      (BitVec.ofNat 64 (160 * k.val + 32 * limb.val + 4 * lane.val))) 32).toNat =
      avx2BaseWord k limb lane := by
  let offset := 160 * k.val + 32 * limb.val + 4 * lane.val
  have hfit := avx2_base_buffer h
  have ho : offset + 4 ≤ 10240 := by
    have := k.isLt; have := limb.isLt; have := lane.isLt
    dsimp [offset]
    omega
  have ho64 : offset < 2 ^ 64 := by omega
  have hr := MemoryState.readAt_add_of_readAt hfit.fits
    (hfit.offset_noOverflow offset (by omega))
    (w := 32) (by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho64]
      omega) h.readAt
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho64] at hr
  rw [hr]
  unfold avx2BaseWord
  congr 2
  dsimp [offset]
  omega

/-- A serial limb load in the real effectful semantics reads the corresponding
checked initializer word. Its byte range follows from the record coordinates. -/
theorem serial_base_load_word {s : GlobalState}
    (h : serialBaseGlobal.Present id s.mem)
    (k : Fin 64) (coordinate : Fin 3) (limb : Fin 5)
    (dst : Dst Γ (.bv 64)) (env : ⟪Γ⟫) :
    Operation.load dst (.value ((serialBaseGlobal.address id).add
      (BitVec.ofNat 64 (120 * k.val + 40 * coordinate.val + 8 * limb.val)))) env s =
      .value (env[dst := .value (BitVec.ofNat 64 (serialBaseWord k coordinate limb))], s) := by
  have hfit := (serial_base_buffer h).fits_at
    (120 * k.val + 40 * coordinate.val + 8 * limb.val) 8
    (by have := k.isLt; have := coordinate.isLt; have := limb.isLt; omega)
  apply run_load hfit
  change PoisonOr.value (s.mem.readAt _ 64) = _
  rw [← serial_base_word h k coordinate limb, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The SIMD table's 32-bit lane load has the exact initializer value used by
the static cache-scaling certificate, with no assumed interior load bounds. -/
theorem avx2_base_load_lane {s : GlobalState}
    (h : avx2BaseGlobal.Present id s.mem)
    (k : Fin 64) (limb : Fin 5) (lane : Fin 8)
    (dst : Dst Γ (.bv 32)) (env : ⟪Γ⟫) :
    Operation.load dst (.value ((avx2BaseGlobal.address id).add
      (BitVec.ofNat 64 (160 * k.val + 32 * limb.val + 4 * lane.val)))) env s =
      .value (env[dst := .value (BitVec.ofNat 32 (avx2BaseWord k limb lane))], s) := by
  have hfit := (avx2_base_buffer h).fits_at
    (160 * k.val + 32 * limb.val + 4 * lane.val) 4
    (by have := k.isLt; have := limb.isLt; have := lane.isLt; omega)
  apply run_load hfit
  change PoisonOr.value (s.mem.readAt _ 32) = _
  rw [← avx2_base_word h k limb lane, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Agave.Ed25519.Tables.Memory
