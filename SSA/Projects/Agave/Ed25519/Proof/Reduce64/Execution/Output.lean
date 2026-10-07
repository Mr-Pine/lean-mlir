import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Packing

/-! The output contract shared by the standalone reduction kernel and the
inlined reduction schedules in the field multiplication and square kernels.
This module contains only the five-store memory model and its readback proof;
it does not import or assume execution of the standalone reduction program. -/

namespace Agave.Ed25519.Reduce64.Execution
open LeanMLIR.RIR

/-- The exact five stores performed by the compiled kernel. -/
def storeOutputs (m : MemoryState) (p : Pointer) (z : Columns4) : MemoryState :=
  let m0 := m.storeAt p (BitVec.packLanes (packedOutput z 0))
  let m1 := m0.storeAt (p.add 32) (BitVec.packLanes (packedOutput z 1))
  let m2 := m1.storeAt (p.add 64) (BitVec.packLanes (packedOutput z 2))
  let m3 := m2.storeAt (p.add 96) (BitVec.packLanes (packedOutput z 3))
  m3.storeAt (p.add 128) (BitVec.packLanes (packedOutput z 4))

/-- The five writes preserve state validity without unfolding the reduction
model. Registering this fact keeps `func_init` on its frame-free call rule. -/
@[mlir_mem]
theorem storeOutputs_wf (s : GlobalState) (p : Pointer) (z : Columns4) (h : s.WF) :
    ({s with mem := storeOutputs s.mem p z} : GlobalState).WF := by
  simpa only [storeOutputs, GlobalState.WF_storeAt] using h

/-- Reading any of the five written registers recovers exactly its packed limbs;
the other four stores are at disjoint offsets in the same allocation. -/
theorem storeOutputs_readAt (m : MemoryState) (dst : Pointer) (z : Columns4)
    (h : SmallRange m dst 160) (k : Fin 5) :
    (storeOutputs m dst z).readAt (dst.add (BitVec.ofNat 64 (32 * k.val))) 256 =
      BitVec.packLanes (packedOutput z k) := by
  have hf0 := h.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := h.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := h.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := h.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := h.fits_add (k := 128) (count := 32) (by decide)
  have hd10 := h.disjoint_chunks (i := 1) (j := 0) (by decide) (by decide) (by decide)
  have hd20 := h.disjoint_chunks (i := 2) (j := 0) (by decide) (by decide) (by decide)
  have hd21 := h.disjoint_chunks (i := 2) (j := 1) (by decide) (by decide) (by decide)
  have hd30 := h.disjoint_chunks (i := 3) (j := 0) (by decide) (by decide) (by decide)
  have hd31 := h.disjoint_chunks (i := 3) (j := 1) (by decide) (by decide) (by decide)
  have hd32 := h.disjoint_chunks (i := 3) (j := 2) (by decide) (by decide) (by decide)
  have hd40 := h.disjoint_chunks (i := 4) (j := 0) (by decide) (by decide) (by decide)
  have hd41 := h.disjoint_chunks (i := 4) (j := 1) (by decide) (by decide) (by decide)
  have hd42 := h.disjoint_chunks (i := 4) (j := 2) (by decide) (by decide) (by decide)
  have hd43 := h.disjoint_chunks (i := 4) (j := 3) (by decide) (by decide) (by decide)
  norm_num only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Pointer.add_zero] at hf0 hd10 hd20 hd21 hd30 hd31 hd32 hd40 hd41 hd42 hd43
  fin_cases k
  · simp only [storeOutputs, Nat.mul_zero, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Pointer.add_zero]
    rw [MemoryState.readAt_storeAt_disjoint hd40, MemoryState.readAt_storeAt_disjoint hd30, MemoryState.readAt_storeAt_disjoint hd20, MemoryState.readAt_storeAt_disjoint hd10]
    exact MemoryState.readAt_storeAt_self hf0 _
  · simp only [storeOutputs, Nat.mul_one, Nat.reduceMul, BitVec.ofNat_eq_ofNat]
    rw [MemoryState.readAt_storeAt_disjoint hd41, MemoryState.readAt_storeAt_disjoint hd31, MemoryState.readAt_storeAt_disjoint hd21]
    exact MemoryState.readAt_storeAt_self hf1.storeAt _
  · simp only [storeOutputs, Nat.reduceMul, BitVec.ofNat_eq_ofNat]
    rw [MemoryState.readAt_storeAt_disjoint hd42, MemoryState.readAt_storeAt_disjoint hd32]
    exact MemoryState.readAt_storeAt_self hf2.storeAt.storeAt _
  · simp only [storeOutputs, Nat.reduceMul, BitVec.ofNat_eq_ofNat]
    rw [MemoryState.readAt_storeAt_disjoint hd43]
    exact MemoryState.readAt_storeAt_self hf3.storeAt.storeAt.storeAt _
  · simp only [storeOutputs, Nat.reduceMul, BitVec.ofNat_eq_ofNat]
    exact MemoryState.readAt_storeAt_self hf4.storeAt.storeAt.storeAt.storeAt _

/-- Decode one of the ten output limbs from its actual 256-bit memory register. -/
def outputWord (m : MemoryState) (dst : Pointer) (limb : Fin 10) (lane : Fin 4) : BitVec 32 :=
  let chunk : Fin 5 := ⟨limb.val / 2, by omega⟩
  let odd := decide (limb.val % 2 = 1)
  (m.readAt (dst.add (BitVec.ofNat 64 (32 * chunk.val))) 256).extractLsb'
    ((physicalLane odd lane).val * 32) 32

/-- Complete packing refinement: a limb read from output memory is precisely
its low 32-bit word in the proven wrapping `Word.reduce` schedule. -/
theorem outputWord_storeOutputs (m : MemoryState) (dst : Pointer) (z : Columns4)
    (h : SmallRange m dst 160) (limb : Fin 10) (lane : Fin 4) :
    outputWord (storeOutputs m dst z) dst limb lane =
      low32 (Word.reduce (fun j => (z j)[lane]) limb) := by
  dsimp only [outputWord]
  rw [storeOutputs_readAt m dst z h ⟨limb.val / 2, by omega⟩]
  rw [BitVec.extractLsb'_packLanes _ _
    (physicalLane (decide (limb.val % 2 = 1)) lane).isLt]
  fin_cases limb <;> fin_cases lane <;> simp [packedOutput, packPair, physicalLane, reduceLanes]

/-- No narrowing is lost under the caller-derived column bound. -/
theorem low32_reduce_toNat (z : Word.Columns) (h : ColumnsBound (fun i => (z i).toNat))
    (limb : Fin 10) :
    (low32 (Word.reduce z limb)).toNat = Reduce64.reduce (fun i => (z i).toNat) limb := by
  have hb := output_u32 (fun i => (z i).toNat) h limb
  simp only [low32, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Word.toNat_reduce z h, Nat.mod_eq_of_lt hb]

/-- The stored natural-number limbs equal the integer carry schedule. -/
theorem outputWord_toNat (m : MemoryState) (dst : Pointer) (z : Columns4)
    (hm : SmallRange m dst 160) (lane : Fin 4)
    (hz : ColumnsBound (fun j => ((z j)[lane]).toNat)) (limb : Fin 10) :
    (outputWord (storeOutputs m dst z) dst limb lane).toNat =
      Reduce64.reduce (fun j => ((z j)[lane]).toNat) limb := by
  rw [outputWord_storeOutputs m dst z hm]
  exact low32_reduce_toNat _ hz limb

end Agave.Ed25519.Reduce64.Execution
