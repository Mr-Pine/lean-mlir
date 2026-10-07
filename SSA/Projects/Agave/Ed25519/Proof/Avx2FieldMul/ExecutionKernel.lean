import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.Program
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionMemory
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionStores
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionInstructions

import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

namespace Agave.Ed25519.Avx2FieldMul.Execution
open LeanMLIR.RIR
attribute [local implicit_reducible] Ty.width
open Reduce64.Execution
open Avx2SquareNegateD

attribute [-mlir_operation] Operation.bitcast Operation.add Operation.mul


set_option maxHeartbeats 64000000 in
/-- Actual execution with independent input vectors fixed by their memory
reads. The arithmetic proof never unfolds the initial memory representation. -/
theorem kernel_call_of_reads (r a b : Pointer) (s : GlobalState) (x y : Blocks)
    (hwf : s.WF) (hr : SmallRange s.mem r 160) (ha : SmallRange s.mem a 160)
    (hb : SmallRange s.mem b 160)
    (hreadsA : ∀ k : Fin 5,
      (Ty.vec 8 32).unflatten
        (s.mem.readAt (a.add (BitVec.ofNat 64 (32 * k.val))) 256) = Ty.wrap (x k))
    (hreadsB : ∀ k : Fin 5,
      (Ty.vec 8 32).unflatten
        (s.mem.readAt (b.add (BitVec.ofNat 64 (32 * k.val))) 256) = Ty.wrap (y k)) :
    program.call (program.args (.value r) (.value a) (.value b)) s =
      .value (.nil, {s with mem := storeBlocks s.mem r (wordTrace x y)}) := by
  have hx0 : Ty.wrap (t := .vec 8 32) (Vector.ofFn fun i => Ty.extractVecElem 8 32 i
      (s.mem.readAt a 256)) = Ty.wrap (t := .vec 8 32) (x 0) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreadsA 0
  have hx1 : Ty.wrap (t := .vec 8 32) (Vector.ofFn fun i => Ty.extractVecElem 8 32 i
      (s.mem.readAt (a.add 32#64) 256)) = Ty.wrap (t := .vec 8 32) (x 1) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreadsA 1
  have hx2 : Ty.wrap (t := .vec 8 32) (Vector.ofFn fun i => Ty.extractVecElem 8 32 i
      (s.mem.readAt (a.add 64#64) 256)) = Ty.wrap (t := .vec 8 32) (x 2) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreadsA 2
  have hx3 : Ty.wrap (t := .vec 8 32) (Vector.ofFn fun i => Ty.extractVecElem 8 32 i
      (s.mem.readAt (a.add 96#64) 256)) = Ty.wrap (t := .vec 8 32) (x 3) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreadsA 3
  have hx4 : Ty.wrap (t := .vec 8 32) (Vector.ofFn fun i => Ty.extractVecElem 8 32 i
      (s.mem.readAt (a.add 128#64) 256)) = Ty.wrap (t := .vec 8 32) (x 4) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreadsA 4
  have hy0 : Ty.wrap (t := .vec 8 32) (Vector.ofFn fun i => Ty.extractVecElem 8 32 i
      (s.mem.readAt b 256)) = Ty.wrap (t := .vec 8 32) (y 0) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreadsB 0
  have hy1 : Ty.wrap (t := .vec 8 32) (Vector.ofFn fun i => Ty.extractVecElem 8 32 i
      (s.mem.readAt (b.add 32#64) 256)) = Ty.wrap (t := .vec 8 32) (y 1) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreadsB 1
  have hy2 : Ty.wrap (t := .vec 8 32) (Vector.ofFn fun i => Ty.extractVecElem 8 32 i
      (s.mem.readAt (b.add 64#64) 256)) = Ty.wrap (t := .vec 8 32) (y 2) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreadsB 2
  have hy3 : Ty.wrap (t := .vec 8 32) (Vector.ofFn fun i => Ty.extractVecElem 8 32 i
      (s.mem.readAt (b.add 96#64) 256)) = Ty.wrap (t := .vec 8 32) (y 3) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreadsB 3
  have hy4 : Ty.wrap (t := .vec 8 32) (Vector.ofFn fun i => Ty.extractVecElem 8 32 i
      (s.mem.readAt (b.add 128#64) 256)) = Ty.wrap (t := .vec 8 32) (y 4) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreadsB 4
  have hfa0 := ha.fits_add (k := 0) (count := 32) (by decide)
  have hfa1 := ha.fits_add (k := 32) (count := 32) (by decide)
  have hfa2 := ha.fits_add (k := 64) (count := 32) (by decide)
  have hfa3 := ha.fits_add (k := 96) (count := 32) (by decide)
  have hfa4 := ha.fits_add (k := 128) (count := 32) (by decide)
  have hfb0 := hb.fits_add (k := 0) (count := 32) (by decide)
  have hfb1 := hb.fits_add (k := 32) (count := 32) (by decide)
  have hfb2 := hb.fits_add (k := 64) (count := 32) (by decide)
  have hfb3 := hb.fits_add (k := 96) (count := 32) (by decide)
  have hfb4 := hb.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hfa0 hfb0 hx0 hy0
  func_init
  block_init
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  as_aux_lemma =>
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    simp only [hS] at hx0
    step_load [hx0] inline
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    have hgep := ha.gep (k := 32) (by decide)
    norm_num only [Nat.cast_ofNat] at hgep
    simp only [hS] at hgep
    step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
        Operation.GepSignedRange]
    clear hgep
    simp only [hS] at hx1
    step_load [hx1] inline
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    have hgep := ha.gep (k := 64) (by decide)
    norm_num only [Nat.cast_ofNat] at hgep
    simp only [hS] at hgep
    step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
        Operation.GepSignedRange]
    clear hgep
    simp only [hS] at hx2
    step_load [hx2] inline
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    have hgep := ha.gep (k := 96) (by decide)
    norm_num only [Nat.cast_ofNat] at hgep
    simp only [hS] at hgep
    step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
        Operation.GepSignedRange]
    clear hgep
    simp only [hS] at hx3
    step_load [hx3] inline
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    have hgep := ha.gep (k := 128) (by decide)
    norm_num only [Nat.cast_ofNat] at hgep
    simp only [hS] at hgep
    step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
        Operation.GepSignedRange]
    clear hgep
    simp only [hS] at hx4
    step_load [hx4] inline
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    simp only [hS] at hy0
    step_load [hy0] inline
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    have hgep := hb.gep (k := 32) (by decide)
    norm_num only [Nat.cast_ofNat] at hgep
    simp only [hS] at hgep
    step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
        Operation.GepSignedRange]
    clear hgep
    simp only [hS] at hy1
    step_load [hy1] inline
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    have hgep := hb.gep (k := 64) (by decide)
    norm_num only [Nat.cast_ofNat] at hgep
    simp only [hS] at hgep
    step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
        Operation.GepSignedRange]
    clear hgep
    simp only [hS] at hy2
    step_load [hy2] inline
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    as_aux_lemma =>
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      have hgep := hb.gep (k := 96) (by decide)
      norm_num only [Nat.cast_ofNat] at hgep
      simp only [hS] at hgep
      step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
          Operation.GepSignedRange]
      clear hgep
      simp only [hS] at hy3
      step_load [hy3] inline
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      have hgep := hb.gep (k := 128) (by decide)
      norm_num only [Nat.cast_ofNat] at hgep
      simp only [hS] at hgep
      step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
          Operation.GepSignedRange]
      clear hgep
      simp only [hS] at hy4
      step_load [hy4] inline
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp] named
      as_aux_lemma =>
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        step_pure [expandOfFn, avx2_execution_simp] named
        as_aux_lemma =>
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp]
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp]
          step_pure [expandOfFn, avx2_execution_simp]
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp]
          step_pure [expandOfFn, avx2_execution_simp]
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp] named
          as_aux_lemma =>
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp]
            step_pure [expandOfFn, avx2_execution_simp]
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp]
            step_pure [expandOfFn, avx2_execution_simp]
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp]
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp]
            step_pure [expandOfFn, avx2_execution_simp]
            step_pure [expandOfFn, avx2_execution_simp]
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp]
            step_pure [expandOfFn, avx2_execution_simp]
            step_pure [expandOfFn, avx2_execution_simp]
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            step_pure [expandOfFn, avx2_execution_simp] named
            as_aux_lemma =>
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp] named
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp] named
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp] named
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp] named
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp]
              step_pure [expandOfFn, avx2_execution_simp] named
              clear hreadsA hx0 hx1 hx2 hx3 hx4 hreadsB hy0 hy1 hy2 hy3 hy4
              have htail := stores_run E S r ![v396, v401, v405, v410, v415] hr
                (by env_reads) (by env_reads) (by env_reads)
                (by env_reads) (by env_reads) (by env_reads)
              rw [htail]
              clear htail
              simp only [EffectM.bind_eq, PoisonOr.value_bind, reduceBlockExit, Exit.run,
                Regs.read_nil, EffectM.pure_eq, reduceFuncContinue]
              rw [hS]
              try erase_frame
              subst_vars
              simp [storeBlocks, wordTrace, Pointer.add, expandOfFn, avx2_execution_simp,
                zipWith_eq_ofFn]

/-- Exact memory-to-memory execution of the imported AVX2 region, including
all five stores. Field-size bounds are needed only for arithmetic refinement. -/
theorem kernel_call (r a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 160) (ha : SmallRange s.mem a 160)
    (hb : SmallRange s.mem b 160) :
    program.call (program.args (.value r) (.value a) (.value b)) s =
      .value (.nil, {s with mem := storeBlocks s.mem r (wordTrace (readBlocks s.mem a) (readBlocks s.mem b))}) := by
  apply kernel_call_of_reads r a b s _ _ hwf hr ha hb
  all_goals intro k
  all_goals simp only [readBlocks, Ty.unflatten_vec]
  all_goals rfl

end Agave.Ed25519.Avx2FieldMul.Execution
