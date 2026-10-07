import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionProgram
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionMemory
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionSuffix
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionInstructions

import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

namespace Agave.Ed25519.Avx2SquareNegateD.Execution
open LeanMLIR.RIR
attribute [local implicit_reducible] Ty.width
open Reduce64.Execution
open Avx2FieldMul.Execution

attribute [-mlir_operation] Operation.bitcast Operation.add Operation.mul


-- Keep self-products pointwise so the widening overflow rules can discharge each lane.
attribute [-simp] Vector.zipWith_self in
set_option maxHeartbeats 64000000 in
/-- Actual execution with independent input vectors fixed by their memory
reads. The arithmetic proof never unfolds the initial memory representation. -/
theorem kernel_call_of_reads (r a : Pointer) (s : GlobalState) (x : Blocks)
    (hwf : s.WF) (hr : SmallRange s.mem r 160) (ha : SmallRange s.mem a 160)
    (hreadsA : ∀ k : Fin 5,
      (Ty.vec 8 32).unflatten
        (s.mem.readAt (a.add (BitVec.ofNat 64 (32 * k.val))) 256) = Ty.wrap (x k)) :
    program.call (program.args (.value r) (.value a)) s =
      .value (.nil, {s with mem := storeBlocks s.mem r (wordTrace x)}) := by
  have hx0 : Ty.wrap (t := .vec 8 32) (Vector.ofFn (fun j =>
      Ty.extractVecElem 8 32 j (s.mem.readAt (a.add 0#64) 256))) =
      Ty.wrap (t := .vec 8 32) (x 0) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreadsA 0
  have hx1 : Ty.wrap (t := .vec 8 32) (Vector.ofFn (fun j =>
      Ty.extractVecElem 8 32 j (s.mem.readAt (a.add 32#64) 256))) =
      Ty.wrap (t := .vec 8 32) (x 1) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreadsA 1
  have hx2 : Ty.wrap (t := .vec 8 32) (Vector.ofFn (fun j =>
      Ty.extractVecElem 8 32 j (s.mem.readAt (a.add 64#64) 256))) =
      Ty.wrap (t := .vec 8 32) (x 2) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreadsA 2
  have hx3 : Ty.wrap (t := .vec 8 32) (Vector.ofFn (fun j =>
      Ty.extractVecElem 8 32 j (s.mem.readAt (a.add 96#64) 256))) =
      Ty.wrap (t := .vec 8 32) (x 3) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreadsA 3
  have hx4 : Ty.wrap (t := .vec 8 32) (Vector.ofFn (fun j =>
      Ty.extractVecElem 8 32 j (s.mem.readAt (a.add 128#64) 256))) =
      Ty.wrap (t := .vec 8 32) (x 4) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreadsA 4
  have hfa0 := ha.fits_add (k := 0) (count := 32) (by decide)
  have hfa1 := ha.fits_add (k := 32) (count := 32) (by decide)
  have hfa2 := ha.fits_add (k := 64) (count := 32) (by decide)
  have hfa3 := ha.fits_add (k := 96) (count := 32) (by decide)
  have hfa4 := ha.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hfa0 hx0
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
    as_aux_lemma =>
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
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp]
      step_pure [expandOfFn, avx2_execution_simp] named
      step_pure [expandOfFn, avx2_execution_simp]
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
      step_pure [expandOfFn, avx2_execution_simp]
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
        step_pure [expandOfFn, avx2_execution_simp]
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
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp]
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp]
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp]
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp]
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp]
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp]
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp]
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp]
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp]
          step_pure [expandOfFn, avx2_execution_simp] named
          step_pure [expandOfFn, avx2_execution_simp]
          step_pure [expandOfFn, avx2_execution_simp] named
          -- Identify the convolution columns before applying the independently checked suffix.
          have hcolumns : ![v281, v283, v285, v287, v289, v291, v293, v295, v297, v299] =
              columnTrace x := by
            clear hE hArgs E E₀ hreadsA hx0 hx1 hx2 hx3 hx4
            subst_vars
            funext i
            fin_cases i
            all_goals simp [columnTrace, expandOfFn, avx2_execution_simp, zipWith_eq_ofFn]
          have htail := Suffix.run E S r
            ![v281, v283, v285, v287, v289, v291, v293, v295, v297, v299] hr
            (by env_reads)
            (by env_reads) (by env_reads) (by env_reads) (by env_reads)
            (by env_reads) (by env_reads)
            (by env_reads) (by env_reads)
            (by env_reads) (by env_reads) (by env_reads) (by env_reads) (by env_reads)
            (by env_reads) (by env_reads) (by env_reads) (by env_reads) (by env_reads)
          change Suffix.resume300 E S = _
          rw [htail, hcolumns, ← wordTrace_eq_stages, hS]

/-- Exact memory-to-memory execution of the imported AVX2 region, including
all five stores. Field-size bounds are needed only for arithmetic refinement. -/
theorem kernel_call (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 160) (ha : SmallRange s.mem a 160) :
    program.call (program.args (.value r) (.value a)) s =
      .value (.nil, {s with mem := storeBlocks s.mem r (wordTrace (readBlocks s.mem a))}) := by
  apply kernel_call_of_reads r a s _ hwf hr ha
  all_goals intro k
  all_goals simp only [readBlocks, Ty.unflatten_vec]
  all_goals rfl

end Agave.Ed25519.Avx2SquareNegateD.Execution
