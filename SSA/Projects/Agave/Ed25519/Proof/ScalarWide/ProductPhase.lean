import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ProductState
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryTail

/-! Compose all actual product columns, retaining scratch stores and proving
that none changes the as-yet unread input limbs. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 100000

structure ProductReady (E : Env program.Γ) (left right : Pointer)
    (scratch : Fin 9 → Pointer) : Prop where
  left : E.read (%arg1) = .value left
  right : E.read (%arg2) = .value right
  offset1 : E.read (%1) = .value 8#64
  offset2 : E.read (%2) = .value 16#64
  offset3 : E.read (%3) = .value 24#64
  offset4 : E.read (%4) = .value 32#64
  scratch1 : E.read (%25) = .value (scratch 1)
  scratch2 : E.read (%26) = .value (scratch 2)
  scratch3 : E.read (%27) = .value (scratch 3)
  scratch4 : E.read (%28) = .value (scratch 4)
  scratch5 : E.read (%29) = .value (scratch 5)
  scratch6 : E.read (%30) = .value (scratch 6)
  scratch7 : E.read (%31) = .value (scratch 7)
  scratch8 : E.read (%32) = .value (scratch 8)

/-- Execute indices 33–121, including all ten original input loads and eight
scratch writes. Input/scratch separation is a pointer fact, not an execution premise. -/
theorem product_run (p : Primitives) (E : Env program.Γ) (state : GlobalState)
    (a b : Fin 5 → BitVec 64) (left right : Pointer) (scratch : Fin 9 → Pointer)
    (hr : ProductReady E left right scratch)
    (hlive : SmallRange state.mem left 40) (hrive : SmallRange state.mem right 40)
    (hscratch : ∀ i, Fits state.mem (scratch i) 128)
    (hdleft : ∀ i, (scratch i).id ≠ left.id) (hdright : ∀ i, (scratch i).id ≠ right.id)
    (ha : ∀ i : Fin 5, state.mem.readAt (left.add (BitVec.ofNat 64 (8 * i.val))) 64 = a i)
    (hb : ∀ i : Fin 5, state.mem.readAt (right.add (BitVec.ofNat 64 (8 * i.val))) 64 = b i) :
    (program.entry p).runBodyFrom E 33 state =
      (program.entry p).runBodyFrom (productEnvs E a b left right 8) 122
        (productStates state a b left right scratch 8) := by
  let es := productEnvs E a b left right
  let ss := productStates state a b left right scratch
  have hleft := hr.left
  have hright := hr.right
  have hoffset1 := hr.offset1
  have hoffset2 := hr.offset2
  have hoffset3 := hr.offset3
  have hoffset4 := hr.offset4
  have hscratch1 := hr.scratch1
  have hscratch2 := hr.scratch2
  have hscratch3 := hr.scratch3
  have hscratch4 := hr.scratch4
  have hscratch5 := hr.scratch5
  have hscratch6 := hr.scratch6
  have hscratch7 := hr.scratch7
  have hscratch8 := hr.scratch8
  have hal := ha 0
  have hbr := hb 0
  simp only [Fin.val_zero, Nat.mul_zero, Pointer.add_zero] at hal hbr
  have hfleft : Fits state.mem left 64 := by
    simpa only [Pointer.add_zero] using hlive.fits_add (k := 0) (count := 8) (by decide)
  have hfright : Fits state.mem right 64 := by
    simpa only [Pointer.add_zero] using hrive.fits_add (k := 0) (count := 8) (by decide)
  have h0 : List.foldlM Instr.run E (((program.entry p).body.drop 33).take 17) state =
      .value (es 0, ss 0) := by
    simpa only [hal, hbr, es, ss, productEnvs, productStates,
      Matrix.cons_val_zero] using input_product_run p E state left right
      hr.left hr.right hfleft hfright
  have h1 : List.foldlM Instr.run (es 0) (((program.entry p).body.drop 50).take 10) (ss 0) =
      .value (es 1, ss 1) := by
    apply column1_run p (es 0) (ss 0) a b left right (scratch 1)
    · simp [es, productEnvs, inputProductEnv, mlir_env]
    · simp [es, productEnvs, inputProductEnv, mlir_env]
    · simpa [es, productEnvs, inputProductEnv, mlir_env] using hleft
    · simpa [es, productEnvs, inputProductEnv, mlir_env] using hright
    · simpa [es, productEnvs, inputProductEnv, mlir_env] using hoffset1
    · exact productStates_smallRange state a b left right scratch left 40 hlive 0
    · exact productStates_smallRange state a b left right scratch right 40 hrive 0
    · rw [productStates_read state a b left right scratch (right.add 8#64) 64
        (by simpa only [Pointer.add_id] using hdright) 0]
      exact hb 1
    · rw [productStates_read state a b left right scratch (left.add 8#64) 64
        (by simpa only [Pointer.add_id] using hdleft) 0]
      exact ha 1
    · simpa [es, productEnvs, inputProductEnv, mlir_env] using hscratch1
    · exact productStates_fits state a b left right scratch (scratch 1) 128 (hscratch 1) 0
  have h2 : List.foldlM Instr.run (es 1) (((program.entry p).body.drop 60).take 12) (ss 1) =
      .value (es 2, ss 2) := by
    apply column2_run p (es 1) (ss 1) a b left right (scratch 2)
    · simp [es, productEnvs, inputProductEnv, column1Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, mlir_env]
    · simpa [es, productEnvs, inputProductEnv, column1Env, mlir_env] using hleft
    · simpa [es, productEnvs, inputProductEnv, column1Env, mlir_env] using hright
    · simpa [es, productEnvs, inputProductEnv, column1Env, mlir_env] using hoffset2
    · exact productStates_smallRange state a b left right scratch left 40 hlive 1
    · exact productStates_smallRange state a b left right scratch right 40 hrive 1
    · rw [productStates_read state a b left right scratch (right.add 16#64) 64
        (by simpa only [Pointer.add_id] using hdright) 1]
      exact hb 2
    · rw [productStates_read state a b left right scratch (left.add 16#64) 64
        (by simpa only [Pointer.add_id] using hdleft) 1]
      exact ha 2
    · simpa [es, productEnvs, inputProductEnv, column1Env, mlir_env] using hscratch2
    · exact productStates_fits state a b left right scratch (scratch 2) 128 (hscratch 2) 1
  have h3 : List.foldlM Instr.run (es 2) (((program.entry p).body.drop 72).take 14) (ss 2) =
      .value (es 3, ss 3) := by
    apply column3_run p (es 2) (ss 2) a b left right (scratch 3)
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, mlir_env]
    · simpa [es, productEnvs, inputProductEnv, column1Env, column2Env, mlir_env] using hleft
    · simpa [es, productEnvs, inputProductEnv, column1Env, column2Env, mlir_env] using hright
    · simpa [es, productEnvs, inputProductEnv, column1Env, column2Env, mlir_env] using hoffset3
    · exact productStates_smallRange state a b left right scratch left 40 hlive 2
    · exact productStates_smallRange state a b left right scratch right 40 hrive 2
    · rw [productStates_read state a b left right scratch (right.add 24#64) 64
        (by simpa only [Pointer.add_id] using hdright) 2]
      exact hb 3
    · rw [productStates_read state a b left right scratch (left.add 24#64) 64
        (by simpa only [Pointer.add_id] using hdleft) 2]
      exact ha 3
    · simpa [es, productEnvs, inputProductEnv, column1Env, column2Env, mlir_env] using hscratch3
    · exact productStates_fits state a b left right scratch (scratch 3) 128 (hscratch 3) 2
  have h4 : List.foldlM Instr.run (es 3) (((program.entry p).body.drop 86).take 16) (ss 3) =
      .value (es 4, ss 4) := by
    apply column4_run p (es 3) (ss 3) a b left right (scratch 4)
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, mlir_env]
    · simpa [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, mlir_env] using hleft
    · simpa [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, mlir_env] using hright
    · simpa [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, mlir_env] using hoffset4
    · exact productStates_smallRange state a b left right scratch left 40 hlive 3
    · exact productStates_smallRange state a b left right scratch right 40 hrive 3
    · rw [productStates_read state a b left right scratch (right.add 32#64) 64
        (by simpa only [Pointer.add_id] using hdright) 3]
      exact hb 4
    · rw [productStates_read state a b left right scratch (left.add 32#64) 64
        (by simpa only [Pointer.add_id] using hdleft) 3]
      exact ha 4
    · simpa [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, mlir_env] using hscratch4
    · exact productStates_fits state a b left right scratch (scratch 4) 128 (hscratch 4) 3
  have h5 : List.foldlM Instr.run (es 4) (((program.entry p).body.drop 102).take 8) (ss 4) =
      .value (es 5, ss 5) := by
    apply column5_run p (es 4) (ss 4) a b left right (scratch 5)
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, mlir_env]
    · simpa [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, mlir_env] using hscratch5
    · exact productStates_fits state a b left right scratch (scratch 5) 128 (hscratch 5) 4
  have h6 : List.foldlM Instr.run (es 5) (((program.entry p).body.drop 110).take 6) (ss 5) =
      .value (es 6, ss 6) := by
    apply column6_run p (es 5) (ss 5) a b left right (scratch 6)
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, mlir_env]
    · simpa [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, mlir_env] using hscratch6
    · exact productStates_fits state a b left right scratch (scratch 6) 128 (hscratch 6) 5
  have h7 : List.foldlM Instr.run (es 6) (((program.entry p).body.drop 116).take 4) (ss 6) =
      .value (es 7, ss 7) := by
    apply column7_run p (es 6) (ss 6) a b left right (scratch 7)
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, mlir_env]
    · simpa [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, mlir_env] using hscratch7
    · exact productStates_fits state a b left right scratch (scratch 7) 128 (hscratch 7) 6
  have h8 : List.foldlM Instr.run (es 7) (((program.entry p).body.drop 120).take 2) (ss 7) =
      .value (es 8, ss 8) := by
    apply column8_run p (es 7) (ss 7) a b left right (scratch 8)
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, mlir_env]
    · simp [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, mlir_env]
    · simpa [es, productEnvs, inputProductEnv, column1Env, column2Env, column3Env, column4Env, column5Env, column6Env, column7Env, mlir_env] using hscratch8
    · exact productStates_fits state a b left right scratch (scratch 8) 128 (hscratch 8) 7
  exact (runBodyFrom_chunk h0).trans
    ((runBodyFrom_chunk h1).trans ((runBodyFrom_chunk h2).trans
      ((runBodyFrom_chunk h3).trans ((runBodyFrom_chunk h4).trans
        ((runBodyFrom_chunk h5).trans ((runBodyFrom_chunk h6).trans
          ((runBodyFrom_chunk h7).trans (runBodyFrom_chunk h8))))))))

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
