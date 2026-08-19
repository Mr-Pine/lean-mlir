/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Group.Unbundled.Int


-- Core
-- ====
import LeanMLIR


-- Projects
-- ========

-- Eventually, all projects must be imported.
import SSA.Projects.InstCombine.Alive
import SSA.Projects.FullyHomomorphicEncryption
import SSA.Projects.Tensor1D.Tensor1D
import SSA.Projects.Tensor2D.Tensor2D
import SSA.Projects.Holor.Holor
import SSA.Projects.PaperExamples.PaperExamples
import SSA.Projects.Scf.ScfFunctor
import SSA.Projects.LeanMlirCommon.LeanMlirCommon
import SSA.Projects.SLLVM.SLLVM
import SSA.Projects.Firedancer.Avx512.Proof.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.Avx512.Proof.fd_r43x6_mul_fast
import SSA.Projects.Firedancer.Avx512.Proof.fd_r43x6_quad_mul_fast
import SSA.Projects.Firedancer.Avx512.Proof.fd_r43x6_quad_sqr_fast
import SSA.Projects.Firedancer.Avx512.Proof.fd_long_if
import SSA.Projects.Firedancer.Avx512.Mlir.fd_r43x6_is_nonzero
import SSA.Projects.Firedancer.Avx512.Proof.fd_r43x6_biased_carry_propagate_limbs
import SSA.Projects.Firedancer.Avx512.Proof.fd_r43x6_mod_nearly_reduced_limbs
import SSA.Projects.Firedancer.Avx512.Proof.fd_r43x6_is_nonzero
import SSA.Projects.Firedancer.Avx512.Proof.IsNonzeroTest


-- EXPERIMENTAL
-- ============
