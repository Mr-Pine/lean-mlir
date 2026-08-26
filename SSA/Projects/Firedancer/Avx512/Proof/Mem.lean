/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Quad
import SSA.Projects.SLLVM.Dialect.Semantics.MemoryLemmas

/-!
# Kernels that write their results through pointers

`fd_r43x6_quad_sqr_fast` and `fd_r43x6_quad_mul_fast` take their three
`fd_r43x6_t` results as out-parameters and end in three
`llvm.store … : (vector<8xi64>, !llvm.ptr) -> ()`. Lifted verbatim, such a
region is one `.impure` `Com` with three `!llvm.ptr` block arguments and no
results.

This file carries what is common to reasoning about them: the valuation, the
`EffectM` shape of a whole-vector store, and the bridge from "the denotation is
these three stores" to "these three vectors are in memory afterwards".

## The aliasing assumption

`storeVec3_readback` assumes the three destination blocks are pairwise
distinct. That is *not* something the IR guarantees: the kernel's pointer
parameters carry `nocapture noundef writeonly` and, notably, **not**
`noalias`. It is a fact about the call site -- `FD_R43X6_QUAD_SQR_FAST` passes
`&_R03, &_R14, &_R25`, three distinct locals -- and so it appears here as a
hypothesis rather than as something read off the program.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The `LLVM.Ty` of an `fd_r43x6_t`, which is the shape every load and store
in these kernels has. -/
abbrev QVecTy : LLVM.Ty := .vector 8 (.bitvec (.concrete 64))

/-- The dialect type of a pointer. -/
abbrev PTy : SLLVM.Ty := SLLVM.Ty.ptr

@[simp] theorem width_QVecTy : LLVM.Ty.width QVecTy = 512 := rfl

/-- Storing a whole `fd_r43x6_t` through a pointer, at the `EffectM` type the
denotation of an `llvm.store` has. -/
def storeVec (p : SLLVM.Ptr) (v : Vector (PoisonOr (BitVec 64)) 8) : EffectM Unit :=
  SLLVM.store p QVecTy v

/-- Valuation for a kernel with three pointer out-parameters and a quad input,
in the order `fd_r43x6_quad_sqr_fast` declares them. Block arguments
enter a `Ctxt` in *reverse* declaration order (`%arg0` is the deepest
variable), so the list reads backwards: the three vectors first, then the three
pointers.

Built as an explicit `Valuation.cons` chain rather than with
`Valuation.ofHVector`: the `@[simp]` lemma `Valuation.ofHVector_apply` rewrites
a lookup on an `ofHVector` into an `HVector` index, for which there are no
reduction lemmas in the per-opcode simp sets, so the operand of a `vpmadd52`
would get stuck. On a `cons` chain `Valuation.cons_last` and
`Valuation.cons_toCons` reduce the lookup all the way. -/
def quadValMem (p₀ p₁ p₂ : SLLVM.Ptr) (x: Quad) :
    Ctxt.Valuation (Ctxt.ofList [QTy, QTy, QTy, PTy, PTy, PTy]) :=
  x.v25.map PoisonOr.value ::ᵥ x.v14.map PoisonOr.value ::ᵥ x.v03.map PoisonOr.value ::ᵥ
    p₂ ::ᵥ p₁ ::ᵥ p₀ ::ᵥ Ctxt.Valuation.nil

/-- As `quadValMem`, for a kernel with two quad inputs and three pointers. -/
def quadDualValMem (p₀ p₁ p₂ : SLLVM.Ptr) (x y: Quad) :
    Ctxt.Valuation (Ctxt.ofList [QTy, QTy, QTy, QTy, QTy, QTy, PTy, PTy, PTy]) :=
    y.v25.map PoisonOr.value ::ᵥ y.v14.map PoisonOr.value ::ᵥ y.v03.map PoisonOr.value ::ᵥ
    x.v25.map PoisonOr.value ::ᵥ x.v14.map PoisonOr.value ::ᵥ x.v03.map PoisonOr.value ::ᵥ
    p₂ ::ᵥ p₁ ::ᵥ p₀ ::ᵥ Ctxt.Valuation.nil

/-! ## A fully-defined vector flattens -/

/-- A vector of values -- which is what every one of these kernels produces --
is `Defined`, so it has a flat encoding and the store does not raise UB. -/
theorem flatten_map_value (v : Vector (BitVec 64) 8) :
    LLVM.Ty.flatten QVecTy (v.map PoisonOr.value)
      = .value (LLVM.Ty.flattenBV QVecTy (v.map PoisonOr.value)) := by
  rw [LLVM.Ty.flatten, if_pos]
  intro i
  show LLVM.Ty.ofBitvec ((v.map PoisonOr.value)[i.val]) ≠ .poison
  rw [Vector.getElem_map]
  exact PoisonOr.value_ne_poison _

/-- The bits a `fd_r43x6_t` occupies in memory. -/
def vecBits (v : Vector (BitVec 64) 8) : BitVec 512 :=
  LLVM.Ty.flattenBV QVecTy (v.map PoisonOr.value)

/-- The memory state after writing `v` through `p`. -/
def _root_.LeanMLIR.MemoryState.writeVec (m : MemoryState) (p : Pointer)
    (v : Vector (BitVec 64) 8) : MemoryState := m.splice p (vecBits v)

/-! ## Running three stores -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- Three whole-vector stores through three live, big-enough pointers succeed,
and leave exactly the three writes behind. No distinctness is needed here: if
two of the pointers alias, the later write simply wins, which is what the
nested `writeVec`s say. -/
theorem run_storeVec3 {p₀ p₁ p₂ : Pointer} {u v w : Vector (BitVec 64) 8} {s : GlobalState}
    (h₀ : Fits s.mem p₀ 512) (h₁ : Fits (s.mem.writeVec p₀ u) p₁ 512)
    (h₂ : Fits ((s.mem.writeVec p₀ u).writeVec p₁ v) p₂ 512) :
    (do storeVec (.value p₀) (u.map PoisonOr.value)
        storeVec (.value p₁) (v.map PoisonOr.value)
        storeVec (.value p₂) (w.map PoisonOr.value)
        pure (HVector.nil : HVector TyDenote.toType ([] : List SLLVM.Ty))).run s
      = .value (HVector.nil,
          { s with mem := ((s.mem.writeVec p₀ u).writeVec p₁ v).writeVec p₂ w }) := by
  have e₀ := SLLVM.run_liftM (s := s) (SLLVM.run_store (flatten_map_value u) h₀)
  have e₁ := SLLVM.run_liftM (s := { s with mem := s.mem.writeVec p₀ u })
    (SLLVM.run_store (flatten_map_value v) h₁)
  have e₂ := SLLVM.run_liftM
    (s := { s with mem := (s.mem.writeVec p₀ u).writeVec p₁ v })
    (SLLVM.run_store (flatten_map_value w) h₂)
  simp only [storeVec, MemoryState.writeVec, vecBits] at e₀ e₁ e₂ ⊢
  simp only [EffectM.run_bind, e₀, PoisonOr.value_bind, e₁, e₂, EffectM.run_pure]

/-! ## Reading the results back -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **Readback.** After the three stores, each pointer addresses the vector
that was written through it -- provided the three destination blocks are
pairwise distinct. -/
theorem storeVec3_readback {p₀ p₁ p₂ : Pointer} {u v w : Vector (BitVec 64) 8}
    {m : MemoryState}
    (h₀ : Fits m p₀ 512) (h₁ : Fits m p₁ 512) (h₂ : Fits m p₂ 512)
    (d₀₁ : p₀.id ≠ p₁.id) (d₀₂ : p₀.id ≠ p₂.id) (d₁₂ : p₁.id ≠ p₂.id) :
    let m' := ((m.writeVec p₀ u).writeVec p₁ v).writeVec p₂ w
    (SLLVM.load (.value p₀) QVecTy).run m' = .value (u.map PoisonOr.value, m')
      ∧ (SLLVM.load (.value p₁) QVecTy).run m' = .value (v.map PoisonOr.value, m')
      ∧ (SLLVM.load (.value p₂) QVecTy).run m' = .value (w.map PoisonOr.value, m') := by
  obtain ⟨b₀, hb₀, hl₀⟩ := h₀
  obtain ⟨b₁, hb₁, hl₁⟩ := h₁
  obtain ⟨b₂, hb₂, hl₂⟩ := h₂
  simp only [MemoryState.writeVec, vecBits]
  refine ⟨?_, ?_, ?_⟩
  · refine SLLVM.run_load_of_splice (flatten_map_value u) hl₀ ?_
    rw [SLLVM.getElem?_splice_ne (Ne.symm d₀₂), SLLVM.getElem?_splice_ne (Ne.symm d₀₁)]
    exact SLLVM.getElem?_splice_self hb₀
  · refine SLLVM.run_load_of_splice (flatten_map_value v) hl₁ ?_
    rw [SLLVM.getElem?_splice_ne (Ne.symm d₁₂)]
    exact SLLVM.getElem?_splice_self (by rw [SLLVM.getElem?_splice_ne d₀₁, hb₁])
  · exact SLLVM.run_load_of_splice (flatten_map_value w) hl₂
      (SLLVM.getElem?_splice_self
        (by rw [SLLVM.getElem?_splice_ne d₁₂, SLLVM.getElem?_splice_ne d₀₂, hb₂]))

end Firedancer.Avx512
