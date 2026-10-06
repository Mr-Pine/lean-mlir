import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.Bounds
import SSA.Projects.Agave.Ed25519.Spec.PointArithmetic

/-! The exact point-level operation ordering and caller-bound preservation.
These are integer limb specifications. The observation modules contain the
actual RIR; relating their execution to this composition remains a separate
obligation. -/
namespace Agave.Ed25519.Avx2PointAdd
open Avx2FieldMul PointArithmetic

abbrev Point := Extended Limbs

def pointReduced (P : Point) : Prop :=
  reduced P.X ∧ reduced P.Y ∧ reduced P.Z ∧ reduced P.T

def pointWide (P : Point) : Prop :=
  wide P.X ∧ wide P.Y ∧ wide P.Z ∧ wide P.T

def prepare (P : Point) : Point :=
  ⟨lazyDiff P.X P.Y, lazySum P.X P.Y, P.Z, P.T⟩

def multiply (P Q : Point) : Point :=
  ⟨product P.X Q.X, product P.Y Q.Y, product P.Z Q.Z, product P.T Q.T⟩

def diffSum (P : Point) : Point :=
  ⟨lazyDiff P.X P.Y, lazySum P.X P.Y, lazyDiff P.Z P.T, lazySum P.Z P.T⟩

def shuffleABDC (P : Point) : Point := ⟨P.X, P.Y, P.T, P.Z⟩
def shuffleADDA (P : Point) : Point := ⟨P.X, P.T, P.T, P.X⟩
def shuffleCBCB (P : Point) : Point := ⟨P.Z, P.Y, P.Z, P.Y⟩

def negate (P : Point) : Point := ⟨P.Y, P.X, P.Z, lazyNeg P.T⟩

def add (P C : Point) : Point :=
  let t := diffSum (shuffleABDC (multiply (prepare P) C))
  multiply (shuffleADDA t) (shuffleCBCB t)

def sub (P C : Point) : Point := add P (negate C)

theorem prepare_wide {P : Point} (h : pointReduced P) : pointWide (prepare P) :=
  ⟨lazyDiff_wide h.2.1, lazySum_wide h.1 h.2.1,
    reduced_wide h.2.2.1, reduced_wide h.2.2.2⟩

theorem multiply_reduced {P Q : Point} (hP : pointWide P) (hQ : pointWide Q) :
    pointReduced (multiply P Q) :=
  ⟨wide_product_reduced hP.1 hQ.1, wide_product_reduced hP.2.1 hQ.2.1,
    wide_product_reduced hP.2.2.1 hQ.2.2.1,
    wide_product_reduced hP.2.2.2 hQ.2.2.2⟩

theorem diffSum_wide {P : Point} (h : pointReduced P) : pointWide (diffSum P) :=
  ⟨lazyDiff_wide h.2.1, lazySum_wide h.1 h.2.1,
    lazyDiff_wide h.2.2.2, lazySum_wide h.2.2.1 h.2.2.2⟩

/-- Both multiplication calls satisfy the enlarged limb contract and the
result restores the reduced invariant used by the next ladder operation. -/
theorem add_reduced {P C : Point} (hP : pointReduced P) (hC : pointWide C) :
    pointReduced (add P C) := by
  have hm := multiply_reduced (prepare_wide hP) hC
  have hs : pointReduced (shuffleABDC (multiply (prepare P) C)) :=
    ⟨hm.1, hm.2.1, hm.2.2.2, hm.2.2.1⟩
  have hd := diffSum_wide hs
  exact multiply_reduced ⟨hd.1, hd.2.2.2, hd.2.2.2, hd.1⟩
    ⟨hd.2.2.1, hd.2.1, hd.2.2.1, hd.2.1⟩

/-- One lazy cache negation fits the same enlarged multiplication contract. -/
theorem negate_wide {C : Point} (h : pointWide C) : pointWide (negate C) :=
  ⟨h.2.1, h.1, h.2.2.1, lazyNeg_wide _⟩

theorem sub_reduced {P C : Point} (hP : pointReduced P) (hC : pointWide C) :
    pointReduced (sub P C) := add_reduced hP (negate_wide hC)

section Algebra
variable {K : Type*} [CommRing K]

def laneMul (P Q : Extended K) : Extended K :=
  ⟨P.X * Q.X, P.Y * Q.Y, P.Z * Q.Z, P.T * Q.T⟩
def laneDiffSum (P : Extended K) : Extended K :=
  ⟨P.Y - P.X, P.Y + P.X, P.T - P.Z, P.T + P.Z⟩

def addPipeline (P C : Extended K) : Extended K :=
  let p : Extended K := ⟨P.Y - P.X, P.Y + P.X, P.Z, P.T⟩
  let m := laneMul p C
  let t := laneDiffSum ⟨m.X, m.Y, m.T, m.Z⟩
  laneMul ⟨t.X, t.T, t.T, t.X⟩ ⟨t.Z, t.Y, t.Z, t.Y⟩

/-- The physical ABDC, ADDA and CBCB ordering yields the existing point spec. -/
theorem addPipeline_eq (P C : Extended K) :
    addPipeline P C = avx2AddCached P C := rfl

/-- Composing the actual lane schedule with serial cached coordinates. -/
theorem addPipeline_cacheScale (c : K) (P C : Extended K) :
    addPipeline P (cacheScale c C) = scale (c^2) (serialAddCached P C) :=
  avx2AddCached_cacheScale c P C

theorem negateCache_cacheScale (c : K) (C : Extended K) :
    negateCache (cacheScale c C) = cacheScale c (negateCache C) := by
  ext <;> simp [negateCache, cacheScale]

theorem subPipeline_cacheScale (c : K) (P C : Extended K) :
    addPipeline P (negateCache (cacheScale c C)) =
      scale (c^2) (serialAddCached P (negateCache C)) := by
  rw [negateCache_cacheScale]
  exact addPipeline_cacheScale c P (negateCache C)
end Algebra
end Agave.Ed25519.Avx2PointAdd
