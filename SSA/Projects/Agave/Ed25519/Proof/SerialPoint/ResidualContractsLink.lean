import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointContractMemory
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CachedSubExecution
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.AffineAddExecution
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.AffineSubExecution
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.ResidualRepresentation

/-! The three residual serial helpers, linked to their exact RIR executions.
The raw readback theorems require only live input/output ranges and caller limb
bounds. The CFG adapters preserve the existing contract interface. The group
corollaries apply the separately proved completed-to-extended arithmetic and
carry full projective validity, including a nonzero Z coordinate.
-/
namespace Agave.Ed25519.SerialPoint.Execution
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
open DoubleBase.SerialContracts

/-- The affine decoder uses exactly the three physical fields; its mathematical
Z placeholder is zero and needs no fourth memory range. -/
theorem readAffineCached_words (s : GlobalState) (p : Pointer) :
    readAffineCached s p = unsignedPoint (affineCacheFromWords (readPointWords s p)) := by
  apply PointArithmetic.Extended.ext <;> funext i <;> fin_cases i <;>
    simp [readAffineCached, readField, unsignedPoint, affineCacheFromWords,
      pointFromWords, readPointWords, unsigned, readLimbs, Pointer.add_add]

/-- Exact imported cached_sub result and frame, with no disjointness premise. -/
theorem cached_sub_readback (s : GlobalState) (out input cached : Pointer)
    (hwf : s.WF) (hout : SmallRange s.mem out 160)
    (hin : SmallRange s.mem input 160) (hcache : SmallRange s.mem cached 160)
    (hP : PointTight (readPoint s input)) (hC : PointBounded (readCached s cached)) :
    ∃ final, cached_sub.call (cached_sub.args (.value out) (.value input) (.value cached)) s =
      .value (.nil, final) ∧ WritesOnly out 160 s final ∧
      readPoint final out = cachedSubCompleted (readPoint s input) (readCached s cached) ∧
      PointBounded (readPoint final out) := by
  have hp : PointTight (unsignedPoint (pointFromWords (readPointWords s input))) := by
    rwa [readPoint_words] at hP
  have hc : PointBounded (unsignedPoint (cacheFromWords (readPointWords s cached))) := by
    rwa [readCached_words] at hC
  let output := cachedSubWordTrace (readPointWords s input) (readPointWords s cached)
  let final := pointPost s out output 6
  have hread : readPoint final out = cachedSubCompleted (readPoint s input) (readCached s cached) := by
    rw [readPoint_words, pointPost_readback s out output 6 hout,
      readPoint_words, readCached_words]
    exact cachedSubWordTrace_unsigned _ _ hp hc
  refine ⟨final, cached_sub_call out input cached s hwf hout hin hcache,
    pointPost_writesOnly s out output 6 hwf hout, hread, ?_⟩
  rw [hread]
  exact cachedSubCompleted_bounded _ _ hP hC

/-- The residual CFG contract is discharged by the actual imported helper. -/
theorem cached_sub_contract :
    BinaryPointContract cached_sub.call 160 readCached
      cachedSubCompleted := by
  intro s out input cached hwf hout hin hcache _ _ hP hC
  exact cached_sub_readback s out input cached hwf hout hin hcache hP hC

/-- Group correctness includes a valid extended representative after the
source completed-to-extended conversion; no nonzero-result premise is assumed. -/
theorem cached_sub_represents (s : GlobalState) (out input cached : Pointer)
    (hwf : s.WF) (hout : SmallRange s.mem out 160)
    (hin : SmallRange s.mem input 160) (hcache : SmallRange s.mem cached 160)
    (hP : PointTight (readPoint s input)) (hC : PointBounded (readCached s cached))
    {Q : FieldPoint} {V W : DoubleBase.GroupPoint}
    (hPV : Tables.Represents (pointValue (readPoint s input)) V)
    (hQ : Tables.Represents Q W)
    (hCV : pointValue (readCached s cached) = PointArithmetic.serialCache _root_.Ed25519.d Q) :
    ∃ final, cached_sub.call (cached_sub.args (.value out) (.value input) (.value cached)) s =
      .value (.nil, final) ∧ WritesOnly out 160 s final ∧
      PointBounded (readPoint final out) ∧
      PointTight (asExtended (readPoint final out)) ∧
      Tables.Represents (pointValue (asExtended (readPoint final out))) (V - W) := by
  obtain ⟨final, hcall, hframe, hread, hbound⟩ :=
    cached_sub_readback s out input cached hwf hout hin hcache hP hC
  refine ⟨final, hcall, hframe, hbound, asExtended_tight _ hbound, ?_⟩
  rw [hread]
  exact cachedSubCompleted_represents _ _ hP hC hPV hQ hCV

/-- Exact imported affine_sub result and frame, with no disjointness premise. -/
theorem affine_sub_readback (s : GlobalState) (out input cached : Pointer)
    (hwf : s.WF) (hout : SmallRange s.mem out 160)
    (hin : SmallRange s.mem input 160) (hcache : SmallRange s.mem cached 120)
    (hP : PointTight (readPoint s input)) (hC : PointBounded (readAffineCached s cached)) :
    ∃ final, affine_sub.call (affine_sub.args (.value out) (.value input) (.value cached)) s =
      .value (.nil, final) ∧ WritesOnly out 160 s final ∧
      readPoint final out = affineSubCompleted (readPoint s input)
        (readAffineCached s cached).X (readAffineCached s cached).Y (readAffineCached s cached).T ∧
      PointBounded (readPoint final out) := by
  have hp : PointTight (unsignedPoint (pointFromWords (readPointWords s input))) := by
    rwa [readPoint_words] at hP
  have hc : PointBounded (unsignedPoint (affineCacheFromWords (readPointWords s cached))) := by
    rwa [readAffineCached_words] at hC
  let output := affineSubWordTrace (readPointWords s input) (readPointWords s cached)
  let final := pointPost s out output 5
  have hread : readPoint final out = affineSubCompleted (readPoint s input)
        (readAffineCached s cached).X (readAffineCached s cached).Y (readAffineCached s cached).T := by
    rw [readPoint_words, pointPost_readback s out output 5 hout,
      readPoint_words, readAffineCached_words]
    exact affineSubWordTrace_unsigned _ _ hp hc
  refine ⟨final, affine_sub_call out input cached s hwf hout hin hcache,
    pointPost_writesOnly s out output 5 hwf hout, hread, ?_⟩
  rw [hread]
  exact affineSubCompleted_bounded _ _ hP hC

/-- The residual CFG contract is discharged by the actual imported helper. -/
theorem affine_sub_contract :
    BinaryPointContract affine_sub.call 120 readAffineCached
      (fun P C => affineSubCompleted P C.X C.Y C.T) := by
  intro s out input cached hwf hout hin hcache _ _ hP hC
  exact affine_sub_readback s out input cached hwf hout hin hcache hP hC

/-- Group correctness includes a valid extended representative after the
source completed-to-extended conversion; no nonzero-result premise is assumed. -/
theorem affine_sub_represents (s : GlobalState) (out input cached : Pointer)
    (hwf : s.WF) (hout : SmallRange s.mem out 160)
    (hin : SmallRange s.mem input 160) (hcache : SmallRange s.mem cached 120)
    (hP : PointTight (readPoint s input)) (hC : PointBounded (readAffineCached s cached))
    {Q : FieldPoint} {V W : DoubleBase.GroupPoint}
    (hPV : Tables.Represents (pointValue (readPoint s input)) V)
    (hQ : Tables.Represents Q W)
    (hCV : affineCacheValue (readAffineCached s cached) = PointArithmetic.serialCache _root_.Ed25519.d Q) :
    ∃ final, affine_sub.call (affine_sub.args (.value out) (.value input) (.value cached)) s =
      .value (.nil, final) ∧ WritesOnly out 160 s final ∧
      PointBounded (readPoint final out) ∧
      PointTight (asExtended (readPoint final out)) ∧
      Tables.Represents (pointValue (asExtended (readPoint final out))) (V - W) := by
  obtain ⟨final, hcall, hframe, hread, hbound⟩ :=
    affine_sub_readback s out input cached hwf hout hin hcache hP hC
  refine ⟨final, hcall, hframe, hbound, asExtended_tight _ hbound, ?_⟩
  rw [hread]
  exact affineSubCompleted_represents _ _ hP hC hPV hQ hCV

/-- Exact imported affine_add result and frame, with no disjointness premise. -/
theorem affine_add_readback (s : GlobalState) (out input cached : Pointer)
    (hwf : s.WF) (hout : SmallRange s.mem out 160)
    (hin : SmallRange s.mem input 160) (hcache : SmallRange s.mem cached 120)
    (hP : PointTight (readPoint s input)) (hC : PointBounded (readAffineCached s cached)) :
    ∃ final, affine_add.call (affine_add.args (.value out) (.value input) (.value cached)) s =
      .value (.nil, final) ∧ WritesOnly out 160 s final ∧
      readPoint final out = affineAddCompleted (readPoint s input)
        (readAffineCached s cached).X (readAffineCached s cached).Y (readAffineCached s cached).T ∧
      PointBounded (readPoint final out) := by
  have hp : PointTight (unsignedPoint (pointFromWords (readPointWords s input))) := by
    rwa [readPoint_words] at hP
  have hc : PointBounded (unsignedPoint (affineCacheFromWords (readPointWords s cached))) := by
    rwa [readAffineCached_words] at hC
  let output := affineAddWordTrace (readPointWords s input) (readPointWords s cached)
  let final := pointPost s out output 5
  have hread : readPoint final out = affineAddCompleted (readPoint s input)
        (readAffineCached s cached).X (readAffineCached s cached).Y (readAffineCached s cached).T := by
    rw [readPoint_words, pointPost_readback s out output 5 hout,
      readPoint_words, readAffineCached_words]
    exact affineAddWordTrace_unsigned _ _ hp hc
  refine ⟨final, affine_add_call out input cached s hwf hout hin hcache,
    pointPost_writesOnly s out output 5 hwf hout, hread, ?_⟩
  rw [hread]
  exact affineAddCompleted_bounded _ _ hP hC

/-- The residual CFG contract is discharged by the actual imported helper. -/
theorem affine_add_contract :
    BinaryPointContract affine_add.call 120 readAffineCached
      (fun P C => affineAddCompleted P C.X C.Y C.T) := by
  intro s out input cached hwf hout hin hcache _ _ hP hC
  exact affine_add_readback s out input cached hwf hout hin hcache hP hC

/-- Group correctness includes a valid extended representative after the
source completed-to-extended conversion; no nonzero-result premise is assumed. -/
theorem affine_add_represents (s : GlobalState) (out input cached : Pointer)
    (hwf : s.WF) (hout : SmallRange s.mem out 160)
    (hin : SmallRange s.mem input 160) (hcache : SmallRange s.mem cached 120)
    (hP : PointTight (readPoint s input)) (hC : PointBounded (readAffineCached s cached))
    {Q : FieldPoint} {V W : DoubleBase.GroupPoint}
    (hPV : Tables.Represents (pointValue (readPoint s input)) V)
    (hQ : Tables.Represents Q W)
    (hCV : affineCacheValue (readAffineCached s cached) = PointArithmetic.serialCache _root_.Ed25519.d Q) :
    ∃ final, affine_add.call (affine_add.args (.value out) (.value input) (.value cached)) s =
      .value (.nil, final) ∧ WritesOnly out 160 s final ∧
      PointBounded (readPoint final out) ∧
      PointTight (asExtended (readPoint final out)) ∧
      Tables.Represents (pointValue (asExtended (readPoint final out))) (V + W) := by
  obtain ⟨final, hcall, hframe, hread, hbound⟩ :=
    affine_add_readback s out input cached hwf hout hin hcache hP hC
  refine ⟨final, hcall, hframe, hbound, asExtended_tight _ hbound, ?_⟩
  rw [hread]
  exact affineAddCompleted_represents _ _ hP hC hPV hQ hCV

end Agave.Ed25519.SerialPoint.Execution
