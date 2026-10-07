import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialCacheExecution
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorContext

/-! Readback and caller frame for the real serial inline cache conversion. -/
namespace Agave.Ed25519.Tables.SerialCacheExecution
open LeanMLIR.RIR SerialFieldMul SerialPoint SerialPoint.Execution
open Reduce64.Execution (SmallRange)
open DoubleBase.SerialContracts

/-- Copying a complete field copies precisely its five machine words. -/
theorem copyField_words (s : GlobalState) (out input : Pointer)
    (ho : SmallRange s.mem out 40) (hi : SmallRange s.mem input 40) :
    readLimbs {s with mem := s.mem.storeAt out (s.mem.readAt input 320)} out =
      readLimbs s input := by
  funext k
  have hsz : (BitVec.ofNat 64 (8*k.val)).toNat * 8 + 64 ≤ 320 := by
    have hk := k.isLt
    norm_num only [BitVec.toNat_ofNat]
    omega
  have hout := MemoryState.readAt_storeAt_add ho.fits
    (ho.no_wrap (k := 8*k.val) (by omega)) hsz (s.mem.readAt input 320)
  have hin := MemoryState.readAt_add_of_readAt hi.fits
    (hi.no_wrap (k := 8*k.val) (by omega)) hsz (rfl : s.mem.readAt input 320 = _)
  exact hout.trans hin.symm

/-- Exact readback keeps the physical Y+X/Y-X permutation explicit. -/
theorem cacheState_fields (s : GlobalState) (out input constant : Pointer)
    (ho : SmallRange s.mem out 160) (hi : SmallRange s.mem input 160) :
    readLimbs (cacheState s out input constant) (out.add 40) =
        subWord (readLimbs s (input.add 40)) (readLimbs s input) ∧
    readLimbs (cacheState s out input constant) out =
        addWord (readLimbs s input) (readLimbs s (input.add 40)) ∧
    readLimbs (cacheState s out input constant) (out.add 80) =
        readLimbs s (input.add 80) ∧
    readLimbs (cacheState s out input constant) (out.add 120) =
        machine (readLimbs s (input.add 120)) (readLimbs s constant) := by
  let s₀ : GlobalState := {s with mem := s.mem.storeAt (out.add 80) (s.mem.readAt (input.add 80) 320)}
  let t := machine (readLimbs s (input.add 120)) (readLimbs s constant)
  let plus := addWord (readLimbs s input) (readLimbs s (input.add 40))
  let minus := subWord (readLimbs s (input.add 40)) (readLimbs s input)
  let s₁ : GlobalState := {s₀ with mem := storeLimbs s₀.mem (out.add 120) t}
  let s₂ : GlobalState := {s₁ with mem := storeLimbs s₁.mem out plus}
  have ho₀ : SmallRange s₀.mem out 160 := ho.storeAt _ _
  have ho₁ : SmallRange s₁.mem out 160 := smallRange_storeLimbs ho₀ _ _
  have ho₂ : SmallRange s₂.mem out 160 := smallRange_storeLimbs ho₁ _ _
  have hd (i j : Fin 4) (hne : i ≠ j) :
      (Range.of (out.add (BitVec.ofNat 64 (40*i.val))) 320).Disjoint
        (Range.of (out.add (BitVec.ofNat 64 (40*j.val))) 320) := by
    apply subranges_disjoint ho (ni := 40) (nj := 40) (by omega) (by omega)
    have : i.val ≠ j.val := fun he => hne (Fin.ext he)
    omega
  have h0₁ : SmallRange s₁.mem out 40 := by simpa using smallRange_add ho₁ (k := 0) (count := 40) (by decide)
  have h0₂ : SmallRange s₂.mem out 40 := by simpa using smallRange_add ho₂ (k := 0) (count := 40) (by decide)
  have hm : readLimbs (cacheState s out input constant) (out.add 40) = minus :=
    readLimbs_storeLimbs s₂ (out.add 40) minus (smallRange_add ho₂ (k := 40) (count := 40) (by decide))
  have hp₁ : readLimbs s₂ out = plus := readLimbs_storeLimbs s₁ out plus h0₁
  have hp₂ : readLimbs (cacheState s out input constant) out = readLimbs s₂ out :=
    readLimbs_storeLimbs_frame s₂ (out.add 40) out minus
      (smallRange_add ho₂ (k := 40) (count := 40) (by decide)) h0₂ (by simpa using hd 0 1 (by decide))
  have hz₀ : readLimbs s₀ (out.add 80) = readLimbs s (input.add 80) :=
    copyField_words s (out.add 80) (input.add 80)
      (smallRange_add ho (k := 80) (count := 40) (by decide))
      (smallRange_add hi (k := 80) (count := 40) (by decide))
  have hz₁ : readLimbs s₁ (out.add 80) = readLimbs s₀ (out.add 80) :=
    readLimbs_storeLimbs_frame s₀ (out.add 120) (out.add 80) t
      (smallRange_add ho₀ (k := 120) (count := 40) (by decide))
      (smallRange_add ho₀ (k := 80) (count := 40) (by decide)) (by simpa using hd 2 3 (by decide))
  have hz₂ : readLimbs s₂ (out.add 80) = readLimbs s₁ (out.add 80) :=
    readLimbs_storeLimbs_frame s₁ out (out.add 80) plus h0₁
      (smallRange_add ho₁ (k := 80) (count := 40) (by decide)) (by simpa using hd 2 0 (by decide))
  have hz₃ : readLimbs (cacheState s out input constant) (out.add 80) = readLimbs s₂ (out.add 80) :=
    readLimbs_storeLimbs_frame s₂ (out.add 40) (out.add 80) minus
      (smallRange_add ho₂ (k := 40) (count := 40) (by decide))
      (smallRange_add ho₂ (k := 80) (count := 40) (by decide)) (by simpa using hd 2 1 (by decide))
  have ht₁ : readLimbs s₁ (out.add 120) = t :=
    readLimbs_storeLimbs s₀ (out.add 120) t (smallRange_add ho₀ (k := 120) (count := 40) (by decide))
  have ht₂ : readLimbs s₂ (out.add 120) = readLimbs s₁ (out.add 120) :=
    readLimbs_storeLimbs_frame s₁ out (out.add 120) plus h0₁
      (smallRange_add ho₁ (k := 120) (count := 40) (by decide)) (by simpa using hd 3 0 (by decide))
  have ht₃ : readLimbs (cacheState s out input constant) (out.add 120) = readLimbs s₂ (out.add 120) :=
    readLimbs_storeLimbs_frame s₂ (out.add 40) (out.add 120) minus
      (smallRange_add ho₂ (k := 40) (count := 40) (by decide))
      (smallRange_add ho₂ (k := 120) (count := 40) (by decide)) (by simpa using hd 3 1 (by decide))
  exact ⟨hm, hp₂.trans hp₁, hz₃.trans (hz₂.trans (hz₁.trans hz₀)), ht₃.trans (ht₂.trans ht₁)⟩

theorem cacheState_readCached (g : SerialConstructor.Globals) (s : GlobalState)
    (out input : Pointer) (ho : SmallRange s.mem out 160) (hi : SmallRange s.mem input 160)
    (hg : SerialConstructorContext.GlobalsReady g s) (hP : PointTight (readPoint s input)) :
    readCached (cacheState s out input g.address0) out =
      SerialConstructorArithmetic.cache (readPoint s input) := by
  obtain ⟨hx, hy, hz, ht⟩ := cacheState_fields s out input g.address0 ho hi
  have hb := pointTight_bounded _ hP
  change Bounded (unsigned (readLimbs s input)) ∧
    Bounded (unsigned (readLimbs s (input.add 40))) ∧
    Bounded (unsigned (readLimbs s (input.add 80))) ∧
    Bounded (unsigned (readLimbs s (input.add 120))) at hb
  apply PointArithmetic.Extended.ext
  · exact (congrArg unsigned hx).trans (subWord_unsigned _ _ hb.2.1 hb.1)
  · exact (congrArg unsigned hy).trans (addWord_unsigned _ _ hb.1 hb.2.1)
  · exact congrArg unsigned hz
  · change unsigned (readLimbs (cacheState s out input g.address0) (out.add 120)) = _
    rw [ht, hg.words, machine_unsigned_mul _ _ hb.2.2.2 (tight_bounded _ serialD2_tight)]
    rfl


/-- The inline conversion preserves allocation shape and every byte outside
its 160-byte output, including the constructor's pinned global. -/
theorem cacheState_writesOnly (s : GlobalState) (out input constant : Pointer)
    (hwf : s.WF) (ho : SmallRange s.mem out 160) :
    WritesOnly out 160 s (cacheState s out input constant) := by
  refine ⟨?_, le_refl _, ?_, ?_⟩
  · simpa only [cacheState, storeLimbs, GlobalState.WF_storeAt] using hwf
  · intro id
    simp only [cacheState, storeLimbs_allocationShape, storeAt_allocationShape]
  · intro q bits hd
    have hchunk (k count : Nat) (hk : k + count ≤ 160) :
        (Range.of (out.add (BitVec.ofNat 64 k)) (8 * count)).Disjoint (Range.of q bits) := by
      have hoff := Pointer.offsetInBits_add (ho.no_wrap (k := k) (by omega))
      have hk64 : k < 2^64 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at hoff
      simp only [Range.Disjoint, Range.of, Pointer.add_id, hoff] at hd ⊢
      rcases hd with hne | hbefore | hafter
      · exact Or.inl (Ne.symm hne)
      · exact Or.inr (Or.inr (by omega))
      · exact Or.inr (Or.inl (by omega))
    unfold cacheState storeLimbs
    simp only [Pointer.add_add]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 72 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 64 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 56 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 48 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 40 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 32 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 24 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 16 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 8 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 0 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 152 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 144 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 136 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 128 8 (by decide))]
    erw [MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 120 8 (by decide))]
    exact MemoryState.readAt_storeAt_disjoint (by simpa using hchunk 80 40 (by decide)) _

/-- The initial source fragment has the full cache representation and frame,
with all field behavior discharged by the actual imported multiplication. -/
theorem phase_contract (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState) (out input : Pointer)
    (hwf : s.WF) (ho : SmallRange s.mem out 160) (hi : SmallRange s.mem input 160)
    (hg : SerialConstructorContext.GlobalsReady g s) (hne : out.id ≠ input.id)
    (harg : E.args 1 = .value input) (hP : PointTight (readPoint s input)) :
    let final := cacheState s out input g.address0
    (phase p g).runFrom (E[%35 := .value out]) ⟨0, by change 0 < 1; decide⟩ s =
      .value (.nil, final) ∧ WritesOnly out 160 s final ∧
      PointBounded (readCached final out) ∧
      pointValue (readCached final out) =
        PointArithmetic.serialCache _root_.Ed25519.d (pointValue (readPoint s input)) := by
  dsimp only
  refine ⟨phase_run p g E s out input hwf ho hi hg.buffer hne (hg.separate ho (by decide)) harg,
    cacheState_writesOnly s out input g.address0 hwf ho, ?_, ?_⟩
  · rw [cacheState_readCached g s out input ho hi hg hP]
    exact SerialConstructorArithmetic.cache_bounded _ hP
  · rw [cacheState_readCached g s out input ho hi hg hP]
    exact SerialConstructorArithmetic.cache_value _ hP

/-- The successor-cache source fragment establishes the same invariant. -/
theorem loopPhase_contract (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState) (out input : Pointer)
    (hwf : s.WF) (ho : SmallRange s.mem out 160) (hi : SmallRange s.mem input 160)
    (hg : SerialConstructorContext.GlobalsReady g s) (hne : out.id ≠ input.id)
    (hP : PointTight (readPoint s input)) :
    let final := cacheState s out input g.address0
    (loopPhase p g).runFrom (loopInput E out input) ⟨0, by change 0 < 1; decide⟩ s =
      .value (.nil, final) ∧ WritesOnly out 160 s final ∧
      PointBounded (readCached final out) ∧
      pointValue (readCached final out) =
        PointArithmetic.serialCache _root_.Ed25519.d (pointValue (readPoint s input)) := by
  dsimp only
  refine ⟨loopPhase_run p g E s out input hwf ho hi hg.buffer hne (hg.separate ho (by decide)),
    cacheState_writesOnly s out input g.address0 hwf ho, ?_, ?_⟩
  · rw [cacheState_readCached g s out input ho hi hg hP]
    exact SerialConstructorArithmetic.cache_bounded _ hP
  · rw [cacheState_readCached g s out input ho hi hg hP]
    exact SerialConstructorArithmetic.cache_value _ hP

end Agave.Ed25519.Tables.SerialCacheExecution
