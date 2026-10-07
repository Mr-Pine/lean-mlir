import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekColdReady

/-! Only the SHA dispatch allocation may differ. Each read needed by the
existing verifier body is transported through its own separated range. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

theorem cold_entry_stack_live (cg : SHA512Finalization.CompressionGlobals) (initial challenged multiplied compared : GlobalState)
    (hwf : initial.WF)
    (hc : SHA512Finalization.CacheAwareOutputFrame cg (allocated initial) challenged (stackSlot initial 12) 32)
    (hm : OutputFrame challenged multiplied (stackSlot initial 4) 160)
    (he : ReadOnlyFrame (identityStoreState multiplied (stackSlot initial 3)) compared)
    (hstackCache : ∀ i, (stackSlot initial i).id ≠ cg.cache)
    (i : Nat) (hi : i < 13) :
    SmallRange compared.mem (stackSlot initial i) (stackBytes i) := by
  apply he.live
  exact ((((hm.live _ _ (hc.live _ _ (hstackCache i) (stackSlot_live initial hwf i 13 hi))).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _

/-- Input bytes are preserved whenever their
range is disjoint from each entry output. No validity of those bytes is required. -/
theorem cold_entry_readBytes (cg : SHA512Finalization.CompressionGlobals) (initial challenged multiplied compared : GlobalState)
    (hc : SHA512Finalization.CacheAwareOutputFrame cg (allocated initial) challenged (stackSlot initial 12) 32)
    (hm : OutputFrame challenged multiplied (stackSlot initial 4) 160)
    (he : ReadOnlyFrame (identityStoreState multiplied (stackSlot initial 3)) compared)
    (hid : SmallRange multiplied.mem (stackSlot initial 3) 160)
    (q : Pointer) (count : Nat) (value : BitVec (8 * count))
    (hq : q.id ≠ cg.cache)
    (hr : ReadBytes (allocated initial) q count value)
    (hdc : (Range.of q (8 * count)).Disjoint (Range.of (stackSlot initial 12) 256))
    (hdm : (Range.of q (8 * count)).Disjoint (Range.of (stackSlot initial 4) 1280))
    (hdi : (Range.of q (8 * count)).Disjoint (Range.of (stackSlot initial 3) 1280)) :
    ReadBytes compared q count value := by
  have h1 := hc.readBytes q count value hr hq hdc
  have h2 := hm.readBytes _ _ _ _ _ _ _ h1 hdm
  have hf := identity_frame multiplied (stackSlot initial 3) hm.wellFormed hid
  exact he.readBytes _ _ _ _ _ (hf.readBytes _ _ _ _ _ _ _ h2 hdi)

theorem cold_entry_body_memory {Point Scalar Result : Type}
    (cg : SHA512Finalization.CompressionGlobals)
    (initial challenged multiplied compared : GlobalState) (hwf : initial.WF)
    (key signature : Pointer) (g : Globals) (layout : Layout Point Scalar Result)
    (h : Scalar) (a : Point) (r bytes : Bytes32)
    (hc : SHA512Finalization.CacheAwareOutputFrame cg (allocated initial) challenged (stackSlot initial 12) 32)
    (hchallenge : ReadBytes challenged (stackSlot initial 12) 32 (layout.scalar h))
    (hm : OutputFrame challenged multiplied (stackSlot initial 4) 160)
    (he : ReadOnlyFrame (identityStoreState multiplied (stackSlot initial 3)) compared)
    (hkey : ReadBytes initial (key.add 32#64) 160 (layout.point a))
    (hsig : SmallRange initial.mem signature 64)
    (hr : ReadBytes initial signature 32 r)
    (hs : ReadBytes initial (signature.add 32#64) 32 bytes)
    (hone : ReadBytes initial g.address0 40 (1#320))
    (hcache : SmallRange initial.mem g.address1 1)
    (hstackCache : ∀ i, (stackSlot initial i).id ≠ cg.cache)
    (hkeyCache : key.id ≠ cg.cache) (hsigCache : signature.id ≠ cg.cache)
    (honeCache : g.address0.id ≠ cg.cache) (hcacheCache : g.address1.id ≠ cg.cache) :
    BodyMemory (entryTailPointers initial key signature g) (entryPointPointers initial g)
      (stackSlot initial 0) compared layout h a r bytes := by
  have hstack (i : Nat) (hi : i < 13) := cold_entry_stack_live cg initial challenged multiplied compared
    hwf hc hm he hstackCache i hi
  have hid : SmallRange multiplied.mem (stackSlot initial 3) 160 :=
    hm.live _ _ (hc.live _ _ (hstackCache 3) (stackSlot_live initial hwf 3 13 (by decide)))
  have hcaller {ptr : Pointer} {n : Nat} {value : BitVec (8 * n)}
      (hv : ReadBytes initial ptr n value) (hpc : ptr.id ≠ cg.cache) : ReadBytes compared ptr n value := by
    apply cold_entry_readBytes cg initial challenged multiplied compared hc hm he hid ptr n value hpc
      (stackState_readBytes initial hwf 13 hv)
    · exact (stackSlot_disjoint_caller initial hwf 12 hv.1 256 (8 * n)).symm
    · exact (stackSlot_disjoint_caller initial hwf 4 hv.1 1280 (8 * n)).symm
    · exact (stackSlot_disjoint_caller initial hwf 3 hv.1 1280 (8 * n)).symm
  have hlive {ptr : Pointer} {n : Nat} (hv : SmallRange initial.mem ptr n) (hpc : ptr.id ≠ cg.cache) :
      SmallRange compared.mem ptr n := by
    apply he.live ptr n
    exact ((((hm.live ptr n (hc.live ptr n hpc (stackState_live initial hwf 13 hv))).storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _
  have hfidentity := identity_frame multiplied (stackSlot initial 3) hm.wellFormed hid
  have hchallengeFinal : ReadBytes compared (stackSlot initial 12) 32 (layout.scalar h) := by
    have hcm := OutputFrame.readBytes challenged multiplied (stackSlot initial 4) (stackSlot initial 12)
      160 32 (layout.scalar h) hm hchallenge (stackSlot_disjoint initial 12 4 (by decide) 256 1280)
    have hci := OutputFrame.readBytes multiplied (identityStoreState multiplied (stackSlot initial 3))
      (stackSlot initial 3) (stackSlot initial 12) 160 32 (layout.scalar h) hfidentity hcm
      (stackSlot_disjoint initial 12 3 (by decide) 256 1280)
    exact ReadOnlyFrame.readBytes _ _ _ _ _ he hci
  refine ⟨?_, hlive hsig hsigCache, hcaller hs (by simpa [entryTailPointers] using hsigCache), ?_, hlive hcache hcacheCache, ?_, ?_, ?_, ?_, ?_, ?_, hcaller hone honeCache⟩
  · refine ⟨he.wellFormed, ?_, ?_, hchallengeFinal, hcaller hkey (by simpa [entryTailPointers] using hkeyCache), ?_, hcaller hr hsigCache,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hstack 5 (by decide)
    · exact hstack 6 (by decide)
    · exact hstack 7 (by decide)
    · exact stackSlot_disjoint initial 5 12 (by decide) 1280 256
    · exact stackSlot_disjoint_caller initial hwf 5 hkey.1 1280 1280
    · exact stackSlot_disjoint initial 5 7 (by decide) 1280 256
    · exact (stackSlot_disjoint_caller initial hwf 5 hr.1 1280 256).symm
    · exact stackSlot_disjoint initial 6 5 (by decide) 256 1280
    · exact (stackSlot_disjoint_caller initial hwf 6 hr.1 256 256).symm
    · exact stackSlot_disjoint initial 12 7 (by decide) 256 256
    · exact (stackSlot_disjoint_caller initial hwf 7 hkey.1 256 1280).symm
    · exact (stackSlot_disjoint_caller initial hwf 7 hr.1 256 256).symm
  all_goals first
    | exact hstack 0 (by decide)
    | exact hstack 8 (by decide)
    | exact hstack 9 (by decide)
    | exact hstack 10 (by decide)
    | exact hstack 11 (by decide)
    | exact hstack 2 (by decide)
    | exact hstack 1 (by decide)

theorem cold_entry_decoder_ready
    (cg : SHA512Finalization.CompressionGlobals)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (initial challenged multiplied compared : GlobalState) (hwf : initial.WF)
    (hc : SHA512Finalization.CacheAwareOutputFrame cg (allocated initial) challenged (stackSlot initial 12) 32)
    (hm : OutputFrame challenged multiplied (stackSlot initial 4) 160)
    (he : ReadOnlyFrame (identityStoreState multiplied (stackSlot initial 3)) compared)
    (hready : Encoding.Decompress.Execution.Ready ddg dsg initial)
    (hstackCache : (stackSlot initial 3).id ≠ cg.cache)
    (hd : ddg.address0.id ≠ cg.cache) (hi : dsg.address0.id ≠ cg.cache) :
    Encoding.Decompress.Execution.Ready ddg dsg compared := by
  have hid : SmallRange multiplied.mem (stackSlot initial 3) 160 :=
    hm.live _ _ (hc.live _ _ hstackCache (stackSlot_live initial hwf 3 13 (by decide)))
  have hcaller {ptr : Pointer} {n : Nat} {value : BitVec (8 * n)}
      (hv : ReadBytes initial ptr n value) (hpc : ptr.id ≠ cg.cache) : ReadBytes compared ptr n value := by
    apply cold_entry_readBytes cg initial challenged multiplied compared hc hm he hid ptr n value hpc
      (stackState_readBytes initial hwf 13 hv)
    · exact (stackSlot_disjoint_caller initial hwf 12 hv.1 256 (8 * n)).symm
    · exact (stackSlot_disjoint_caller initial hwf 4 hv.1 1280 (8 * n)).symm
    · exact (stackSlot_disjoint_caller initial hwf 3 hv.1 1280 (8 * n)).symm
  exact ⟨hcaller hready.curveD hd, hcaller hready.sqrtM1 hi⟩

end Agave.Ed25519.Verifier.Execution.Dalek
