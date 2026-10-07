import SSA.Projects.Agave.Ed25519.Bridge.CrossClientAvx2Prefix
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionColdUnder

/-! Concrete AVX2 table readiness through the real cold verifier prefix.
Only that table's allocation length at challenge and R-decode remains explicit. -/
namespace Agave.Ed25519.Verifier.Execution.Dalek.Avx2BackendReadiness
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open SerialBackendReadiness (noAvx LinkedPrefix)
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

private theorem ready_stack (g : DoubleBase.Avx2CFG.Globals)
    (initial : GlobalState) (hwf : initial.WF) (hr : Ready g initial) (n : Nat) :
    Ready g (stackState initial n) := by
  induction n with
  | zero => exact hr
  | succ n ih => exact ⟨ih.baseAddress, ih.basePresent.alloca (stackState_wf initial hwf n)⟩

private theorem separate_stack (g : DoubleBase.Avx2CFG.Globals)
    (initial : GlobalState) (hwf : initial.WF) (hr : Ready g initial) (n : Nat) :
    Separate g (stackSlot initial n) := by
  have hlt := hwf.lt hr.basePresent.fits.mem
  simp only [ByteGlobal.address] at hlt
  intro heq
  have he := congrArg BlockId.id heq
  simp only [stackSlot_id] at he
  omega

private theorem ready_challenge
    (g : DoubleBase.Avx2CFG.Globals) (scg : SHA512Finalization.CompressionGlobals)
    (hr : Ready g before) (hs : GlobalShape g before after)
    (hf : SHA512Finalization.CacheAwareOutputFrame scg before after out bytes)
    (hd : Separate g out) (hc : g.address2.id ≠ scg.cache) : Ready g after := by
  have hb := AllocationShape.blockAt g.address2.id hs
    (fun w => hf.read ⟨g.address2.id, 0⟩ w hc (Range.disjoint_of_id_ne hd))
  exact ⟨hr.baseAddress, hb.trans hr.basePresent⟩

/-- Only allocation shape at the concrete prefix invocations is conditional.
No callee termination or arithmetic-result equation is assumed by this package. -/
structure ShapeAt (p : Primitives) (g : DoubleBase.Avx2CFG.Globals) (initial : GlobalState) (key signature message : Pointer)
    (length : Nat) : Prop where
  challenge : ∀ challenged,
    p.challengeScalar (.cons (.value (stackSlot initial 12)) (.cons (.value key)
      (.cons (.value signature) (.cons (.value message) (.cons (.value (BitVec.ofNat 64 length)) .nil)))))
      (allocated initial) = .value (.nil, challenged) →
    GlobalShape g (allocated initial) challenged
  decoder : ∀ challenged multiplied compared,
    ColdCallTrace p initial key signature message length challenged multiplied compared →
    ∀ decoded, p.decompress (args2 (stackSlot initial 8) signature) compared = .value (.nil, decoded) →
    GlobalShape g compared decoded

/-- AVX2 backend readiness is derived from initial loaded globals, ordinary
range/separation data, and the two explicit residual allocation-shape facts. -/
theorem coldReady (p : Primitives) (hardware : Avx2Cache.Instructions.HardwareInstructions)
    (laws : Avx2Cache.Instructions.InstructionContracts hardware)
    (dg : Globals) (hlink : LinkedPrefix p hardware dg.address1)
    (g : DoubleBase.Avx2CFG.Globals)
    (scg : SHA512Finalization.CompressionGlobals)
    (initial : GlobalState) (key signature message : Pointer) (length : Nat) (bytes : Bytes32)
    (hwf : initial.WF) (hkey : SmallRange initial.mem key 192)
    (hsig : SmallRange initial.mem signature 64) (hcache : SmallRange initial.mem dg.address1 1)
    (hready : Ready g initial)
    (hsepCache : Separate g dg.address1)
    (hsepSha : g.address2.id ≠ scg.cache)
    (hstackCache : ∀ i, (stackSlot initial i).id ≠ scg.cache)
    (hkeyCache : key.id ≠ scg.cache) (hsigCache : signature.id ≠ scg.cache)
    (hcacheCache : dg.address1.id ≠ scg.cache)
    (hshape : ShapeAt p g initial key signature message length) :
    ColdBackendsReady p noAvx (ready g) scg dg
      initial key signature message length bytes := by
  intro challenged multiplied compared htrace hc hm he
  have hr0 := ready_stack g initial hwf hready 13
  have hcShape := hshape.challenge challenged htrace.1
  have hrc := ready_challenge g scg hr0 hcShape hc (separate_stack g initial hwf hready 12) hsepSha
  have hinput : SmallRange challenged.mem (key.add 32#64) 120 := by
    apply hc.live _ _ (by simpa using hkeyCache)
    exact stackState_live initial hwf 13 (smallRange_add hkey (k := 32) (count := 120) (by decide))
  have hout : SmallRange challenged.mem (stackSlot initial 4) 160 :=
    hc.live _ _ (hstackCache 4) (stackSlot_live initial hwf 4 13 (by decide))
  have hmcall := htrace.2.1
  rw [hlink.cofactor] at hmcall
  have hmShape := cofactor_allocationShape (stackSlot initial 4) (key.add 32#64)
    challenged multiplied hc.wellFormed hout hinput hmcall
  have hrm := ready_output hrc hmShape hm (separate_stack g initial hwf hready 4)
  have hid : SmallRange multiplied.mem (stackSlot initial 3) 160 :=
    hm.live _ _ (hc.live _ _ (hstackCache 3) (stackSlot_live initial hwf 3 13 (by decide)))
  have hif := identity_frame multiplied (stackSlot initial 3) hm.wellFormed hid
  have hri := ready_output hrm (AllocationShape.identityStores _ _) hif
    (separate_stack g initial hwf hready 3)
  obtain ⟨returned, hecall⟩ := htrace.2.2
  rw [hlink.pointEq] at hecall
  have heShape := pointEq_allocationShape (stackSlot initial 4) (stackSlot initial 3)
    _ compared returned hif.wellFormed (hif.live _ _ (hm.live _ _ hout)) (hif.live _ _ hid) hecall
  have hreadyCompared := ready_readOnly hri heShape he
  have hstack (i : Nat) (hi : i < 13) := cold_entry_stack_live scg initial challenged multiplied compared
    hwf hc hm he hstackCache i hi
  have hsigCompared : SmallRange compared.mem signature 64 :=
    he.live _ _ (hif.live _ _ (hm.live _ _ (hc.live _ _ hsigCache (stackState_live initial hwf 13 hsig))))
  have hcacheCompared : SmallRange compared.mem dg.address1 1 :=
    he.live _ _ (hif.live _ _ (hm.live _ _ (hc.live _ _ hcacheCache (stackState_live initial hwf 13 hcache))))
  refine bodyReady_of_ranges p hardware laws (entryTailPointers initial key signature dg)
    (entryPointPointers initial dg) (stackSlot initial 0) hlink g compared bytes he.wellFormed
    hsigCompared (hstack 7 (by decide)) (hstack 0 (by decide)) hcacheCompared
    (hstack 11 (by decide)) (hstack 2 (by decide)) (hstack 1 (by decide)) hreadyCompared
    (separate_stack g initial hwf hready 8) ?_
    (separate_stack g initial hwf hready 0) (separate_stack g initial hwf hready 7) hsepCache ?_
  · intro ptr hp
    simp only [pointDestinations, entryPointPointers, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact separate_stack g initial hwf hready _
  · exact hshape.decoder challenged multiplied compared htrace

end Agave.Ed25519.Verifier.Execution.Dalek.Avx2BackendReadiness
