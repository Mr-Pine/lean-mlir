import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekSerialBackendReady
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionColdUnder

/-! Initial serial globals imply readiness at the actual backend call. The
only structural premises left concern allocation shape of this invocation's
linked challenge and R decoder, whose byte frames alone do not imply shape. -/
namespace Agave.Ed25519.Verifier.Execution.Dalek.SerialBackendReadiness
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

private theorem ready_stack (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (initial : GlobalState) (hwf : initial.WF) (hr : Ready g d2 initial) (n : Nat) :
    Ready g d2 (stackState initial n) := by
  induction n with
  | zero => exact hr
  | succ n ih =>
      exact ⟨⟨ih.1.identityOffset, ih.1.identity.alloca (stackState_wf initial hwf n),
        ih.1.baseOffset, ih.1.base.alloca (stackState_wf initial hwf n)⟩,
        ih.2.alloca (stackState_wf initial hwf n)⟩

private theorem separate_stack (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (initial : GlobalState) (hwf : initial.WF) (hr : Ready g d2 initial) (n : Nat) :
    Separate g d2 (stackSlot initial n) := by
  have hne {bg : ByteGlobal} {id : BlockId} (hp : bg.Present id initial.mem) :
      id ≠ (stackSlot initial n).id := by
    have hlt := hwf.lt hp.fits.mem
    simp only [ByteGlobal.address] at hlt
    intro heq
    have he := congrArg BlockId.id heq
    simp only [stackSlot_id] at he
    omega
  exact ⟨hne hr.1.identity, hne hr.1.base, hne hr.2.present⟩

private theorem ready_challenge
    (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (scg : SHA512Finalization.CompressionGlobals)
    (hr : Ready g d2 before) (hs : GlobalShape g d2 before after)
    (hf : SHA512Finalization.CacheAwareOutputFrame scg before after out bytes)
    (hd : Separate g d2 out)
    (hc : g.address0.id ≠ scg.cache ∧ g.address3.id ≠ scg.cache ∧ d2.address0.id ≠ scg.cache) :
    Ready g d2 after := by
  have hb (q : Pointer)
      (hq : (after.mem[q.id]?).map MemoryBlock.length = (before.mem[q.id]?).map MemoryBlock.length)
      (hqc : q.id ≠ scg.cache) (hqo : q.id ≠ out.id) :
      after.mem[q.id]? = before.mem[q.id]? :=
    AllocationShape.blockAt q.id hq (fun w => hf.read ⟨q.id, 0⟩ w hqc (Range.disjoint_of_id_ne hqo))
  exact ⟨⟨hr.1.identityOffset, (hb _ hs.1 hc.1 hd.1).trans hr.1.identity,
    hr.1.baseOffset, (hb _ hs.2.1 hc.2.1 hd.2.1).trans hr.1.base⟩,
    ⟨hr.2.offsetZero, (hb _ hs.2.2 hc.2.2 hd.2.2).trans hr.2.present⟩⟩

/-- Only allocation shape at the concrete prefix invocations is conditional.
No callee termination or arithmetic-result equation is assumed by this package. -/
structure ShapeAt (p : Primitives) (g : DoubleBase.SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (initial : GlobalState) (key signature message : Pointer)
    (length : Nat) : Prop where
  challenge : ∀ challenged,
    p.challengeScalar (.cons (.value (stackSlot initial 12)) (.cons (.value key)
      (.cons (.value signature) (.cons (.value message) (.cons (.value (BitVec.ofNat 64 length)) .nil)))))
      (allocated initial) = .value (.nil, challenged) →
    GlobalShape g d2 (allocated initial) challenged
  decoder : ∀ challenged multiplied compared,
    ColdCallTrace p initial key signature message length challenged multiplied compared →
    ∀ decoded, p.decompress (args2 (stackSlot initial 8) signature) compared = .value (.nil, decoded) →
    GlobalShape g d2 compared decoded

/-- Serial backend readiness is derived from initial loaded globals, ordinary
range/separation data, and the two explicit residual allocation-shape facts. -/
theorem coldReady (p : Primitives) (hardware : Avx2Cache.Instructions.HardwareInstructions)
    (laws : Avx2Cache.Instructions.InstructionContracts hardware)
    (dg : Globals) (hlink : LinkedPrefix p hardware dg.address1)
    (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (scg : SHA512Finalization.CompressionGlobals)
    (initial : GlobalState) (key signature message : Pointer) (length : Nat) (bytes : Bytes32)
    (hwf : initial.WF) (hkey : SmallRange initial.mem key 192)
    (hsig : SmallRange initial.mem signature 64) (hcache : SmallRange initial.mem dg.address1 1)
    (hready : Ready g d2 initial)
    (hsepCache : Separate g d2 dg.address1)
    (hsepSha : g.address0.id ≠ scg.cache ∧ g.address3.id ≠ scg.cache ∧ d2.address0.id ≠ scg.cache)
    (hstackCache : ∀ i, (stackSlot initial i).id ≠ scg.cache)
    (hkeyCache : key.id ≠ scg.cache) (hsigCache : signature.id ≠ scg.cache)
    (hcacheCache : dg.address1.id ≠ scg.cache)
    (hshape : ShapeAt p g d2 initial key signature message length) :
    ColdBackendsReady p (DoubleBase.RIR.serialLinkedReady g d2) noAvx scg dg
      initial key signature message length bytes := by
  intro challenged multiplied compared htrace hc hm he
  have hr0 := ready_stack g d2 initial hwf hready 13
  have hcShape := hshape.challenge challenged htrace.1
  have hrc := ready_challenge g d2 scg hr0 hcShape hc (separate_stack g d2 initial hwf hready 12) hsepSha
  have hinput : SmallRange challenged.mem (key.add 32#64) 120 := by
    apply hc.live _ _ (by simpa using hkeyCache)
    exact stackState_live initial hwf 13 (smallRange_add hkey (k := 32) (count := 120) (by decide))
  have hout : SmallRange challenged.mem (stackSlot initial 4) 160 :=
    hc.live _ _ (hstackCache 4) (stackSlot_live initial hwf 4 13 (by decide))
  have hmcall := htrace.2.1
  rw [hlink.cofactor] at hmcall
  have hmShape := cofactor_allocationShape (stackSlot initial 4) (key.add 32#64)
    challenged multiplied hc.wellFormed hout hinput hmcall
  have hrm := serialGlobals_output g d2 hrc.1 hrc.2 hmShape hm
    (separate_stack g d2 initial hwf hready 4).1
    (separate_stack g d2 initial hwf hready 4).2.1
    (separate_stack g d2 initial hwf hready 4).2.2
  have hid : SmallRange multiplied.mem (stackSlot initial 3) 160 :=
    hm.live _ _ (hc.live _ _ (hstackCache 3) (stackSlot_live initial hwf 3 13 (by decide)))
  have hif := identity_frame multiplied (stackSlot initial 3) hm.wellFormed hid
  have hri := serialGlobals_output g d2 hrm.1 hrm.2 (AllocationShape.identityStores _ _) hif
    (separate_stack g d2 initial hwf hready 3).1
    (separate_stack g d2 initial hwf hready 3).2.1
    (separate_stack g d2 initial hwf hready 3).2.2
  obtain ⟨returned, hecall⟩ := htrace.2.2
  rw [hlink.pointEq] at hecall
  have heShape := pointEq_allocationShape (stackSlot initial 4) (stackSlot initial 3)
    _ compared returned hif.wellFormed (hif.live _ _ (hm.live _ _ hout)) (hif.live _ _ hid) hecall
  have hreadyCompared := serialGlobals_readOnly g d2 hri.1 hri.2 heShape he
  have hstack (i : Nat) (hi : i < 13) := cold_entry_stack_live scg initial challenged multiplied compared
    hwf hc hm he hstackCache i hi
  have hsigCompared : SmallRange compared.mem signature 64 :=
    he.live _ _ (hif.live _ _ (hm.live _ _ (hc.live _ _ hsigCache (stackState_live initial hwf 13 hsig))))
  have hcacheCompared : SmallRange compared.mem dg.address1 1 :=
    he.live _ _ (hif.live _ _ (hm.live _ _ (hc.live _ _ hcacheCache (stackState_live initial hwf 13 hcache))))
  refine bodyReady_of_ranges p hardware laws (entryTailPointers initial key signature dg)
    (entryPointPointers initial dg) (stackSlot initial 0) hlink g d2 compared bytes he.wellFormed
    hsigCompared (hstack 7 (by decide)) (hstack 0 (by decide)) hcacheCompared
    (hstack 11 (by decide)) (hstack 2 (by decide)) (hstack 1 (by decide)) hreadyCompared
    (separate_stack g d2 initial hwf hready 8) ?_
    (separate_stack g d2 initial hwf hready 0) (separate_stack g d2 initial hwf hready 7) hsepCache ?_
  · intro ptr hp
    simp only [pointDestinations, entryPointPointers, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact separate_stack g d2 initial hwf hready _
  · exact hshape.decoder challenged multiplied compared htrace

end Agave.Ed25519.Verifier.Execution.Dalek.SerialBackendReadiness
