import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekSerialBackendReady
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Concrete

/-! The concrete AVX2 backend needs only its loaded fixed table. Transport that
exact allocation through actual prefix calls; no arithmetic readiness is assumed. -/
namespace Agave.Ed25519.Verifier.Execution.Dalek.Avx2BackendReadiness
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open SerialBackendReadiness (noAvx LinkedPrefix)
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

abbrev Ready := DoubleBase.ExecutionAvx2.GlobalsReady

def ready (g : DoubleBase.Avx2CFG.Globals) : BackendReadyPredicate :=
  fun _ _ _ _ state => Ready g state

def Separate (g : DoubleBase.Avx2CFG.Globals) (out : Pointer) : Prop :=
  g.address2.id ≠ out.id

def GlobalShape (g : DoubleBase.Avx2CFG.Globals) (before after : GlobalState) : Prop :=
  (after.mem[g.address2.id]?).map MemoryBlock.length = (before.mem[g.address2.id]?).map MemoryBlock.length

theorem ready_output_of_globalShape (h : Ready g before) (hs : GlobalShape g before after)
    (hf : OutputFrame before after out bytes) (hd : Separate g out) : Ready g after := by
  have hb := AllocationShape.blockAt g.address2.id hs
    (fun w => hf.read ⟨g.address2.id, 0⟩ w (Range.disjoint_of_id_ne hd))
  exact ⟨h.baseAddress, hb.trans h.basePresent⟩

theorem ready_output (h : Ready g before) (hs : AllocationShape before after)
    (hf : OutputFrame before after out bytes) (hd : Separate g out) : Ready g after :=
  ready_output_of_globalShape h (hs g.address2.id) hf hd

theorem ready_readOnly (h : Ready g before) (hs : AllocationShape before after)
    (hf : ReadOnlyFrame before after) : Ready g after :=
  ⟨h.baseAddress, (hs.readOnlyBlock hf _).trans h.basePresent⟩

private theorem ready_point (h : Ready g before) (hs : AllocationShape before after)
    (hf : PointCheckFrame before after z)
    (hd : ∀ ptr ∈ pointDestinations z, Separate g ptr) : Ready g after := by
  have hb : after.mem[g.address2.id]? = before.mem[g.address2.id]? := by
    apply hs.block
    intro width
    apply hf.read ⟨g.address2.id, 0⟩ width
    · exact Range.disjoint_of_id_ne (hd z.slot29 (by simp [pointDestinations]))
    · exact Range.disjoint_of_id_ne (hd z.slot30 (by simp [pointDestinations]))
    · exact Range.disjoint_of_id_ne (hd z.point (by simp [pointDestinations]))
    · exact Range.disjoint_of_id_ne (hd z.cofactor (by simp [pointDestinations]))
    · exact Range.disjoint_of_id_ne (hd z.identity (by simp [pointDestinations]))
  exact ⟨h.baseAddress, hb.trans h.basePresent⟩

theorem cacheReady (p : Primitives) (hardware : Avx2Cache.Instructions.HardwareInstructions)
    (laws : Avx2Cache.Instructions.InstructionContracts hardware)
    (q : TailPointers) (hlink : LinkedPrefix p hardware q.cache)
    (g : DoubleBase.Avx2CFG.Globals)
    (state : GlobalState) (hwf : state.WF) (hcache : SmallRange state.mem q.cache 1)
    (hready : Ready g state) (hd : Separate g q.cache) :
    CacheBackendsReady p noAvx (ready g) q state := by
  refine ⟨⟨True.intro, hready⟩, ?_⟩
  intro after returned hcall hf
  rw [hlink.cacheCall] at hcall
  exact ⟨True.intro, ready_output hready (cache_allocationShape hardware laws q.cache state after returned hwf hcache hcall) hf hd⟩

theorem scalarReady (p : Primitives) (hardware : Avx2Cache.Instructions.HardwareInstructions)
    (laws : Avx2Cache.Instructions.InstructionContracts hardware)
    (q : TailPointers) (scratch : Pointer) (hlink : LinkedPrefix p hardware q.cache)
    (g : DoubleBase.Avx2CFG.Globals)
    (state : GlobalState) (bytes : Bytes32) (hwf : state.WF)
    (hsig : SmallRange state.mem q.signature 64) (hsc : SmallRange state.mem q.scalar 32)
    (hout : SmallRange state.mem scratch 32) (hcache : SmallRange state.mem q.cache 1)
    (hready : Ready g state)
    (hdScratch : Separate g scratch) (hdScalar : Separate g q.scalar)
    (hdCache : Separate g q.cache) :
    ScalarBackendsReady p noAvx (ready g) q scratch state bytes := by
  intro checked htrace hf
  have hs := scalarTrace_allocationShape p q.signature scratch state checked
    hlink.black hlink.scalar hlink.bytesEq hwf hsig hout htrace
  have hr := ready_output hready hs hf hdScratch
  have hcopy := scalar_copy_frame checked q.signature q.scalar (bytes.extractLsb' 0 8)
    hf.wellFormed (hf.live _ _ hsc)
  have hcopyReady := ready_output hr (AllocationShape.scalarCopy checked _ _ _) hcopy hdScalar
  exact cacheReady p hardware laws q hlink g _ hcopy.wellFormed
    (hcopy.live _ _ (hf.live _ _ hcache)) hcopyReady hdCache

/-- Range-only version: no semantic point/scalar assumptions enter readiness. -/
theorem bodyReady_of_ranges (p : Primitives) (hardware : Avx2Cache.Instructions.HardwareInstructions)
    (laws : Avx2Cache.Instructions.InstructionContracts hardware)
    (q : TailPointers) (z : PointPointers) (scratch : Pointer) (hlink : LinkedPrefix p hardware q.cache)
    (g : DoubleBase.Avx2CFG.Globals)
    (state : GlobalState) (bytes : Bytes32) (_hwf : state.WF)
    (hsig : SmallRange state.mem q.signature 64) (hsc : SmallRange state.mem q.scalar 32)
    (hout : SmallRange state.mem scratch 32) (hcache : SmallRange state.mem q.cache 1)
    (hp : SmallRange state.mem z.point 160) (hc : SmallRange state.mem z.cofactor 160)
    (hi : SmallRange state.mem z.identity 160) (hready : Ready g state)
    (hdOption : Separate g z.option)
    (hdPoint : ∀ ptr ∈ pointDestinations z, Separate g ptr)
    (hdScratch : Separate g scratch) (hdScalar : Separate g q.scalar)
    (hdCache : Separate g q.cache)
    (hdecodeShape : ∀ decoded, p.decompress (args2 z.option q.signature) state = .value (.nil, decoded) →
      GlobalShape g state decoded) :
    BodyBackendsReady p noAvx (ready g) q z scratch state bytes := by
  intro decoded hcall hf checked htrace hpframe
  have hdReady := ready_output_of_globalShape hready (hdecodeShape decoded hcall) hf hdOption
  have hs := pointTrace_allocationShape p z decoded checked hlink.cofactor hlink.pointEq
    hf.wellFormed (hf.live _ _ hp) (hf.live _ _ hc) (hf.live _ _ hi) htrace
  have hcReady := ready_point hdReady hs hpframe hdPoint
  exact scalarReady p hardware laws q scratch hlink g checked bytes hpframe.wellFormed
    (hpframe.live _ _ (hf.live _ _ hsig)) (hpframe.live _ _ (hf.live _ _ hsc))
    (hpframe.live _ _ (hf.live _ _ hout)) (hpframe.live _ _ (hf.live _ _ hcache))
    hcReady hdScratch hdScalar hdCache

end Agave.Ed25519.Verifier.Execution.Dalek.Avx2BackendReadiness
