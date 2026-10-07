import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekTraceAllocationShape
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekSerialGlobalTransport
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContractsUnder

/-! Derive serial backend readiness from loaded globals and concrete prefix
calls. Only decoder allocation shape is conditional at the body boundary. -/
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace SerialBackendReadiness

def noAvx : BackendReadyPredicate := fun _ _ _ _ _ => True

abbrev Ready (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (state : GlobalState) :=
  DoubleBase.SerialContracts.GlobalsReady g state ∧ Tables.SerialConstructorContext.GlobalsReady d2 state

def Separate (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (out : Pointer) : Prop :=
  g.address0.id ≠ out.id ∧ g.address3.id ≠ out.id ∧ d2.address0.id ≠ out.id

/-- Only the three immutable serial allocation lengths are needed. -/
def GlobalShape (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (before after : GlobalState) : Prop :=
  (after.mem[g.address0.id]?).map MemoryBlock.length = (before.mem[g.address0.id]?).map MemoryBlock.length ∧
  (after.mem[g.address3.id]?).map MemoryBlock.length = (before.mem[g.address3.id]?).map MemoryBlock.length ∧
  (after.mem[d2.address0.id]?).map MemoryBlock.length = (before.mem[d2.address0.id]?).map MemoryBlock.length

private theorem ready_output_of_globalShape (h : Ready g d2 before) (hs : GlobalShape g d2 before after)
    (hf : OutputFrame before after out bytes) (hd : Separate g d2 out) : Ready g d2 after := by
  have hi := AllocationShape.blockAt g.address0.id hs.1
    (fun w => hf.read ⟨g.address0.id, 0⟩ w (Range.disjoint_of_id_ne hd.1))
  have hb := AllocationShape.blockAt g.address3.id hs.2.1
    (fun w => hf.read ⟨g.address3.id, 0⟩ w (Range.disjoint_of_id_ne hd.2.1))
  have hc := AllocationShape.blockAt d2.address0.id hs.2.2
    (fun w => hf.read ⟨d2.address0.id, 0⟩ w (Range.disjoint_of_id_ne hd.2.2))
  exact ⟨⟨h.1.identityOffset, hi.trans h.1.identity, h.1.baseOffset, hb.trans h.1.base⟩,
    ⟨h.2.offsetZero, hc.trans h.2.present⟩⟩

/-- Concrete linkage, independently of values and execution correctness. -/
structure LinkedPrefix (p : Primitives) (hardware : Avx2Cache.Instructions.HardwareInstructions)
    (cache : Pointer) : Prop where
  cofactor : p.pointMulByPow2 = SmallOrder.Execution.cofactorProgram.call
  pointEq : p.pointConstantTimeEq = SmallOrder.Execution.equalityProgram.call
  black : p.blackBoxByte = Encoding.Decompress.Execution.BlackBox.program.call
  scalar : p.scalarReduce = ScalarReduce32.Execution.program.call
  bytesEq : p.bytesConstantTimeEq = (Encoding.Decompress.Execution.BytesEq.program
    Encoding.Decompress.Execution.bytesEqPrimitives).call
  cacheCall : p.initializeAvx2Cache = (Avx2Cache.Instructions.initializer hardware.link cache).call

private theorem ready_output (h : Ready g d2 before) (hs : AllocationShape before after)
    (hf : OutputFrame before after out bytes) (hd : Separate g d2 out) : Ready g d2 after :=
  serialGlobals_output g d2 h.1 h.2 hs hf hd.1 hd.2.1 hd.2.2

private theorem ready_point (h : Ready g d2 before) (hs : AllocationShape before after)
    (hf : PointCheckFrame before after z)
    (hd : ∀ ptr ∈ pointDestinations z, Separate g d2 ptr) : Ready g d2 after := by
  have hb (q : Pointer) (hne : ∀ ptr ∈ pointDestinations z, q.id ≠ ptr.id) :
      after.mem[q.id]? = before.mem[q.id]? := by
    apply hs.block
    intro width
    apply hf.read ⟨q.id, 0⟩ width
    · exact Range.disjoint_of_id_ne (hne z.slot29 (by simp [pointDestinations]))
    · exact Range.disjoint_of_id_ne (hne z.slot30 (by simp [pointDestinations]))
    · exact Range.disjoint_of_id_ne (hne z.point (by simp [pointDestinations]))
    · exact Range.disjoint_of_id_ne (hne z.cofactor (by simp [pointDestinations]))
    · exact Range.disjoint_of_id_ne (hne z.identity (by simp [pointDestinations]))
  exact ⟨⟨h.1.identityOffset, (hb g.address0 (fun q hq => (hd q hq).1)).trans h.1.identity,
    h.1.baseOffset, (hb g.address3 (fun q hq => (hd q hq).2.1)).trans h.1.base⟩,
    ⟨h.2.offsetZero, (hb d2.address0 (fun q hq => (hd q hq).2.2)).trans h.2.present⟩⟩

theorem cacheReady (p : Primitives) (hardware : Avx2Cache.Instructions.HardwareInstructions)
    (laws : Avx2Cache.Instructions.InstructionContracts hardware)
    (q : TailPointers) (hlink : LinkedPrefix p hardware q.cache)
    (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (state : GlobalState) (hwf : state.WF) (hcache : SmallRange state.mem q.cache 1)
    (hready : Ready g d2 state) (hd : Separate g d2 q.cache) :
    CacheBackendsReady p (DoubleBase.RIR.serialLinkedReady g d2) noAvx q state := by
  refine ⟨⟨hready, True.intro⟩, ?_⟩
  intro after returned hcall hf
  rw [hlink.cacheCall] at hcall
  exact ⟨ready_output hready (cache_allocationShape hardware laws q.cache state after returned hwf hcache hcall) hf hd,
    True.intro⟩

theorem scalarReady (p : Primitives) (hardware : Avx2Cache.Instructions.HardwareInstructions)
    (laws : Avx2Cache.Instructions.InstructionContracts hardware)
    (q : TailPointers) (scratch : Pointer) (hlink : LinkedPrefix p hardware q.cache)
    (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (state : GlobalState) (bytes : Bytes32) (hwf : state.WF)
    (hsig : SmallRange state.mem q.signature 64) (hsc : SmallRange state.mem q.scalar 32)
    (hout : SmallRange state.mem scratch 32) (hcache : SmallRange state.mem q.cache 1)
    (hready : Ready g d2 state)
    (hdScratch : Separate g d2 scratch) (hdScalar : Separate g d2 q.scalar)
    (hdCache : Separate g d2 q.cache) :
    ScalarBackendsReady p (DoubleBase.RIR.serialLinkedReady g d2) noAvx q scratch state bytes := by
  intro checked htrace hf
  have hs := scalarTrace_allocationShape p q.signature scratch state checked
    hlink.black hlink.scalar hlink.bytesEq hwf hsig hout htrace
  have hr := ready_output hready hs hf hdScratch
  have hcopy := scalar_copy_frame checked q.signature q.scalar (bytes.extractLsb' 0 8)
    hf.wellFormed (hf.live _ _ hsc)
  have hcopyReady := ready_output hr (AllocationShape.scalarCopy checked _ _ _) hcopy hdScalar
  exact cacheReady p hardware laws q hlink g d2 _ hcopy.wellFormed
    (hcopy.live _ _ (hf.live _ _ hcache)) hcopyReady hdCache

/-- Range-only version: no semantic point/scalar assumptions enter readiness. -/
theorem bodyReady_of_ranges (p : Primitives) (hardware : Avx2Cache.Instructions.HardwareInstructions)
    (laws : Avx2Cache.Instructions.InstructionContracts hardware)
    (q : TailPointers) (z : PointPointers) (scratch : Pointer) (hlink : LinkedPrefix p hardware q.cache)
    (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (state : GlobalState) (bytes : Bytes32) (_hwf : state.WF)
    (hsig : SmallRange state.mem q.signature 64) (hsc : SmallRange state.mem q.scalar 32)
    (hout : SmallRange state.mem scratch 32) (hcache : SmallRange state.mem q.cache 1)
    (hp : SmallRange state.mem z.point 160) (hc : SmallRange state.mem z.cofactor 160)
    (hi : SmallRange state.mem z.identity 160) (hready : Ready g d2 state)
    (hdOption : Separate g d2 z.option)
    (hdPoint : ∀ ptr ∈ pointDestinations z, Separate g d2 ptr)
    (hdScratch : Separate g d2 scratch) (hdScalar : Separate g d2 q.scalar)
    (hdCache : Separate g d2 q.cache)
    (hdecodeShape : ∀ decoded, p.decompress (args2 z.option q.signature) state = .value (.nil, decoded) →
      GlobalShape g d2 state decoded) :
    BodyBackendsReady p (DoubleBase.RIR.serialLinkedReady g d2) noAvx q z scratch state bytes := by
  intro decoded hcall hf checked htrace hpframe
  have hdReady := ready_output_of_globalShape hready (hdecodeShape decoded hcall) hf hdOption
  have hs := pointTrace_allocationShape p z decoded checked hlink.cofactor hlink.pointEq
    hf.wellFormed (hf.live _ _ hp) (hf.live _ _ hc) (hf.live _ _ hi) htrace
  have hcReady := ready_point hdReady hs hpframe hdPoint
  exact scalarReady p hardware laws q scratch hlink g d2 checked bytes hpframe.wellFormed
    (hpframe.live _ _ (hf.live _ _ hsig)) (hpframe.live _ _ (hf.live _ _ hsc))
    (hpframe.live _ _ (hf.live _ _ hout)) (hpframe.live _ _ (hf.live _ _ hcache))
    hcReady hdScratch hdScalar hdCache

/-- All nondecoder call and copy effects are discharged by exact imported
execution. The decoder's shape premise is scoped to this one body invocation. -/
theorem bodyReady (p : Primitives) (hardware : Avx2Cache.Instructions.HardwareInstructions)
    (laws : Avx2Cache.Instructions.InstructionContracts hardware)
    (q : TailPointers) (z : PointPointers) (scratch : Pointer) (hlink : LinkedPrefix p hardware q.cache)
    (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (layout : Layout Point Scalar Result) (state : GlobalState) (h : Scalar) (a : Point) (r bytes : Bytes32)
    (hm : BodyMemory q z scratch state layout h a r bytes) (hdisjoint : BodyDisjoint q z scratch)
    (hready : Ready g d2 state)
    (hdOption : Separate g d2 z.option)
    (hdPoint : ∀ ptr ∈ pointDestinations z, Separate g d2 ptr)
    (hdScratch : Separate g d2 scratch) (hdScalar : Separate g d2 q.scalar)
    (hdCache : Separate g d2 q.cache)
    (hdecodeShape : ∀ decoded, p.decompress (args2 z.option q.signature) state = .value (.nil, decoded) →
      AllocationShape state decoded) :
    BodyBackendsReady p (DoubleBase.RIR.serialLinkedReady g d2) noAvx q z scratch state bytes := by
  intro decoded hcall hf checked htrace hpframe
  have hdReady := ready_output hready (hdecodeShape decoded hcall) hf hdOption
  have hmd := hm.decompressFrame hf hdisjoint
  have hs := pointTrace_allocationShape p z decoded checked hlink.cofactor hlink.pointEq
    hf.wellFormed hmd.point hmd.cofactor hmd.identity htrace
  have hcReady := ready_point hdReady hs hpframe hdPoint
  have hmc := hmd.pointFrame hpframe hdisjoint
  exact scalarReady p hardware laws q scratch hlink g d2 checked bytes hpframe.wellFormed
    hmc.signature hmc.tail.scalar hmc.scratch hmc.cache hcReady hdScratch hdScalar hdCache

end SerialBackendReadiness
end Agave.Ed25519.Verifier.Execution.Dalek
