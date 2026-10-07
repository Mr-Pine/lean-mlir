import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2DalekAdapter
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekDoubleBaseContractUnder

namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Reduce64.Execution (SmallRange)
open Verifier Verifier.Execution
set_option maxRecDepth 10000

theorem readKeyWords_of_validPoint (s : GlobalState) (q : Pointer) (P : ValidPoint)
    (hp : Dalek.ReadBytes s q 160 P.bytes) : readKeyWords s q = P.words := by
  have hx : SerialFieldMul.readLimbs s q = P.words.X := by
    simpa [SmallOrder.coordinates] using SmallOrder.read_coordinate s q P.words hp 0
  have hy : SerialFieldMul.readLimbs s (q.add 40) = P.words.Y := by
    simpa [SmallOrder.coordinates] using SmallOrder.read_coordinate s q P.words hp 1
  have hz : SerialFieldMul.readLimbs s (q.add 80) = P.words.Z := by
    simpa [SmallOrder.coordinates] using SmallOrder.read_coordinate s q P.words hp 2
  have ht : SerialFieldMul.readLimbs s (q.add 120) = P.words.T := by
    simpa [SmallOrder.coordinates] using SmallOrder.read_coordinate s q P.words hp 3
  unfold readKeyWords
  rw [hx, hy, hz, ht]

theorem validPoint_readPoint_represents (s : GlobalState) (q : Pointer) (P : ValidPoint)
    (hp : Dalek.ReadBytes s q 160 P.bytes) :
    Tables.Represents (Conformance.BackendExecution.readPoint s q) P.curve := by
  rw [← serial_readPoint_value, ← readKeyWords_unsigned, readKeyWords_of_validPoint s q P hp]
  exact (SmallOrder.key_represents_iff P.words P.curve).mp P.represents

/-- The verifier's exact bytes already provide the constructor's widened
input bound. No normalization or canonical-byte premise is imposed here. -/
theorem validPoint_input_tight (s : GlobalState) (q : Pointer) (P : ValidPoint)
    (hp : Dalek.ReadBytes s q 160 P.bytes) (c : Fin 4) (k : Fin 5) :
    (s.mem.readAt (q.add (BitVec.ofNat 64 (40*c.val+8*k.val))) 64).toNat < 2^52 := by
  have he : s.mem.readAt (q.add (BitVec.ofNat 64 (40*c.val+8*k.val))) 64 =
      SmallOrder.coordinates P.words c k := by
    simpa only [SerialFieldMul.readLimbs, Pointer.add_add, ← BitVec.ofNat_add] using
      congrArg (fun words => words k) (SmallOrder.read_coordinate s q P.words hp c)
  rw [he]
  have ht : SerialPoint.Tight (SerialFieldMul.unsigned (SmallOrder.coordinates P.words c)) := by
    fin_cases c
    · exact P.tightX
    · exact P.tightY
    · exact P.tightZ
    · exact P.tightT
  exact ht k

/-- Exact input bytes imply the AVX2 constructor's noncanonical limb bound. -/
theorem validPoint_input_bounds (s : GlobalState) (q : Pointer) (P : ValidPoint)
    (hp : Dalek.ReadBytes s q 160 P.bytes) : serialLimbsBounded s q :=
  validPoint_input_tight s q P hp

/-- No separate output, full-backend, or representation contract is assumed.
The five local blocks must preserve the caller-memory invariant, in addition
to their existing arithmetic and control obligations. -/
theorem doubleBaseContractUnder_of_blocks
    (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (cofactor : ValidPoint → ValidPoint)
    (ready : Pointer → Pointer → Pointer → Pointer → GlobalState → Prop)
    (htable : TableContract p.call0)
    (hblocks : ∀ (i : Conformance.BackendExecution.Invocation) (state : GlobalState),
      ready i.output i.scalarA i.pointA i.scalarB state → Input i state →
      ArithmeticBlocks p g (DalekContext i state)
        (state.mem.readAt i.scalarA 256).toNat (state.mem.readAt i.scalarB 256).toNat
        (avx2StackPtr state 29) (avx2StackPtr state 28)
        (finiteTable (Tables.avx2DoubleBaseTable
          (Conformance.BackendExecution.readPoint state i.pointA)))) :
    Dalek.DoubleBaseContractUnder ready (avx2Kernel p g).call
      (ValidPoint.layout cofactor) ValidPoint.doubleBase := by
  intro out hptr aptr sptr state hval sval aval hwf hr hout hh hA hs _ _ _
  let i : Conformance.BackendExecution.Invocation := ⟨out, hptr, aptr, sptr⟩
  have hi : Input i state :=
    ⟨hwf, hout, hh.1, hA.1, hs.1, validPoint_input_bounds state aptr aval hA⟩
  have hH : state.mem.readAt hptr 256 = CanonicalScalar.encode hval := hh.2
  have hS : state.mem.readAt sptr 256 = CanonicalScalar.encode sval := hs.2
  have hHbound : (state.mem.readAt i.scalarA 256).toNat < 2^255 := by
    change (state.mem.readAt hptr 256).toNat < 2^255
    rw [hH, CanonicalScalar.encode_toNat]
    exact CanonicalScalar.bound hval
  have hSbound : (state.mem.readAt i.scalarB 256).toNat < 2^255 := by
    change (state.mem.readAt sptr 256).toNat < 2^255
    rw [hS, CanonicalScalar.encode_toNat]
    exact CanonicalScalar.bound sval
  obtain ⟨P, after, hcall, hframe, hcurve, hbytes⟩ :=
    backend_validPoint_of_framed_blocks p g htable i state hi (hblocks i state hr hi)
      aval.curve (validPoint_readPoint_represents state aptr aval hA) hHbound hSbound
  refine ⟨after, P.bytes, hcall, hframe, hbytes, P, ?_, rfl⟩
  change P.curve = hval.val • aval.curve + sval.val • Tables.baseGroup
  simpa only [i, hH, hS, CanonicalScalar.encode_toNat] using hcurve

end Agave.Ed25519.DoubleBase.ExecutionAvx2
