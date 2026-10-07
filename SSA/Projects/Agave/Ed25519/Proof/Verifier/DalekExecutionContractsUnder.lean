import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekPrefixTrace
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekDoubleBaseContractUnder
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionDecoderContextual

/-! Contextual backend contracts and invocation-local readiness. The staged
readiness predicates mention only the actual caller pointers and prefix calls and frames;
they do not assert backend execution or require globals in arbitrary states. -/
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR

abbrev BackendReadyPredicate := Pointer → Pointer → Pointer → Pointer → GlobalState → Prop

def BackendsReady (serialReady avx2Ready : BackendReadyPredicate)
    (q : TailPointers) (state : GlobalState) : Prop :=
  serialReady q.output q.challenge q.point q.scalar state ∧
  avx2Ready q.output q.challenge q.point q.scalar state

/-- Readiness before the optional single-byte cache initialization. -/
def CacheBackendsReady (p : Primitives) (serialReady avx2Ready : BackendReadyPredicate)
    (q : TailPointers) (state : GlobalState) : Prop :=
  BackendsReady serialReady avx2Ready q state ∧
  ∀ after returned, p.initializeAvx2Cache .nil state =
    .value (.cons (.value returned) .nil, after) →
    OutputFrame state after q.cache 1 → BackendsReady serialReady avx2Ready q after

/-- The scalar copy has a deterministic state, so readiness is required there. -/
def CopyBackendsReady (p : Primitives) (serialReady avx2Ready : BackendReadyPredicate)
    (q : TailPointers) (state : GlobalState) (first : BitVec 8) : Prop :=
  CacheBackendsReady p serialReady avx2Ready q (scalarCopyState state q.signature q.scalar first)

/-- The scalar checker only writes its scratch output. -/
def ScalarBackendsReady (p : Primitives) (serialReady avx2Ready : BackendReadyPredicate)
    (q : TailPointers) (scratch : Pointer) (state : GlobalState) (bytes : Bytes32) : Prop :=
  ∀ after, ScalarCallTrace p q.signature scratch state after →
    OutputFrame state after scratch 32 →
    CopyBackendsReady p serialReady avx2Ready q after (bytes.extractLsb' 0 8)

/-- Readiness through the decoder and the point-small-order check. -/
def BodyBackendsReady (p : Primitives) (serialReady avx2Ready : BackendReadyPredicate)
    (q : TailPointers) (z : PointPointers) (scratch : Pointer)
    (state : GlobalState) (bytes : Bytes32) : Prop :=
  ∀ decoded, p.decompress (args2 z.option q.signature) state = .value (.nil, decoded) →
    OutputFrame state decoded z.option 168 →
    ∀ checked, PointCallTrace p z decoded checked → PointCheckFrame decoded checked z →
      ScalarBackendsReady p serialReady avx2Ready q scratch checked bytes

structure NonDecoderLeafContractsUnder (p : Primitives) (g : Globals)
    (serialReady avx2Ready : BackendReadyPredicate)
    (layout : Layout Point Scalar Result) (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    : Prop where
  pointMulByPow2 : CofactorContract p.pointMulByPow2 layout
  pointConstantTimeEq : SmallOrderEqContract p.pointConstantTimeEq layout shared
  blackBoxByte : BlackBoxContract p.blackBoxByte
  scalarReduce : ScalarReduceContract p.scalarReduce layout
  bytesConstantTimeEq : BytesEqContract p.bytesConstantTimeEq
  initializeAvx2Cache : CacheContract p.initializeAvx2Cache g.address1
  serialDoubleBase : DoubleBaseContractUnder serialReady p.serialDoubleBase layout doubleBase
  avx2DoubleBase : DoubleBaseContractUnder avx2Ready p.avx2DoubleBase layout doubleBase
  compressPoint : CompressContract p.compressPoint layout compress
  compareBytes : CompareContract p.compareBytes
  scalarParse : ScalarParseContract layout shared
  scalarComplete : ScalarParseComplete layout shared


end Agave.Ed25519.Verifier.Execution.Dalek
