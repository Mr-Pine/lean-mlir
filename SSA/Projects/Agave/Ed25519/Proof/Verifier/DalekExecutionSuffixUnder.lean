import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionTailUnder

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

theorem copy_tail_of_contracts_under {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (serialReady avx2Ready : BackendReadyPredicate)
    (hserial : DoubleBaseContractUnder serialReady p.serialDoubleBase layout doubleBase)
    (havx2 : DoubleBaseContractUnder avx2Ready p.avx2DoubleBase layout doubleBase)
    (hcompress : CompressContract p.compressPoint layout compress)
    (hcompare : CompareContract p.compareBytes)
    (q : TailPointers) (hinit : CacheContract p.initializeAvx2Cache q.cache)
    (E : Env program.Γ) (state : GlobalState)
    (h scalar : Scalar) (a : Point) (r : Bytes32)
    (hready : CopyBackendsReady p serialReady avx2Ready q state ((layout.scalar scalar).extractLsb' 0 8))
    (hregs : TailRegisters q E) (hmem : TailBeforeCopy q state layout h a r)
    (hfirst : E.read (%50) = .value ((layout.scalar scalar).extractLsb' 0 8))
    (h33 : E.read (%15) = .value 33#64) (h1 : E.read (%16) = .value 1#64)
    (h31 : E.read (%17) = .value 31#64)
    (hsig : SmallRange state.mem q.signature 64)
    (hbytes : ReadBytes state (q.signature.add 32#64) 32 (layout.scalar scalar))
    (hds : (Range.of q.signature 512).Disjoint (Range.of q.scalar 256))
    (hc : SmallRange state.mem q.cache 1) (hdc : CacheDisjoint q) :
    ∃ after, (program p g).runFrom E 5 state =
      .value (.cons (.value (code (decide (compress (doubleBase h a scalar) = r)))) .nil, after) := by
  let first := (layout.scalar scalar).extractLsb' 0 8
  let copied := scalarCopyState state q.signature q.scalar first
  let cached := copied.mem.readAt q.cache 8
  have hhigh := scalar_signature_subread state q.signature (layout.scalar scalar) hbytes 1 31 (by decide)
  change state.mem.readAt (q.signature.add 33#64) 248 = (layout.scalar scalar).extractLsb' 8 248 at hhigh
  have hread := scalar_copy_readback state q.signature q.scalar first (layout.scalar scalar)
    hmem.scalar hhigh rfl
  have hframe := scalar_copy_frame state q.signature q.scalar first hmem.wellFormed hmem.scalar
  have htail := (hmem.frame hframe hmem.challengeScalar hmem.pointScalar hmem.signatureScalar).finish hread
  have hregsc := TailRegisters.scalarCopy q E hregs cached
  have hfc := hframe.live q.cache 1 hc
  have hdhigh := disjoint_add_subrange hsig hds.symm (k := 33) (count := 31) (by decide)
  have hdcopy := (disjoint_add_subrange hmem.scalar hdhigh.symm (k := 1) (count := 31) (by decide)).symm
  rw [scalar_copy_block p g E state q.signature q.scalar q.cache first cached
    hregs.signature hregs.scalar hregs.cache hfirst h33 h1 h31 hregs.ok
    hsig hmem.scalar hdcopy hc.fits rfl]
  by_cases heq : cached = 255#8
  · simp only [heq, ↓reduceIte]
    have hi := initialized_tail_of_contracts_under p g layout doubleBase compress serialReady avx2Ready hserial havx2 hcompress
      hcompare q hinit _ copied h scalar a r hready.2 hregsc htail ⟨hfc, heq⟩ hdc
    simpa only [heq] using hi
  · simp only [heq, ↓reduceIte]
    exact dispatch_tail_of_contracts_under p g layout doubleBase compress serialReady avx2Ready hserial havx2 hcompress
      hcompare q _ copied h scalar a r cached hready.1 hregsc htail hfc.fits rfl


end Agave.Ed25519.Verifier.Execution.Dalek
