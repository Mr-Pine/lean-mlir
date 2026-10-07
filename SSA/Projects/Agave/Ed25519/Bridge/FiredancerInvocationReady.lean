import SSA.Projects.Agave.Ed25519.Bridge.FiredancerExistingProof
import SSA.Projects.Agave.Ed25519.Bridge.HashChallenge
import SSA.Projects.Firedancer.Common.Proof.Scalar.fd_curve25519_scalar_reduce

/-!
Concrete preparation of the existing Firedancer proof invocation. A fresh
256-byte SHA allocation establishes all separation obligations. The loaded
curve constants and the actual initialized base-table entries remain loader
obligations; the mathematical table values and scalar determinism are proved.
No SHA determinism axiom is used: the three SHA call contracts stay explicit.
-/

namespace Agave.Ed25519.Bridge
open LeanMLIR SLLVM Firedancer Firedancer.Common

/-- The reducer determined by the committed source proof. This choice does
not assert termination or modular-arithmetic correctness. -/
noncomputable def firedancerSourceReduce : FiredancerReduce :=
  Classical.choose scalarReduce_determined

theorem firedancerSourceReduce_by : ScalarReduceBy firedancerSourceReduce :=
  Classical.choose_spec scalarReduce_determined

/-- Local reducer termination can be discharged by any defined execution on
the same 512 input bits. No uniform termination theorem is required. -/
theorem firedancerSourceReduce_returns_iff_defined_call
    (out inp : Pointer) (state : GlobalState) (hwf : state.WF)
    (hout : IsByteBufPtr state.mem out) (hoff : inp.offset.toNat + 64 ≤ 2 ^ 64)
    (hin : Fits state.mem inp (64 * 8)) :
    (∃ words, firedancerSourceReduce (readWord hin) = some words) ↔
      ∃ finalState,
        StateT.run (runFunction (fd_curve25519_scalar_reduce.denote
          (Ctxt.Valuation.ofHVector [.value inp, .value out]ₕ))) state =
          .value ([.value out]ₕ, finalState) := by
  have hby := firedancerSourceReduce_by out inp state hwf hout hoff hin
  constructor
  · rintro ⟨words, hw⟩
    obtain ⟨finalState, hrun, _⟩ := hby.1 words hw
    exact ⟨finalState, hrun⟩
  · rintro ⟨finalState, hrun⟩
    cases hwords : firedancerSourceReduce (readWord hin) with
    | some words => exact ⟨words, rfl⟩
    | none =>
      have hpoison := hby.2 hwords
      rw [hpoison] at hrun
      cases hrun

/-- The chosen deterministic model's packed value is exactly what an actual
successful reducer call writes. Arithmetic refinement can be proved against
that output buffer and transported to the invocation model. -/
theorem firedancerSourceReduce_value_of_call
    (out inp : Pointer) (state finalState : GlobalState) (hwf : state.WF)
    (hout : IsByteBufPtr state.mem out) (hoff : inp.offset.toNat + 64 ≤ 2 ^ 64)
    (hin : Fits state.mem inp (64 * 8)) (hout' : IsByteBufPtr finalState.mem out)
    (hrun : StateT.run (runFunction (fd_curve25519_scalar_reduce.denote
      (Ctxt.Valuation.ofHVector [.value inp, .value out]ₕ))) state =
      .value ([.value out]ₕ, finalState)) :
    ∃ words, firedancerSourceReduce (readWord hin) = some words ∧
      packWords words = readBuf hout' := by
  obtain ⟨words, hwords⟩ :=
    (firedancerSourceReduce_returns_iff_defined_call out inp state hwf hout hoff hin).mpr
      ⟨finalState, hrun⟩
  obtain ⟨otherState, hother, hequiv⟩ :=
    (firedancerSourceReduce_by out inp state hwf hout hoff hin).1 words hwords
  have hstates : finalState = otherState := by
    have heq := hrun.symm.trans hother
    simp only [PoisonOr.value_inj, Prod.mk.injEq] at heq
    exact heq.2
  subst otherState
  have hbuf : IsByteBufPtr (scalarOutMem state.mem out words) out :=
    isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice hout)))
  refine ⟨words, hwords, ?_⟩
  rw [← readBuf_scalarOutMem hout hbuf]
  exact readBuf_of_live?_eq (hequiv.live out.id).symm

/-- The affine odd multiple whose precomputed form belongs in entry `k`. -/
def firedancerBaseAffine (k : Nat) : CurvePoint :=
  (2 * k + 1) • _root_.Ed25519.basePoint.toAffine _root_.Ed25519.wellFormed_basePoint

def firedancerBasePoint (k : Nat) : _root_.Ed25519.Point :=
  _root_.Ed25519.decodedPoint (firedancerBaseAffine k).x (firedancerBaseAffine k).y

theorem firedancerBasePoint_wellFormed (k : Nat) :
    (firedancerBasePoint k).WellFormed where
  isUnit_Z := isUnit_one
  onCurve := by
    simpa [firedancerBasePoint, _root_.Ed25519.OnCurve, Edwards.Curve.OnCurve,
      _root_.Ed25519.curve] using (firedancerBaseAffine k).on
  t_spec := by simp [firedancerBasePoint, _root_.Ed25519.decodedPoint]

theorem firedancerBasePoint_toAffine (k : Nat) :
    (firedancerBasePoint k).toAffine (firedancerBasePoint_wellFormed k) =
      firedancerBaseAffine k := by
  apply Edwards.Point.ext
  · exact _root_.Ed25519.decodedPoint_x _ _
  · exact _root_.Ed25519.decodedPoint_y _ _

def firedancerBaseTable (k : Nat) : _root_.Ed25519.PrecomputedPoint :=
  (firedancerBasePoint k).toPrecomputed

theorem firedancerBaseTable_values :
    BaseVals firedancerBaseTable _root_.Ed25519.basePoint
      _root_.Ed25519.wellFormed_basePoint := by
  intro k _
  exact ⟨firedancerBasePoint k, firedancerBasePoint_wellFormed k, rfl, rfl,
    firedancerBasePoint_toAffine k⟩

/-- An initializer need only certify its one table address and its concrete
entries. The universally quantified table contract follows by symbol uniqueness. -/
theorem firedancerBaseTable_holds_of_entries (state : GlobalState) (q : Pointer)
    (hglobal : GlobalPtr state "fd_ed25519_base_point_wnaf_table" q)
    (hentries : ∀ k < 128,
      ∃ h : Firedancer.Ref.IsPointPtr state.mem (q.withOffset (BitVec.ofNat 64 (160 * k))),
        (∀ i, Firedancer.Ref.LimbBounds.Loose (Firedancer.Ref.isCoordPtr h i)) ∧
          _root_.Ed25519.PrecomputedPoint.ofSlots (Firedancer.Ref.readPoint h) =
            firedancerBaseTable k) :
    Firedancer.Ref.BaseTableHolds state firedancerBaseTable := by
  intro q' hq' k hk
  have heq : q' = q := Option.some.inj (hq'.symm.trans hglobal)
  subst q'
  exact hentries k hk

/-- Memory facts before the SHA allocation. A single 64-byte signature
buffer supplies both R and S; their separate buffer facts are derived. -/
structure FiredancerInputReady (state : GlobalState) (msg : Pointer) (sz : BitVec 64)
    (sig pk : Pointer) : Prop where
  message : Fits state.mem msg (sz.toNat * 8)
  signature : Fits state.mem sig (64 * 8)
  publicKey : IsByteBufPtr state.mem pk
  signatureNonNull : sig.id ≠ nullBlock
  signatureOffset : sig.offset.toNat + 64 ≤ 2 ^ 64
  messageOffset : msg.offset.toNat + sz.toNat ≤ 2 ^ 64

def firedancerFreshSha (state : GlobalState) : Pointer :=
  ⟨⟨state.alloc.nextFreeBlock⟩, 0⟩

def firedancerWithSha (state : GlobalState) : GlobalState := state.afterAlloca (256 * 8)

/-- Preparation fixes the complete initial SHA block, independently of the
other caller memory. Streaming contracts can therefore use this literal block. -/
@[simp] theorem firedancerFreshSha_live (state : GlobalState) :
    (firedancerWithSha state).mem.live? (firedancerFreshSha state).id =
      some { length := 256, bytes := 0#_ } :=
  live?_afterAlloca_self state (256 * 8)

theorem firedancerFreshSha_apart {state : GlobalState} (hwf : state.WF)
    {p : Pointer} {n : Nat} (h : Fits state.mem p n) :
    (firedancerFreshSha state).id ≠ p.id := by
  have hlt := lt_nextFreeBlock_of_fits hwf h
  intro heq
  have := congrArg BlockId.id heq
  simp only [firedancerFreshSha] at this
  omega

theorem FiredancerInputReady.args {state : GlobalState} {msg : Pointer} {sz : BitVec 64}
    {sig pk : Pointer} (h : FiredancerInputReady state msg sz sig pk) (hwf : state.WF) :
    VerifyArgs (firedancerWithSha state) msg sz sig pk (firedancerFreshSha state) := by
  have hs : Fits (firedancerWithSha state).mem sig (64 * 8) :=
    fits_of_live?_eq (live?_afterAlloca_of_fits hwf _ h.signature) h.signature
  have hS : Fits (firedancerWithSha state).mem (sig.withOffset 32) (32 * 8) := by
    simpa using remainingFits _ sig hs 32 (by decide)
  refine ⟨fits_of_live?_eq (live?_afterAlloca_of_fits hwf _ h.message) h.message,
    ⟨Fits.mono hs (by decide), by have := h.signatureOffset; omega⟩, ⟨hS, ?_⟩,
    ⟨fits_of_live?_eq (live?_afterAlloca_of_fits hwf _ h.publicKey.1) h.publicKey.1,
      h.publicKey.2⟩,
    fits_afterAlloca_self state (256 * 8), h.signatureNonNull,
    h.signatureOffset, h.messageOffset, by change 0 + 256 ≤ 2 ^ 64; decide,
    firedancerFreshSha_apart hwf h.signature,
    firedancerFreshSha_apart hwf h.publicKey.1,
    firedancerFreshSha_apart hwf h.message⟩
  have := h.signatureOffset
  simp only [Pointer.withOffset, BitVec.toNat_add]
  change (sig.offset.toNat + 32) % 2 ^ 64 + 32 ≤ 2 ^ 64
  omega

/-- The remaining global facts are precisely initialization: loaded field
constants, SHA constants, and bounded table entries containing odd multiples. -/
structure FiredancerGlobalsReady (state : GlobalState) (kbits : BitVec (80 * 64)) : Prop where
  reference : state.RefWF []
  shaConstants : ∃ q, HoldsGlobal state "fd_sha512_core_ref.K" q kbits
  baseTable : Firedancer.Ref.BaseTableHolds state firedancerBaseTable

theorem FiredancerGlobalsReady.referenceWithSha {state : GlobalState}
    {kbits : BitVec (80 * 64)} (h : FiredancerGlobalsReady state kbits) :
    (firedancerWithSha state).RefWF [firedancerFreshSha state] := by
  apply Firedancer.Ref.DoubleScalarMulBase.refWF_widen h.reference
    (h.reference.wf.afterAlloca _) rfl
  · intro b hb _
    exact live?_afterAlloca_of_lt hb
  · intro p hp
    have hp' : p = firedancerFreshSha state := by simpa using hp
    subst p
    exact Or.inl (Nat.le_refl _)

theorem FiredancerGlobalsReady.shaConstantsWithSha {state : GlobalState}
    {kbits : BitVec (80 * 64)} (h : FiredancerGlobalsReady state kbits) :
    Sha512KHolds (firedancerWithSha state) (firedancerFreshSha state) kbits := by
  obtain ⟨q, hq, hf, hv⟩ := h.shaConstants
  obtain ⟨hf', hv'⟩ := readWord_of_live?_eq
    (live?_afterAlloca_of_fits h.reference.wf (256 * 8) hf) hf
  exact ⟨q, ⟨hq, hf', hv'.trans hv⟩, (firedancerFreshSha_apart h.reference.wf hf).symm⟩

theorem FiredancerGlobalsReady.baseTableWithSha {state : GlobalState}
    {kbits : BitVec (80 * 64)} (h : FiredancerGlobalsReady state kbits) :
    Firedancer.Ref.BaseTableHolds (firedancerWithSha state) firedancerBaseTable := by
  apply h.baseTable.of_live?_eq (s' := firedancerWithSha state) rfl
  intro q hq
  obtain ⟨q', hq', _⟩ := h.reference.gtbl
  have heq : q = q' := Option.some.inj (hq.symm.trans hq'.addr)
  subst q'
  exact live?_afterAlloca_of_fits h.reference.wf _ hq'.fits

/-- Three actual SHA call contracts are the external execution boundary.
Scalar determinism and the mathematical base-table contract are supplied by
proved theorems, and freshness supplies every required disjointness fact. -/
theorem FiredancerGlobalsReady.environment {state : GlobalState}
    {kbits : BitVec (80 * 64)} (h : FiredancerGlobalsReady state kbits)
    (calls : FiredancerHashCalls)
    (finishBlock : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option LiveBlock)
    (hinit : Sha512InitBy calls.init)
    (happend : Sha512AppendBy kbits calls.append)
    (hfinish : Sha512FiniBy kbits calls.finish finishBlock) :
    FiredancerRefEnvironment (firedancerWithSha state) (firedancerFreshSha state)
      firedancerSourceReduce kbits calls.init calls.append calls.finish finishBlock :=
  ⟨h.referenceWithSha, h.shaConstantsWithSha, firedancerSourceReduce_by,
    hinit, happend, hfinish,
    firedancerBaseTable, h.baseTableWithSha, firedancerBaseTable_values⟩

end Agave.Ed25519.Bridge
