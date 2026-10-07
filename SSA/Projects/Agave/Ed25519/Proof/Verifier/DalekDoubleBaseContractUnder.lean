import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContracts

/-! Invocation-local readiness for the actual four-pointer double-base ABI.
The existing unconditional Dalek contract is unchanged. -/
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

def DoubleBaseContractUnder
    (ready : Pointer → Pointer → Pointer → Pointer → GlobalState → Prop)
    (call : Vals [.ptr, .ptr, .ptr, .ptr] → EffectM (Vals []))
    (layout : Layout Point Scalar Result) (doubleBase : Scalar → Point → Scalar → Result) : Prop :=
  ∀ (out hptr aptr sptr : Pointer) (state : GlobalState) (h s : Scalar) (a : Point), state.WF →
    ready out hptr aptr sptr state → SmallRange state.mem out 160 →
    ReadBytes state hptr 32 (layout.scalar h) →
    ReadBytes state aptr 160 (layout.point a) →
    ReadBytes state sptr 32 (layout.scalar s) →
    (Range.of out 1280).Disjoint (Range.of hptr 256) →
    (Range.of out 1280).Disjoint (Range.of aptr 1280) →
    (Range.of out 1280).Disjoint (Range.of sptr 256) →
    ∃ after encoded,
      call (args4 out hptr aptr sptr) state = .value (.nil, after) ∧
      OutputFrame state after out 160 ∧ ReadBytes after out 160 encoded ∧
      layout.result (doubleBase h a s) encoded

theorem DoubleBaseContract.under
    (h : DoubleBaseContract call layout doubleBase)
    (ready : Pointer → Pointer → Pointer → Pointer → GlobalState → Prop) :
    DoubleBaseContractUnder ready call layout doubleBase := by
  intro out hptr aptr sptr state hval sval aval hwf _ hout hh ha hs hdH hdA hdS
  exact h out hptr aptr sptr state hval sval aval hwf hout hh ha hs hdH hdA hdS

theorem DoubleBaseContractUnder.mono
    (h : DoubleBaseContractUnder ready call layout doubleBase)
    (hready : ∀ out hptr aptr sptr state, stronger out hptr aptr sptr state →
      ready out hptr aptr sptr state) :
    DoubleBaseContractUnder stronger call layout doubleBase := by
  intro out hptr aptr sptr state hval sval aval hwf hr hout hh ha hs hdH hdA hdS
  exact h out hptr aptr sptr state hval sval aval hwf (hready _ _ _ _ _ hr)
    hout hh ha hs hdH hdA hdS

/-- The unconditional contract follows only when its ordinary input and
aliasing premises establish invocation readiness. -/
theorem DoubleBaseContractUnder.unconditional
    {Point Scalar Result : Type} {layout : Layout Point Scalar Result}
    {doubleBase : Scalar → Point → Scalar → Result}
    {call : Vals [.ptr, .ptr, .ptr, .ptr] → EffectM (Vals [])}
    {ready : Pointer → Pointer → Pointer → Pointer → GlobalState → Prop}
    (h : DoubleBaseContractUnder ready call layout doubleBase)
    (hready : ∀ (out hptr aptr sptr : Pointer) (state : GlobalState)
      (hval sval : Scalar) (aval : Point), state.WF →
      SmallRange state.mem out 160 →
      ReadBytes state hptr 32 (layout.scalar hval) →
      ReadBytes state aptr 160 (layout.point aval) →
      ReadBytes state sptr 32 (layout.scalar sval) →
      (Range.of out 1280).Disjoint (Range.of hptr 256) →
      (Range.of out 1280).Disjoint (Range.of aptr 1280) →
      (Range.of out 1280).Disjoint (Range.of sptr 256) →
      ready out hptr aptr sptr state) :
    DoubleBaseContract call layout doubleBase := by
  intro out hptr aptr sptr state hval sval aval hwf hout hh ha hs hdH hdA hdS
  exact h out hptr aptr sptr state hval sval aval hwf
    (hready out hptr aptr sptr state hval sval aval hwf hout hh ha hs hdH hdA hdS)
    hout hh ha hs hdH hdA hdS

end Agave.Ed25519.Verifier.Execution.Dalek
