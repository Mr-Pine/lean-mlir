import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryStartupMemory

/-! Complete call composition for the exact imported Montgomery callee. Its
post-state keeps the caller allocation domain, writes five output words, and
accounts for all nine scratch allocations plus the real black-box allocation. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
open LeanMLIR.RIR
open Agave.Ed25519.Bridge
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 100000

/-- Exact callee post-state, with every private allocation erased. -/
def callPostState (state : GlobalState) (a b : Fin 5 → BitVec 64)
    (out left right : Pointer) : GlobalState :=
  { alloc := ⟨state.alloc.nextFreeBlock + 10⟩,
    mem := outputStores state.mem out (tailWords (quotient52 a b left right)) }

/-- The actual imported call, under live input/output and normalized limb facts.
The constant operand is canonical; no primitive-reducer correctness is assumed. -/
theorem program_call (p : Primitives)
    (hblack : p.blackBoxByte = Agave.Ed25519.Encoding.Decompress.Execution.BlackBox.program.call)
    (state : GlobalState) (a b : Fin 5 → BitVec 64) (out left right : Pointer)
    (hwf : state.WF) (hout : SmallRange state.mem out 40)
    (hlive : SmallRange state.mem left 40) (hrive : SmallRange state.mem right 40)
    (ha : ∀ i : Fin 5, state.mem.readAt (left.add (BitVec.ofNat 64 (8 * i.val))) 64 = a i)
    (hb : ∀ i : Fin 5, state.mem.readAt (right.add (BitVec.ofNat 64 (8 * i.val))) 64 = b i)
    (habound : ∀ i, (a i).toNat < 2 ^ 52) (hbbound : ∀ i, (b i).toNat < 2 ^ 52)
    (hbcanonical : limbValue (fun i => (b i).toNat) < subgroupOrder) :
    (program p).call (.cons (.value out) (.cons (.value left) (.cons (.value right) .nil))) state =
      .value (.nil, callPostState state a b out left right) := by
  let args : Vals [.ptr, .ptr, .ptr] :=
    .cons (.value out) (.cons (.value left) (.cons (.value right) .nil))
  let e0 : Env program.Γ := Env.init args.get
  let e1 := startupEnv e0 state
  let s1 := startupState state
  let scratch := scratchPtrs state
  let ef := bodyEnv e1 a b out left right
  let sf := bodyState s1 a b out left right scratch
  have hs1 : s1.WF := by
    dsimp only [s1]
    rw [startupState_eq_allocSteps]
    exact allocSteps_wf state hwf 9
  have hready : BodyReady e1 out left right scratch :=
    startup_bodyReady e0 state out left right rfl rfl rfl
  have hout1 : SmallRange s1.mem out 40 := by
    dsimp only [s1]
    rw [startupState_eq_allocSteps]
    exact allocSteps_smallRange state hwf out 40 hout 9
  have hleft1 : SmallRange s1.mem left 40 := by
    dsimp only [s1]
    rw [startupState_eq_allocSteps]
    exact allocSteps_smallRange state hwf left 40 hlive 9
  have hright1 : SmallRange s1.mem right 40 := by
    dsimp only [s1]
    rw [startupState_eq_allocSteps]
    exact allocSteps_smallRange state hwf right 40 hrive 9
  have ha1 (i : Fin 5) : s1.mem.readAt (left.add (BitVec.ofNat 64 (8 * i.val))) 64 = a i := by
    dsimp only [s1]
    rw [startupState_eq_allocSteps, allocSteps_read state hwf _ 64
      (hlive.fits_add (k := 8 * i.val) (count := 8) (by omega)) 9, ha i]
  have hb1 (i : Fin 5) : s1.mem.readAt (right.add (BitVec.ofNat 64 (8 * i.val))) 64 = b i := by
    dsimp only [s1]
    rw [startupState_eq_allocSteps, allocSteps_read state hwf _ 64
      (hrive.fits_add (k := 8 * i.val) (count := 8) (by omega)) 9, hb i]
  have hbody := body_run p hblack e1 s1 a b out left right scratch hready hs1
    hout1 hleft1 hright1 (scratchPtrs_fits state hwf)
    (scratchPtrs_ne_caller state hwf left 320 hlive.fits)
    (scratchPtrs_ne_caller state hwf right 320 hrive.fits)
    ha1 hb1 habound hbbound hbcanonical
  have hfull : (program.entry p).runBodyFrom e0 0 state = .value (ef, sf) := by
    rw [runBodyFrom_chunk (startup_run p e0 state)]
    exact hbody
  have hblock : (program.entry p).run program.blockParams e0 state =
      .value ((ef, .inl .nil), sf) := by
    rw [BasicBlock.run_eq]
    simp only [EffectM.bind_eq, hfull, LeanMLIR.RIR.PoisonOr.value_bind]
    rfl
  have hrun : (program p).run args state = .value (.nil, sf) := by
    rw [Func.run_runFrom_eq, Func.runFrom_eq]
    change (do
      let ((E', res), s') ← (program.entry p).run program.blockParams e0 state
      Func.continue («func» := program p) E' res s') = _
    rw [hblock]
    rfl
  have hpost : {sf with mem := sf.mem.eraseFrom state.alloc.nextFreeBlock} =
      callPostState state a b out left right := by
    apply GlobalState.ext
    · change (⟨(startupState state).alloc.nextFreeBlock + 1⟩ : AllocState) =
        ⟨state.alloc.nextFreeBlock + 10⟩
      congr 1
    · change (zeroizeStores
        (outputStores (productStates s1 a b left right scratch 8).mem out
          (tailWords (quotient52 a b left right))) scratch).eraseFrom state.alloc.nextFreeBlock = _
      rw [zeroizeStores_erase _ _ _ (scratchPtrs_local state), outputStores_erase,
        productStates_erase s1 a b left right scratch _ (scratchPtrs_local state) 8,
        startupState_erase state hwf]
      rfl
  have hcall := Func.call_of_run hrun
  simpa only [hpost] using hcall

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
