import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionControl
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekIdentityMemory

/-! The exact decoded-R payload transport and cofactor rejection block. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

structure PointPointers where
  option : Pointer
  slot29 : Pointer
  slot30 : Pointer
  point : Pointer
  cofactor : Pointer
  identity : Pointer
  one : Pointer

structure PointRegisters (q : PointPointers) (E : Env program.Γ) : Prop where
  option : E.read (%28) = .value q.option
  slot29 : E.read (%29) = .value q.slot29
  slot30 : E.read (%30) = .value q.slot30
  point : E.read (%31) = .value q.point
  cofactor : E.read (%22) = .value q.cofactor
  identity : E.read (%21) = .value q.identity
  one : E.read (%5) = .value q.one
  three : E.read (%2) = .value 3#32
  zero : E.read (%3) = .value 0#8
  forty : E.read (%4) = .value 40#64
  eighty : E.read (%6) = .value 80#64
  oneTwenty : E.read (%7) = .value 120#64
  error : E.read (%8) = .value 2#8
  eight : E.read (%9) = .value 8#64
  six : E.read (%10) = .value 6#64
  length : E.read (%11) = .value 160#64

def pointBlockEnv (E : Env program.Γ) (q : PointPointers) (small : Bool) : Env program.Γ :=
  let E' := E[%41 := .value (q.option.add 8#64), %42 := .value (q.slot29.add 6#64),
    %43 := .value (q.slot30.add 6#64), %44 := .value (q.identity.add 40#64),
    %45 := .value (q.identity.add 80#64), %46 := .value (q.identity.add 120#64),
    %47 := .value (choiceByte small), %48 := .value (BitVec.ofBool (!small))]
  if small then E'[%70 := .value 2#8] else E'

/-- Block 2 executes the three emitted payload copies, multiplication by eight,
four identity stores, exact Choice comparison, and its parameterized branch.
Only the two external-call equalities are assumed. -/
theorem point_check_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (q : PointPointers) (s t u : GlobalState) (small : Bool)
    (hregs : PointRegisters q E)
    (hout : SmallRange s.mem q.option 168)
    (h29 : SmallRange s.mem q.slot29 166)
    (h30 : SmallRange s.mem q.slot30 166)
    (hp : SmallRange s.mem q.point 160)
    (hd1 : (Range.of (q.slot29.add 6#64) 1280).Disjoint
      (Range.of (q.option.add 8#64) 1280))
    (hd2 : (Range.of (q.slot30.add 6#64) 1280).Disjoint
      (Range.of (q.slot29.add 6#64) 1280))
    (hd3 : (Range.of q.point 1280).Disjoint (Range.of (q.slot30.add 6#64) 1280))
    (hmul : p.pointMulByPow2 (.cons (.value q.cofactor) (.cons (.value q.point)
      (.cons (.value 3#32) .nil))) (optionCopyState s q.option q.slot29 q.slot30 q.point) =
      .value (.nil, t))
    (hid : SmallRange t.mem q.identity 160)
    (hone : Fits t.mem q.one 320) (hread : t.mem.readAt q.one 320 = 1#320)
    (hidne : q.identity.id ≠ q.one.id)
    (heq : p.pointConstantTimeEq (args2 q.cofactor q.identity)
      (identityStoreState t q.identity) = .value (.cons (.value (choiceByte small)) .nil, u)) :
    (program p g).runFrom E 2 s =
      (program p g).runFrom (pointBlockEnv E q small) (if small then 12 else 4) u := by
  dsimp only [args2] at heq
  rcases hregs with ⟨ho, h29r, h30r, hpr, hcr, hir, h1r, h3, h0, h40, h80, h120,
    herr, h8, h6, h160⟩
  let s1 := copyPointState s (q.slot29.add 6#64) (q.option.add 8#64)
  let s2 := copyPointState s1 (q.slot30.add 6#64) (q.slot29.add 6#64)
  let s3 := copyPointState s2 q.point (q.slot30.add 6#64)
  let i0 : GlobalState := { t with mem := t.mem.storeAt q.identity (0#320) }
  let i1 : GlobalState := { i0 with mem := i0.mem.storeAt (q.identity.add 40#64) (1#320) }
  let i2 : GlobalState := { i1 with mem := i1.mem.storeAt (q.identity.add 80#64) (1#320) }
  have hg8 : Operation.gepInboundsLive s.mem (.value q.option) [.value (8 : Int)] =
      .value (q.option.add 8#64) := hout.gep (k := 8) (by decide)
  have hg6a : Operation.gepInboundsLive s.mem (.value q.slot29) [.value (6 : Int)] =
      .value (q.slot29.add 6#64) := h29.gep (k := 6) (by decide)
  have hg6b : Operation.gepInboundsLive s1.mem (.value q.slot30) [.value (6 : Int)] =
      .value (q.slot30.add 6#64) := (h30.storeAt _ _).gep (k := 6) (by decide)
  have hc1 (env : Env program.Γ) := copy_point_operation s (q.slot29.add 6#64)
    (q.option.add 8#64) env (smallRange_add h29 (k := 6) (by decide))
    (smallRange_add hout (k := 8) (by decide)) hd1
  have hc2 (env : Env program.Γ) := copy_point_operation s1 (q.slot30.add 6#64)
    (q.slot29.add 6#64) env ((smallRange_add h30 (k := 6) (by decide)).storeAt _ _)
    ((smallRange_add h29 (k := 6) (by decide)).storeAt _ _) hd2
  have hc3 (env : Env program.Γ) := copy_point_operation s2 q.point (q.slot30.add 6#64)
    env ((hp.storeAt _ _).storeAt _ _)
    (((smallRange_add h30 (k := 6) (by decide)).storeAt _ _).storeAt _ _) hd3
  have hzero0 (env : Env program.Γ) := identity_zero_operation t q.identity env
    (Fits.mono (by decide) hid.fits)
  have hg40 : Operation.gepInboundsLive i0.mem (.value q.identity) [.value (40 : Int)] =
      .value (q.identity.add 40#64) := (hid.storeAt _ _).gep (k := 40) (by decide)
  have hg80 : Operation.gepInboundsLive i1.mem (.value q.identity) [.value (80 : Int)] =
      .value (q.identity.add 80#64) := ((hid.storeAt _ _).storeAt _ _).gep (k := 80) (by decide)
  have hg120 : Operation.gepInboundsLive i2.mem (.value q.identity) [.value (120 : Int)] =
      .value (q.identity.add 120#64) := (((hid.storeAt _ _).storeAt _ _).storeAt _ _).gep
        (k := 120) (by decide)
  have hr0 : i0.mem.readAt q.one 320 = 1#320 := by
    dsimp [i0]
    rw [MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hidne)]
    exact hread
  have hr1 : i1.mem.readAt q.one 320 = 1#320 := by
    dsimp only [i1]
    rw [MemoryState.readAt_storeAt_disjoint
      (Range.disjoint_of_id_ne (p := q.identity.add 40#64) hidne)]
    exact hr0
  have hone40 (env : Env program.Γ) := identity_one_operation i0 (q.identity.add 40#64)
    q.one env (hid.fits_add (k := 40) (count := 40) (by decide)).storeAt hone.storeAt
    hr0 (Range.disjoint_of_id_ne hidne)
  have hone80 (env : Env program.Γ) := identity_one_operation i1 (q.identity.add 80#64)
    q.one env ((hid.fits_add (k := 80) (count := 40) (by decide)).storeAt).storeAt
    hone.storeAt.storeAt hr1 (Range.disjoint_of_id_ne hidne)
  have hzero120 (env : Env program.Γ) := identity_zero_operation i2
    (q.identity.add 120#64) env
    (((hid.fits_add (k := 120) (count := 40) (by decide)).storeAt).storeAt).storeAt
  change ∀ env, Operation.memcpy (.value (q.slot29.add 6#64))
    (.value (q.option.add 8#64)) (.value 160#64) env s = .value (env, s1) at hc1
  change ∀ env, Operation.memcpy (.value (q.slot30.add 6#64))
    (.value (q.slot29.add 6#64)) (.value 160#64) env s1 = .value (env, s2) at hc2
  change ∀ env, Operation.memcpy (.value q.point)
    (.value (q.slot30.add 6#64)) (.value 160#64) env s2 = .value (env, s3) at hc3
  change ∀ env, Operation.memset (.value q.identity) (.value 0#8)
    (.value 40#64) env t = .value (env, i0) at hzero0
  change ∀ env, Operation.memcpy (.value (q.identity.add 40#64))
    (.value q.one) (.value 40#64) env i0 = .value (env, i1) at hone40
  change ∀ env, Operation.memcpy (.value (q.identity.add 80#64))
    (.value q.one) (.value 40#64) env i1 = .value (env, i2) at hone80
  change ∀ env, Operation.memset (.value (q.identity.add 120#64)) (.value 0#8)
    (.value 40#64) env i2 = .value (env, identityStoreState t q.identity) at hzero120
  change p.pointMulByPow2 _ s3 = .value (.nil, t) at hmul
  have hb : (program.bb2 p).run program.blockParams E s =
      .value ((pointBlockEnv E q small, .inr (if small then 12 else 4)), u) := by
    cases small <;>
      simp [BasicBlock.run, program.bb2, pointBlockEnv,
        List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, Operation.icmp,
        EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
        Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
        Env.writeMany_cons, Env.writeMany_nil, choiceByte,
        GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
        ho, h29r, h30r, hpr, hcr, hir, h1r, h3, h0, h40, h80, h120, herr, h8, h6, h160,
        hg8, hg6a, hg6b, hc1, hc2, hc3, hmul, hzero0, hg40, hg80, hg120,
        hone40, hone80, hzero120, heq, throwUBIf]
  rw [Func.runFrom_eq, block_2, hb]
  rfl

/-- The independent stack destinations and the read-only one constant. -/
structure PointDisjoint (q : PointPointers) : Prop where
  first : q.slot29.id ≠ q.option.id
  second : q.slot30.id ≠ q.slot29.id
  third : q.point.id ≠ q.slot30.id
  cofactorPoint : q.cofactor.id ≠ q.point.id
  cofactorIdentity : q.cofactor.id ≠ q.identity.id
  oneSlot29 : q.one.id ≠ q.slot29.id
  oneSlot30 : q.one.id ≠ q.slot30.id
  onePoint : q.one.id ≠ q.point.id
  oneCofactor : q.one.id ≠ q.cofactor.id
  oneIdentity : q.one.id ≠ q.identity.id

/-- Frame of block 2, exposing its five concrete writable objects. The
predicate describes only live ranges and bytes, never verifier execution. -/
structure PointCheckFrame (before after : GlobalState) (q : PointPointers) : Prop where
  wellFormed : after.WF
  live : ∀ (ptr : Pointer) (n : Nat),
    SmallRange before.mem ptr n → SmallRange after.mem ptr n
  read : ∀ (ptr : Pointer) (w : Nat),
    (Range.of ptr w).Disjoint (Range.of (q.slot29.add 6#64) 1280) →
    (Range.of ptr w).Disjoint (Range.of (q.slot30.add 6#64) 1280) →
    (Range.of ptr w).Disjoint (Range.of q.point 1280) →
    (Range.of ptr w).Disjoint (Range.of q.cofactor 1280) →
    (Range.of ptr w).Disjoint (Range.of q.identity 1280) →
    after.mem.readAt ptr w = before.mem.readAt ptr w

/-- Local cofactor and exact-Choice contracts determine the actual decoded-R
branch. The payload may encode any point returned by decompression, including
a point of small order. -/
theorem point_check_of_contracts {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (hidentity : layout.identity = identityBytes)
    (hmul : CofactorContract p.pointMulByPow2 layout)
    (hequal : SmallOrderEqContract p.pointConstantTimeEq layout shared)
    (q : PointPointers) (E : Env program.Γ) (state : GlobalState) (point : Point)
    (hregs : PointRegisters q E) (hwf : state.WF)
    (hout : SmallRange state.mem q.option 168)
    (h29 : SmallRange state.mem q.slot29 166)
    (h30 : SmallRange state.mem q.slot30 166)
    (hp : SmallRange state.mem q.point 160)
    (hco : SmallRange state.mem q.cofactor 160)
    (hid : SmallRange state.mem q.identity 160)
    (hpayload : ReadBytes state (q.option.add 8#64) 160 (layout.point point))
    (hone : ReadBytes state q.one 40 (1#320)) (hd : PointDisjoint q) :
    ∃ after, PointCheckFrame state after q ∧
      (program p g).runFrom E 2 state =
        (program p g).runFrom (pointBlockEnv E q (shared.smallOrder point))
          (if shared.smallOrder point then 12 else 4) after := by
  let copied := optionCopyState state q.option q.slot29 q.slot30 q.point
  have hcopied := option_copy_readback state q.option q.slot29 q.slot30 q.point
    (layout.point point) hpayload h29 h30 hp
  have honeCopied : ReadBytes copied q.one 40 (1#320) :=
    ⟨option_copy_live state q.option q.slot29 q.slot30 q.point q.one 40 hone.1,
      (option_copy_read_frame state q.option q.slot29 q.slot30 q.point q.one 320
        (Range.disjoint_of_id_ne hd.oneSlot29) (Range.disjoint_of_id_ne hd.oneSlot30)
        (Range.disjoint_of_id_ne hd.onePoint)).trans hone.2⟩
  obtain ⟨middle, hmcall, hmframe, hmread⟩ := hmul q.cofactor q.point copied point
    (option_copy_wf state q.option q.slot29 q.slot30 q.point hwf)
    (option_copy_live state q.option q.slot29 q.slot30 q.point q.cofactor 160 hco)
    hcopied (Range.disjoint_of_id_ne hd.cofactorPoint)
  have hmidId := hmframe.live q.identity 160
    (option_copy_live state q.option q.slot29 q.slot30 q.point q.identity 160 hid)
  have hmidOne := OutputFrame.readBytes copied middle q.cofactor q.one 160 40 (1#320)
    hmframe honeCopied (Range.disjoint_of_id_ne hd.oneCofactor)
  have hif := identity_frame middle q.identity hmframe.wellFormed hmidId
  have hir : ReadBytes (identityStoreState middle q.identity) q.identity 160 layout.identity := by
    rw [hidentity]
    exact identity_readback middle q.identity hmidId
  have hcoAfter := OutputFrame.readBytes middle (identityStoreState middle q.identity)
    q.identity q.cofactor 160 160 (layout.cofactor point) hif hmread
    (Range.disjoint_of_id_ne hd.cofactorIdentity)
  obtain ⟨after, hecall, heframe⟩ := hequal q.cofactor q.identity
    (identityStoreState middle q.identity) point hif.wellFormed hcoAfter hir
  refine ⟨after, ?_, ?_⟩
  · refine ⟨heframe.wellFormed, ?_, ?_⟩
    · intro ptr n hn
      exact heframe.live ptr n (hif.live ptr n (hmframe.live ptr n
        (option_copy_live state q.option q.slot29 q.slot30 q.point ptr n hn)))
    · intro ptr w h29d h30d hpd hcd hid
      exact (heframe.read ptr w).trans ((hif.read ptr w hid).trans
        ((hmframe.read ptr w hcd).trans
          (option_copy_read_frame state q.option q.slot29 q.slot30 q.point ptr w h29d h30d hpd)))
  · exact point_check_block p g E q state middle after (shared.smallOrder point)
      hregs hout h29 h30 hp (Range.disjoint_of_id_ne hd.first)
      (Range.disjoint_of_id_ne hd.second) (Range.disjoint_of_id_ne hd.third)
      hmcall hmidId hmidOne.1.fits hmidOne.2 (Ne.symm hd.oneIdentity) hecall

end Agave.Ed25519.Verifier.Execution.Dalek
