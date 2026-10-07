import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialSetupContextual

/-! Caller-state transport and composition of actual scalar preparation with
the contextual table/identity setup. All scratch facts come from allocations. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open SerialContracts (WritesOnly readPoint readCached readProjective)
open Tables.SerialConstructorContext (ContextualTableContract)
set_option maxRecDepth 10000

private theorem storeLoop_present (g : ByteGlobal) (id : BlockId) (width : Nat)
    (out : Pointer) (fuel pos : Nat) (st : NAF.State) (m : MemoryState)
    (h : g.Present id m) (hne : id ≠ out.id) :
    g.Present id (NAF.Memory.storeLoop width out fuel pos st m) := by
  induction fuel generalizing pos st m with
  | zero => exact h
  | succ fuel ih =>
      by_cases hp : pos < 256
      · rw [NAF.Memory.storeLoop, if_pos hp]
        dsimp only
        by_cases hd : (NAF.step width st).digit = 0
        · rw [if_pos hd]
          exact ih _ _ _ h
        · rw [if_neg hd]
          exact ih _ _ _ (h.storeAt (by simpa only [Pointer.add_id] using hne))
      · simpa only [NAF.Memory.storeLoop, if_neg hp] using h

private theorem serialStack_present (g : ByteGlobal) (id : BlockId)
    (s : GlobalState) (hwf : s.WF) (h : g.Present id s.mem) (n : Nat) :
    g.Present id (serialStack s n).mem := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.alloca (serialStack_wf hwf n)

private theorem nafInitialized_present (g : ByteGlobal) (id : BlockId)
    (s : GlobalState) (digits scratch : Pointer) (scalar : BitVec 256)
    (h : g.Present id s.mem) (hd : id ≠ digits.id) (hs : id ≠ scratch.id) :
    g.Present id (nafInitialized s digits scratch scalar).mem :=
  ((h.storeAt hd).storeAt (by simpa only [Pointer.add_id] using hs)).storeAt hs

/-- The emitted NAF writes preserve every pre-existing byte global. -/
theorem serialNAFState8_global (g : ByteGlobal) (id : BlockId)
    (s : GlobalState) (a b : BitVec 256) (hwf : s.WF)
    (h : g.Present id s.mem) (hsmall : g.length < 2^63) :
    g.Present id (serialNAFState8 s a b).mem := by
  have hbuf : Buffer s.mem (g.address id) g.length :=
    ⟨⟨g.length, g.bytes⟩, h, hsmall, by simp [ByteGlobal.address]⟩
  have hne (n : Nat) : id ≠ (serialStackPtr s n).id :=
    (serialStack_separate_caller hwf hbuf n).symm
  have hstack := serialStack_present g id s hwf h 12
  have h5 := storeLoop_present g id 5 (serialStackPtr s 11) 256 0 ⟨a.toNat, 0⟩ _
    (nafInitialized_present g id _ _ _ a hstack (hne 11) (hne 1)) (hne 11)
  exact storeLoop_present g id 8 (serialStackPtr s 10) 256 0 ⟨b.toNat, 0⟩ _
    (nafInitialized_present g id _ _ _ b h5 (hne 10) (hne 0)) (hne 10)

/-- Every pre-existing caller read survives stack allocation and both NAF loops. -/
theorem serialNAFState8_read_caller (s : GlobalState) (a b : BitVec 256)
    (q : Pointer) (bytes bits : Nat) (hwf : s.WF) (h : Buffer s.mem q bytes) :
    (serialNAFState8 s a b).mem.readAt q bits = s.mem.readAt q bits := by
  rw [serialNAFState8_read_other _ _ _ _ _
    (serialStack_separate_caller hwf h 10) (serialStack_separate_caller hwf h 0),
    serialNAFState5_read_other _ _ _ _
      (serialStack_separate_caller hwf h 11) (serialStack_separate_caller hwf h 1),
    serialStack_read_existing hwf h]

theorem serialNAFState8_readPoint (s : GlobalState) (a b : BitVec 256)
    (q : Pointer) (hwf : s.WF) (h : Buffer s.mem q 160) :
    readPoint (serialNAFState8 s a b) q = readPoint s q := by
  apply PointArithmetic.Extended.ext
  all_goals
    dsimp only [readPoint]
    unfold SerialContracts.readField SerialFieldMul.unsigned
    funext i
    unfold SerialFieldMul.readLimbs
    apply congrArg BitVec.toNat
    apply serialNAFState8_read_caller s a b _ 8 64 hwf
    first
    | simpa [Pointer.add_add, ← BitVec.ofNat_add] using
        h.slice (0 + 8*i.val) 8 (by have := i.isLt; omega)
    | simpa [Pointer.add_add, ← BitVec.ofNat_add] using
        h.slice (40 + 8*i.val) 8 (by have := i.isLt; omega)
    | simpa [Pointer.add_add, ← BitVec.ofNat_add] using
        h.slice (80 + 8*i.val) 8 (by have := i.isLt; omega)
    | simpa [Pointer.add_add, ← BitVec.ofNat_add] using
        h.slice (120 + 8*i.val) 8 (by have := i.isLt; omega)

theorem serialNAFState8_wellFormed (s : GlobalState) (a b : BitVec 256) (hwf : s.WF) :
    (serialNAFState8 s a b).WF :=
  emittedNAF_wf (nafSetup_wf (emittedNAF_wf (nafSetup_wf (serialStack_wf hwf 12))))

def serialStackSetupSlots (s : GlobalState) : SerialSetupSlots :=
  fun i => serialStackPtr s (i.val + 2)

def serialScalarStartIndex (a b : BitVec 256) : Fin 256 :=
  ⟨startIndex (nafDigits 5 a.toNat) (nafDigits 8 b.toNat) 255,
    by have := startIndex_le (nafDigits 5 a.toNat) (nafDigits 8 b.toNat) 255; omega⟩

theorem serialSetup_stack_buffers (s : GlobalState) (a b : BitVec 256) (hwf : s.WF)
    (i : Fin 7) : Buffer (serialNAFState8 s a b).mem (serialStackSetupSlots s i) 120 := by
  have hsize : 120 ≤ serialStackSize (i.val + 2) := by
    fin_cases i <;> decide
  have hsmall : serialStackSize (i.val + 2) < 2^63 := by
    fin_cases i <;> decide
  have hb := serialNAFState8_buffer (a := a) (b := b)
    (serialStack_buffer hwf (i.val + 2) 12 (by omega) hsmall)
  simpa only [serialStackSetupSlots, Pointer.add_zero] using hb.slice 0 120 hsize

/-- Complete execution of scalar preparation and contextual table setup from
the original entry. No successful inner run or scratch-layout premise is
supplied by the caller; all scratch ranges and separations are derived. -/
theorem serial_prepare_setup (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (htable : ContextualTableContract d2 p.call0)
    (E : ⟪serialKernel.Γ⟫) (s : GlobalState)
    (inputA inputB point : Pointer) (a b : BitVec 256)
    (hwf : s.WF) (hA : Buffer s.mem inputA 32) (hB : Buffer s.mem inputB 32)
    (ha : s.mem.readAt inputA 256 = a) (hb : s.mem.readAt inputB 256 = b)
    (hargA : E.args 1 = .value inputA) (hargB : E.args 3 = .value inputB)
    (hargP : E.args 2 = .value point) (hp : Buffer s.mem point 160)
    (hpoint : SerialPoint.PointTight (readPoint s point))
    (hd2 : Tables.SerialConstructorContext.GlobalsReady d2 s)
    (hid : SerialIdentityReady g.address0 s) :
    ∃ (F : ⟪serialKernel.Γ⟫) (t : GlobalState),
      (serialKernel p g).runFrom E 0 s =
        (serialKernel p g).runFrom
          (serialSetupResult F (serialStackSetupSlots s) (serialStackPtr s 9)
            g.address0 (serialScalarStartIndex a b)) 18
          (serialIdentityState t (serialStackPtr s 8)) ∧
      PrefixEq (serialInitial5 E g s) F 43 ∧
      WritesOnly (serialStackPtr s 9) 1280 (serialNAFState8 s a b) t ∧
      WritesOnly (serialStackPtr s 8) 120 t (serialIdentityState t (serialStackPtr s 8)) ∧
      readProjective (serialIdentityState t (serialStackPtr s 8)) (serialStackPtr s 8) =
        serialIdentityPoint ∧
      Tables.SerialConstructorContext.GlobalsReady d2 (serialIdentityState t (serialStackPtr s 8)) ∧
      SerialIdentityReady g.address0 (serialIdentityState t (serialStackPtr s 8)) ∧
      ∀ k : Fin 8,
        SerialPoint.PointBounded (readCached (serialIdentityState t (serialStackPtr s 8))
          ((serialStackPtr s 9).add (BitVec.ofNat 64 (160*k.val)))) ∧
        SerialPoint.pointValue (readCached (serialIdentityState t (serialStackPtr s 8))
          ((serialStackPtr s 9).add (BitVec.ofNat 64 (160*k.val)))) =
            PointArithmetic.serialCache _root_.Ed25519.d
              (Tables.serialWidth5 _root_.Ed25519.d
                (SerialPoint.pointValue (readPoint s point)) k) := by
  obtain ⟨F, hprefix, hpos, hframe, _, _⟩ :=
    serial_prepare_scalars p g E s inputA inputB a b hwf hA hB ha hb hargA hargB
  have harg : F.args 2 = .value point := by
    rw [hframe.1]
    simpa only [serialInitial5, serialEntryEnv, Env.write_args] using hargP
  have hd2' : Tables.SerialConstructorContext.GlobalsReady d2 (serialNAFState8 s a b) :=
    ⟨hd2.offsetZero, serialNAFState8_global _ _ s a b hwf hd2.present (by decide)⟩
  have hid' : SerialIdentityReady g.address0 (serialNAFState8 s a b) :=
    ⟨hid.offsetZero, serialNAFState8_global _ _ s a b hwf hid.present (by decide)⟩
  have htablebuf : Buffer (serialNAFState8 s a b).mem (serialStackPtr s 9) 1280 :=
    serialNAFState8_buffer (serialStack_buffer hwf 9 12 (by decide) (by decide))
  have hpointbuf : Buffer (serialNAFState8 s a b).mem point 160 :=
    serialNAFState8_buffer (serialStack_existing hwf hp 12)
  have hpointread := serialNAFState8_readPoint s a b point hwf hp
  obtain ⟨t, hsetup, ht, hi, hidentity, hd2final, hidfinal, hvalues⟩ :=
    serial_setup_run p g d2 htable F (serialStackSetupSlots s) (serialStackPtr s 9) point
      (serialScalarStartIndex a b) (serialNAFState8 s a b)
      (serialNAFState8_wellFormed s a b hwf) harg hd2' hid' htablebuf hpointbuf
      (Range.disjoint_of_id_ne (serialStack_separate_caller hwf hp 9))
      (hpointread.symm ▸ hpoint) (serialSetup_stack_buffers s a b hwf)
      (serialStack_separate s 8 9 (by decide))
  have hnorm : serialSetupInput F (serialStackSetupSlots s) (serialStackPtr s 9)
      g.address0 (serialScalarStartIndex a b) = F :=
    serialSetupInput_of_prefix E F g s (serialScalarStartIndex a b) hframe hpos
  rw [hnorm] at hsetup
  refine ⟨F, t, hprefix.trans hsetup, hframe, ht, hi, hidentity, hd2final, hidfinal, ?_⟩
  simpa [hpointread, serialStackSetupSlots] using hvalues

end Agave.Ed25519.DoubleBase.RIR
