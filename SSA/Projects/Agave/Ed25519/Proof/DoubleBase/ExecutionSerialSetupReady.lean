import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialSetupStatic

/-! Concrete register and memory readiness at the first serial ladder entry. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open SerialContracts (WritesOnly readPoint readCached)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The actual setup result has all persistent compiler registers required by
every ladder arm, independently of the scalar-dependent temporary registers. -/
theorem serialSetup_ladderRegisters (E F : ⟪serialKernel.Γ⟫) (g : SerialCFG.Globals)
    (s : GlobalState) (pos : Fin 256) (hframe : PrefixEq (serialInitial5 E g s) F 43) :
    SerialLadderRegisters (serialStackSetupSlots s) (serialStackPtr s 9) g.address3
      (serialStackPtr s 11) (serialStackPtr s 10)
      (serialSetupResult F (serialStackSetupSlots s) (serialStackPtr s 9) g.address0 pos) := by
  constructor
  all_goals
    simp [serialSetupResult, serialSetupInput, serialStackSetupSlots, mlir_env]
  all_goals first
    | rfl
    | (rw [hframe.read _ (by intro i ht he; cases he; decide)]
       simp [serialInitial5, serialEntryEnv, mlir_env])

/-- A framed helper preserves a whole concrete global's length and bytes. -/
theorem setup_global_writesOnly (g : ByteGlobal) (id : BlockId)
    (h : g.Present id s.mem) (hf : WritesOnly out bytes s t)
    (hd : (Range.of (g.address id) (8*g.length)).Disjoint (Range.of out (8*bytes))) :
    g.Present id t.mem := by
  have hs := hf.allocationShape id
  rw [h] at hs
  cases hb : t.mem[id]? with
  | none => simp [hb] at hs
  | some block =>
      have hl : block.length = g.length := by simpa [hb] using hs
      cases block with
      | mk n value =>
          dsimp only at hl
          subst n
          have hr := hf.readFrame (g.address id) (8*g.length) hd
          have hv : t.mem.readAt (g.address id) (8*g.length) = value := by
            simp [MemoryState.readAt, hb, Pointer.offsetInBits, ByteGlobal.address]
          rw [h.readAt, hv] at hr
          subst value
          exact hb

/-- Readiness uses the constructor's checked output and frame, the initial
base-table bytes, and the initial point's mathematical representation. -/
theorem serialSetup_ladderMemory (s t : GlobalState) (a b : BitVec 256)
    (g : SerialCFG.Globals) (hwf : s.WF) (hg : SerialContracts.GlobalsReady g s)
    (P : SerialPoint.LimbPoint) (A : GroupPoint)
    (hP : Tables.Represents (SerialPoint.pointValue P) A)
    (ht : WritesOnly (serialStackPtr s 9) 1280 (serialNAFState8 s a b) t)
    (hvalues : ∀ k : Fin 8,
      SerialPoint.PointBounded (readCached (serialIdentityState t (serialStackPtr s 8))
        ((serialStackPtr s 9).add (BitVec.ofNat 64 (160*k.val)))) ∧
      SerialPoint.pointValue (readCached (serialIdentityState t (serialStackPtr s 8))
        ((serialStackPtr s 9).add (BitVec.ofNat 64 (160*k.val)))) =
          PointArithmetic.serialCache _root_.Ed25519.d
            (Tables.serialWidth5 _root_.Ed25519.d (SerialPoint.pointValue P) k)) :
    SerialLadderMemory (serialStackSetupSlots s) (serialStackPtr s 9) g.address3
      (serialStackPtr s 11) (serialStackPtr s 10) a.toNat b.toNat A Tables.baseGroup
      (serialIdentityState t (serialStackPtr s 8)) := by
  have haddr : g.address3 = Tables.serialBaseGlobal.address g.address3.id := by
    cases hp : g.address3 with
    | mk id offset =>
        have ho := hg.baseOffset
        simp only [hp] at ho
        subst offset
        rfl
  have hbasebuf : Buffer s.mem g.address3 7680 := by
    rw [haddr]
    exact Tables.Memory.serial_base_buffer hg.base
  have hbuffer (i : Nat) (hi : i < 12) (hs : serialStackSize i < 2^63) :
      Buffer t.mem (serialStackPtr s i) (serialStackSize i) :=
    ht.smallRange (serialNAFState8_buffer (serialStack_buffer hwf i 12 hi hs))
  have hproj : Buffer t.mem (serialStackPtr s 8) 120 := hbuffer 8 (by decide) (by decide)
  have hi := serialIdentity_frame t (serialStackPtr s 8) ht.wellFormed hproj
  have hbaseNAF := serialNAFState8_global _ _ s a b hwf hg.base (by decide)
  have hbaseT := setup_global_writesOnly _ _ hbaseNAF ht
    (Range.disjoint_of_id_ne (by
      simpa only [ByteGlobal.address] using (serialStack_separate_caller hwf hbasebuf 9).symm))
  have hbase := setup_global_writesOnly _ _ hbaseT hi
    (Range.disjoint_of_id_ne (by
      simpa only [ByteGlobal.address] using (serialStack_separate_caller hwf hbasebuf 8).symm))
  refine ⟨hi.wellFormed, ?_, hi.smallRange (hbuffer 9 (by decide) (by decide)),
    ?_, hi.smallRange (hbuffer 11 (by decide) (by decide)),
    hi.smallRange (hbuffer 10 (by decide) (by decide)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hs : serialStackSize (i.val+2) = serialScratchBytes i := by
      fin_cases i <;> rfl
    have hb := hi.smallRange (hbuffer (i.val+2) (by omega) (by fin_cases i <;> decide))
    rw [hs] at hb
    exact hb
  · rw [haddr]
    exact Tables.Memory.serial_base_buffer hbase
  · intro i j hne
    apply serialStack_separate
    intro heq
    apply hne
    apply Fin.ext
    omega
  · intro i
    exact serialStack_separate s (i.val+2) 9 (by omega)
  · intro i
    exact serialStack_separate_caller hwf hbasebuf (i.val+2)
  · intro i
    exact serialStack_separate s (i.val+2) 11 (by omega)
  · intro i
    exact serialStack_separate s (i.val+2) 10 (by omega)
  · intro i
    rw [hi.readFrame _ _ (Range.disjoint_of_id_ne (by
      simpa only [Pointer.add_id] using serialStack_separate s 11 8 (by decide))),
      ht.readFrame _ _ (Range.disjoint_of_id_ne (by
        simpa only [Pointer.add_id] using serialStack_separate s 11 9 (by decide)))]
    exact (serialNAFState8_sourceDigits s a b hwf).1 i
  · intro i
    rw [hi.readFrame _ _ (Range.disjoint_of_id_ne (by
      simpa only [Pointer.add_id] using serialStack_separate s 10 8 (by decide))),
      ht.readFrame _ _ (Range.disjoint_of_id_ne (by
        simpa only [Pointer.add_id] using serialStack_separate s 10 9 (by decide)))]
    exact (serialNAFState8_sourceDigits s a b hwf).2 i
  · intro k
    exact ⟨(hvalues k).1, Tables.serialWidth5 _root_.Ed25519.d (SerialPoint.pointValue P) k,
      Tables.serialOdd_represents hP k.val, (hvalues k).2⟩
  · intro k
    rw [haddr]
    exact serialBase_cache_ready _ _ hbase k

/-- Original entry to the first doubling, ready for the proved inclusive
ladder. The sole helper boundary is the contextual table-constructor contract. -/
theorem serial_prepare_ladder (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals)
    (htable : Tables.SerialConstructorContext.ContextualTableContract d2 p.call0)
    (E : ⟪serialKernel.Γ⟫) (s : GlobalState)
    (inputA inputB point : Pointer) (a b : BitVec 256) (A : GroupPoint)
    (hwf : s.WF) (hA : Buffer s.mem inputA 32) (hB : Buffer s.mem inputB 32)
    (ha : s.mem.readAt inputA 256 = a) (hb : s.mem.readAt inputB 256 = b)
    (hargA : E.args 1 = .value inputA) (hargB : E.args 3 = .value inputB)
    (hargP : E.args 2 = .value point) (hp : Buffer s.mem point 160)
    (hpoint : SerialPoint.PointTight (readPoint s point))
    (hrep : Tables.Represents (SerialPoint.pointValue (readPoint s point)) A)
    (hd2 : Tables.SerialConstructorContext.GlobalsReady d2 s)
    (hg : SerialContracts.GlobalsReady g s) :
    ∃ (F : ⟪serialKernel.Γ⟫) (t : GlobalState),
      let outEnv := serialSetupResult F (serialStackSetupSlots s) (serialStackPtr s 9)
        g.address0 (serialScalarStartIndex a b)
      let outState := serialIdentityState t (serialStackPtr s 8)
      (serialKernel p g).runFrom E 0 s = (serialKernel p g).runFrom outEnv 18 outState ∧
      SerialLadderRegisters (serialStackSetupSlots s) (serialStackPtr s 9) g.address3
        (serialStackPtr s 11) (serialStackPtr s 10) outEnv ∧
      outEnv.read (%131) = .value (BitVec.ofNat 64 (serialScalarStartIndex a b).val) ∧
      SerialLadderMemory (serialStackSetupSlots s) (serialStackPtr s 9) g.address3
        (serialStackPtr s 11) (serialStackPtr s 10) a.toNat b.toNat A Tables.baseGroup outState ∧
      SerialPoint.PointTight (SerialContracts.readProjective outState (serialStackPtr s 8)) ∧
      ProjectiveRepresents (SerialContracts.readProjective outState (serialStackPtr s 8)) 0 ∧
      WritesOnly (serialStackPtr s 9) 1280 (serialNAFState8 s a b) t ∧
      WritesOnly (serialStackPtr s 8) 120 t outState := by
  obtain ⟨F, t, hrun, hframe, ht, hi, hid, _, _, hvalues⟩ :=
    serial_prepare_setup p g d2 htable E s inputA inputB point a b hwf hA hB ha hb
      hargA hargB hargP hp hpoint hd2 ⟨hg.identityOffset, hg.identity⟩
  refine ⟨F, t, hrun, serialSetup_ladderRegisters E F g s _ hframe, ?_,
    serialSetup_ladderMemory s t a b g hwf hg _ A hrep ht hvalues,
    hid.symm ▸ serialIdentity_pointTight, hid.symm ▸ serialIdentity_represents, ht, hi⟩
  simp [serialSetupResult, mlir_env]

end Agave.Ed25519.DoubleBase.RIR
