import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialLadder
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialSetupReady
import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyExecutionMemory

/-! Whole serial execution from the original entry through actual call-frame
 erasure. All point arithmetic and loop obligations are discharged. The one
 remaining helper premise is the contextual, concrete table constructor. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open SerialContracts (WritesOnly readPoint)
open Verifier.Execution
set_option maxRecDepth 10000

structure SerialCallerFrame (before after : GlobalState) (out : Pointer) : Prop where
  wellFormed : after.WF
  live : ∀ q bytes, Buffer before.mem q bytes → Buffer after.mem q bytes
  read : ∀ q bits, q.id.id < before.alloc.nextFreeBlock →
    (Range.of q bits).Disjoint (Range.of out 1280) →
    after.mem.readAt q bits = before.mem.readAt q bits

theorem serialStack_separate_old {q : Pointer} {s : GlobalState} (hq : q.id.id < s.alloc.nextFreeBlock) (n : Nat) :
    (serialStackPtr s n).id ≠ q.id := by
  intro he
  have hid := congrArg BlockId.id he
  rw [serialStackPtr_id] at hid
  omega

theorem serialStack_read_old (hq : q.id.id < s.alloc.nextFreeBlock) (n bits : Nat) :
    (serialStack s n).mem.readAt q bits = s.mem.readAt q bits := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((serialStack s n).alloca _).mem.readAt q bits = _
      rw [show ((serialStack s n).alloca _).mem.readAt q bits =
        (serialStack s n).mem.readAt q bits by
          simp only [MemoryState.readAt, GlobalState.getElem?_alloca
            (serialStack_separate_old hq n).symm]]
      exact ih

theorem serialNAFState8_read_old (s : GlobalState) (a b : BitVec 256)
    (hq : q.id.id < s.alloc.nextFreeBlock) (bits : Nat) :
    (serialNAFState8 s a b).mem.readAt q bits = s.mem.readAt q bits := by
  rw [serialNAFState8_read_other _ _ _ _ _
    (serialStack_separate_old hq 10) (serialStack_separate_old hq 0),
    serialNAFState5_read_other _ _ _ _
    (serialStack_separate_old hq 11) (serialStack_separate_old hq 1), serialStack_read_old hq]

private theorem serial_read_erased_new (m : MemoryState) (q : Pointer) (bits : Nat)
    (hq : cutoff ≤ q.id.id) : (m.eraseFrom cutoff).readAt q bits = 0 := by
  simp [MemoryState.readAt, MemoryState.eraseFrom, MemoryState.getElem?_eq,
    Std.ExtHashMap.getElem?_filter', show ¬q.id.id < cutoff by omega]

theorem SerialCallerFrame.erase (hwf : before.WF) (h : SerialCallerFrame before after out) :
    Dalek.OutputFrame before {after with mem := after.mem.eraseFrom before.alloc.nextFreeBlock}
      out 160 := by
  refine ⟨?_, ?_, ?_⟩
  · intro id hi
    exact h.wellFormed id (Std.ExtHashMap.mem_filter.mp hi).1
  · intro q bytes hq
    exact Key.erase_range (h.live q bytes hq) (hwf.lt hq.fits.mem)
  · intro q bits hd
    by_cases hq : q.id.id < before.alloc.nextFreeBlock
    · rw [Key.erase_read after.mem q _ bits hq]
      exact h.read q bits hq hd
    · rw [serial_read_erased_new after.mem q bits (by omega), ← hwf.eraseFrom]
      exact (serial_read_erased_new before.mem q bits (by omega)).symm

/-- Exact complete execution of the linked serial backend. Initial bytes,
scalar bounds, point representation, globals and the constructor leaf are
sufficient; no intermediate state, loop or success premise is supplied. -/
theorem serialLinked_run_validPoint (g : SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : SerialPanic)
    (htable : Tables.SerialConstructorContext.ContextualTableContract d2
      (serialLinkedPrimitives d2 panic).call0)
    (i : SerialContracts.Invocation) (s : GlobalState) (a b : BitVec 256)
    (P : SerialPoint.LimbPoint) (A : GroupPoint)
    (hinput : SerialContracts.InputState i s a b P)
    (hrep : Tables.Represents (SerialPoint.pointValue P) A)
    (hd2 : Tables.SerialConstructorContext.GlobalsReady d2 s)
    (hg : SerialContracts.GlobalsReady g s) :
    ∃ (Q : ValidPoint) (final : GlobalState),
      (serialLinkedKernel g d2 panic).run i.args s = .value (.nil, final) ∧
      SerialCallerFrame s final i.output ∧
      Q.curve = (a.toNat : Int) • A + (b.toNat : Int) • Tables.baseGroup ∧
      Dalek.ReadBytes final i.output 160 Q.bytes := by
  let E : ⟪serialKernel.Γ⟫ := Env.init i.args.get
  obtain ⟨F, t, hprefix, hframe, ht, hidframe, hid, _, _, hvalues⟩ :=
    serial_prepare_setup (serialLinkedPrimitives d2 panic) g d2 htable E s
      i.scalarA i.scalarB i.pointA a b hinput.wellFormed hinput.scalarA hinput.scalarB
      hinput.bytesA hinput.bytesB
      (by simp [E, Env.init, SerialContracts.Invocation.args])
      (by simp [E, Env.init, SerialContracts.Invocation.args])
      (by simp [E, Env.init, SerialContracts.Invocation.args])
      hinput.pointA (hinput.limbsA.symm ▸ hinput.pointTight) hd2
      ⟨hg.identityOffset, hg.identity⟩
  let EL := serialSetupResult F (serialStackSetupSlots s) (serialStackPtr s 9)
    g.address0 (serialScalarStartIndex a b)
  let st := serialIdentityState t (serialStackPtr s 8)
  have hr := serialSetup_ladderRegisters E F g s (serialScalarStartIndex a b) hframe
  have hm := serialSetup_ladderMemory s t a b g hinput.wellFormed hg
    (readPoint s i.pointA) A (hinput.limbsA.symm ▸ hrep) ht hvalues
  have hout : Buffer st.mem i.output 160 := hidframe.smallRange
    (ht.smallRange (serialNAFState8_buffer (serialStack_existing hinput.wellFormed hinput.output 12)))
  have harg : EL.read (%arg0) = .value i.output := by
    simp only [EL, serialSetupResult, serialSetupInput, Env.read, Env.write_args]
    rw [hframe.1]
    simp [serialInitial5, serialEntryEnv, E, Env.init, SerialContracts.Invocation.args]
  obtain ⟨Q, final, hrun, hwf, hmono, hshape, hcurve, hbytes, hread⟩ :=
    serialLinked_ladder_run_validPoint g d2 panic hr
      (by simp [serialSetupResult, serialScalarStartIndex, mlir_env]) hm
      ⟨hid.symm ▸ serialIdentity_pointTight, hid.symm ▸ serialIdentity_represents⟩
      hinput.scalarABound hinput.scalarBBound i.output hout
      (serialStack_separate_caller hinput.wellFormed hinput.output 8).symm harg
  refine ⟨Q, final, ?_, ⟨hwf, ?_, ?_⟩, hcurve, hbytes⟩
  · change (serialKernel (serialLinkedPrimitives d2 panic) g).runFrom E (0 : Fin 36) s = _
    exact hprefix.trans hrun
  · intro q bytes hq
    have hb := hidframe.smallRange
      (ht.smallRange (serialNAFState8_buffer (a := a) (b := b)
        (serialStack_existing hinput.wellFormed hq 12)))
    obtain ⟨block, hblock, hsmall, hrange⟩ := hb
    have he := hshape q.id
    rw [hblock] at he
    cases hf : final.mem[q.id]? with
    | none => simp [hf] at he
    | some block' =>
        have hlen : block'.length = block.length := by simpa [hf] using he
        exact ⟨block', hf, by omega, by omega⟩
  · intro q bits hq hd
    rw [hread q bits (fun j => serialStack_separate_old hq (j.val + 2)) hd,
      hidframe.readFrame q bits (Range.disjoint_of_id_ne (serialStack_separate_old hq 8).symm),
      ht.readFrame q bits (Range.disjoint_of_id_ne (serialStack_separate_old hq 9).symm)]
    exact serialNAFState8_read_old s a b hq bits

/-- The outer call erases its actual stack and preserves every caller read
outside the 160-byte result, including reads of absent blocks. -/
theorem serialLinked_call_validPoint (g : SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : SerialPanic)
    (htable : Tables.SerialConstructorContext.ContextualTableContract d2
      (serialLinkedPrimitives d2 panic).call0)
    (i : SerialContracts.Invocation) (s : GlobalState) (a b : BitVec 256)
    (P : SerialPoint.LimbPoint) (A : GroupPoint)
    (hinput : SerialContracts.InputState i s a b P)
    (hrep : Tables.Represents (SerialPoint.pointValue P) A)
    (hd2 : Tables.SerialConstructorContext.GlobalsReady d2 s)
    (hg : SerialContracts.GlobalsReady g s) :
    ∃ (Q : ValidPoint) (after : GlobalState),
      (serialLinkedKernel g d2 panic).call i.args s = .value (.nil, after) ∧
      Dalek.OutputFrame s after i.output 160 ∧
      Q.curve = (a.toNat : Int) • A + (b.toNat : Int) • Tables.baseGroup ∧
      Dalek.ReadBytes after i.output 160 Q.bytes := by
  obtain ⟨Q, final, hrun, hframe, hcurve, hbytes⟩ :=
    serialLinked_run_validPoint g d2 panic htable i s a b P A hinput hrep hd2 hg
  have hcaller := hinput.wellFormed.lt hinput.output.fits.mem
  exact ⟨Q, _, Func.call_of_run hrun, hframe.erase hinput.wellFormed, hcurve,
    Key.erase_range hbytes.1 hcaller,
    (Key.erase_read final.mem i.output s.alloc.nextFreeBlock 1280 hcaller).trans hbytes.2⟩

end Agave.Ed25519.DoubleBase.RIR
