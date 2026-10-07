import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialSetupMemory
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialReturnRefinement

/-! The contextual constructor interface closes block 16 through the first
ladder entry. Only globals read by this block and its constructor are required. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open SerialContracts (WritesOnly readPoint readCached readProjective)
open Tables.SerialConstructorContext (ContextualTableContract)
set_option maxRecDepth 10000

/-- Exact table construction and identity setup, together with separate
write frames for both real destinations and the final dynamic-table meaning. -/
theorem serial_setup_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals)
    (htable : ContextualTableContract d2 p.call0)
    (E : ⟪serialKernel.Γ⟫) (slots : SerialSetupSlots)
    (table input : Pointer) (pos : Fin 256) (s : GlobalState)
    (hwf : s.WF) (harg : E.args 2 = .value input)
    (hd2 : Tables.SerialConstructorContext.GlobalsReady d2 s)
    (hid : SerialIdentityReady g.address0 s)
    (ht : Buffer s.mem table 1280) (ha : Buffer s.mem input 160)
    (hta : SerialContracts.Disjoint table 1280 input 160)
    (hA : SerialPoint.PointTight (readPoint s input))
    (hslots : ∀ i, Buffer s.mem (slots i) 120)
    (hpt : (slots 6).id ≠ table.id) :
    ∃ t : GlobalState,
      (serialKernel p g).runFrom (serialSetupInput E slots table g.address0 pos) 16 s =
        (serialKernel p g).runFrom (serialSetupResult E slots table g.address0 pos) 18
          (serialIdentityState t (slots 6)) ∧
      WritesOnly table 1280 s t ∧
      WritesOnly (slots 6) 120 t (serialIdentityState t (slots 6)) ∧
      readProjective (serialIdentityState t (slots 6)) (slots 6) = serialIdentityPoint ∧
      Tables.SerialConstructorContext.GlobalsReady d2 (serialIdentityState t (slots 6)) ∧
      SerialIdentityReady g.address0 (serialIdentityState t (slots 6)) ∧
      ∀ k : Fin 8,
        SerialPoint.PointBounded (readCached (serialIdentityState t (slots 6))
          (table.add (BitVec.ofNat 64 (160*k.val)))) ∧
        SerialPoint.pointValue (readCached (serialIdentityState t (slots 6))
          (table.add (BitVec.ofNat 64 (160*k.val)))) =
            PointArithmetic.serialCache _root_.Ed25519.d
              (Tables.serialWidth5 _root_.Ed25519.d
                (SerialPoint.pointValue (readPoint s input)) k) := by
  obtain ⟨t, hcall, hframe, hvalues⟩ := htable s table input hd2 hwf ht ha hta hA
  have hslots' (i : Fin 7) := hframe.smallRange (hslots i)
  have hid' := hid.writesOnly hframe
    (Range.disjoint_of_id_ne (hid.separate ht (by decide)).symm)
  have hd2' := hd2.writesOnly hframe
    (Range.disjoint_of_id_ne (hd2.separate ht (by decide)).symm)
  have hf := serialIdentity_frame t (slots 6) hframe.wellFormed (hslots' 6)
  refine ⟨t, ?_, hframe, hf, serialIdentity_readProjective t (slots 6) (hslots' 6),
    hd2'.writesOnly hf (Range.disjoint_of_id_ne (hd2'.separate (hslots' 6) (by decide)).symm),
    hid'.writesOnly hf (Range.disjoint_of_id_ne (hid'.separate (hslots' 6) (by decide)).symm), ?_⟩
  · rw [Func.runFrom_eq,
      show (serialKernel p g).blocks 16 = serialKernel.bb16 p from rfl,
      serial_setup_block p E slots table g.address0 input pos s t harg hcall hslots'
        hid'.buffer hid'.read (hid'.separate (hslots' 6) (by decide))]
    simp only [PoisonOr.value_bind, Func.continue]
  · intro k
    rw [serialIdentity_readCached_ne t (slots 6) _
      (by simpa only [Pointer.add_id] using hpt)]
    exact hvalues k

/-- The two actual write frames compose for every untouched caller read. -/
theorem serial_setup_read_frame (s t : GlobalState) (table projective : Pointer)
    (ht : WritesOnly table 1280 s t) (hwf : t.WF) (hp : Buffer t.mem projective 120)
    (q : Pointer) (bits : Nat)
    (hqt : (Range.of q bits).Disjoint (Range.of table (8*1280)))
    (hqp : (Range.of q bits).Disjoint (Range.of projective (8*120))) :
    (serialIdentityState t projective).mem.readAt q bits = s.mem.readAt q bits :=
  ((serialIdentity_frame t projective hwf hp).readFrame q bits hqp).trans (ht.readFrame q bits hqt)

/-- The initialized three-coordinate accumulator represents the neutral point. -/
theorem serialIdentity_represents : ProjectiveRepresents serialIdentityPoint 0 := by
  refine ⟨identityPoint, represents_identity, ?_, ?_, ?_⟩
  all_goals norm_num [serialIdentityPoint, SerialPoint.pointValue, SerialPoint.value,
    SerialFieldMul.decode, identityPoint] <;> rfl

end Agave.Ed25519.DoubleBase.RIR
