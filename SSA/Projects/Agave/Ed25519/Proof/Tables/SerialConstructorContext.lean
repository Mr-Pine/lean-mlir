import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructor
import SSA.Projects.Agave.Ed25519.Proof.Tables.ConstructorConstant
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialContracts

/-!
The actual serial constructor reads an immutable 40-byte 2d allocation. Its
contract must require that allocation at the call state. A universal contract
without this condition cannot be linked to a constructor with a fixed pointer.
-/
namespace Agave.Ed25519.Tables.SerialConstructorContext
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open DoubleBase.SerialContracts

structure GlobalsReady (g : SerialConstructor.Globals) (s : GlobalState) : Prop where
  offsetZero : g.address0.offset = 0
  present : serialD2Global.Present g.address0.id s.mem

theorem GlobalsReady.address (h : GlobalsReady g s) :
    g.address0 = serialD2Global.address g.address0.id := by
  cases hp : g.address0 with
  | mk id offset =>
      have ho := h.offsetZero
      simp only [hp] at ho
      subst offset
      rfl

theorem GlobalsReady.buffer (h : GlobalsReady g s) : SmallRange s.mem g.address0 40 := by
  rw [h.address]
  exact serialD2_buffer h.present

theorem GlobalsReady.words (h : GlobalsReady g s) :
    SerialFieldMul.readLimbs s g.address0 = serialD2Words := by
  rw [h.address]
  exact serialD2_read_words s g.address0.id h.present

theorem GlobalsReady.field (h : GlobalsReady g s) :
    readField s g.address0 = serialD2Limbs := by
  simp only [readField, h.words]
  rfl

/-- A point or table allocation cannot be the 40-byte constant allocation. -/
theorem GlobalsReady.separate (h : GlobalsReady g s)
    (hq : SmallRange s.mem q bytes) (hsize : 40 < bytes) :
    q.id ≠ g.address0.id := by
  intro heq
  obtain ⟨b, hb, _, hfit⟩ := hq
  rw [heq, h.present] at hb
  cases hb
  change q.offset.toNat + bytes ≤ 40 at hfit
  omega

theorem GlobalsReady.alloca (h : GlobalsReady g s) (hwf : s.WF) :
    GlobalsReady g (s.alloca n) :=
  ⟨h.offsetZero, h.present.alloca hwf⟩

theorem GlobalsReady.storeAt (h : GlobalsReady g s)
    (p : Pointer) (v : BitVec w) (hne : g.address0.id ≠ p.id) :
    GlobalsReady g {s with mem := s.mem.storeAt p v} :=
  ⟨h.offsetZero, h.present.storeAt hne⟩

/-- Preservation across independently proved helpers uses the actual caller
frame and disjointness from the immutable constant. -/
theorem GlobalsReady.writesOnly (h : GlobalsReady g before)
    (hf : WritesOnly out bytes before after)
    (hd : (Range.of g.address0 320).Disjoint (Range.of out (8 * bytes))) :
    GlobalsReady g after := by
  refine ⟨h.offsetZero, ?_⟩
  have hs := hf.allocationShape g.address0.id
  rw [h.present] at hs
  cases hb : after.mem[g.address0.id]? with
  | none => simp [hb] at hs
  | some b =>
      have hl : b.length = 40 := by simpa [hb, serialD2Global] using hs
      cases b with
      | mk n value =>
          dsimp only at hl
          subst n
          have hr := hf.readFrame g.address0 320 hd
          have hbefore : before.mem.readAt g.address0 320 = serialD2Bytes := by
            rw [h.address]
            exact h.present.readAt
          have hafter : after.mem.readAt g.address0 320 = value := by
            simp [MemoryState.readAt, hb, Pointer.offsetInBits, h.offsetZero]
          rw [hbefore, hafter] at hr
          subst value
          exact hb

/-- Pointwise contract with exact global readiness at the constructor call. -/
def ContextualTableContract (g : SerialConstructor.Globals)
    (helper : Vals [.ptr, .ptr] → EffectM (Vals [])) : Prop :=
  ∀ (s : GlobalState) (out input : Pointer), GlobalsReady g s →
    s.WF → SmallRange s.mem out 1280 → SmallRange s.mem input 160 →
    Disjoint out 1280 input 160 → SerialPoint.PointTight (readPoint s input) →
    ∃ final, helper (.cons (.value out) (.cons (.value input) .nil)) s =
      .value (.nil, final) ∧ WritesOnly out 1280 s final ∧
      ∀ k : Fin 8,
        SerialPoint.PointBounded (readCached final (out.add (BitVec.ofNat 64 (160 * k.val)))) ∧
        SerialPoint.pointValue (readCached final (out.add (BitVec.ofNat 64 (160 * k.val)))) =
          PointArithmetic.serialCache _root_.Ed25519.d
            (serialWidth5 _root_.Ed25519.d (SerialPoint.pointValue (readPoint s input)) k)

/-- Unconditional abstract helpers still instantiate the contextual interface. -/
theorem contextual_of_unconditional (h : TableContract helper) :
    ContextualTableContract g helper := by
  intro s out input _
  exact h s out input

end Agave.Ed25519.Tables.SerialConstructorContext
