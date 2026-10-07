import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorEntry
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorReturn
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialLinked

/-! The exact serial table constructor, including its real helper calls,
seven loop iterations and call-frame erasure. -/
namespace Agave.Ed25519.Tables.SerialConstructorContract
open LeanMLIR.RIR
open DoubleBase.RIR (serialConstructorPrimitives PrefixEq)
open DoubleBase.SerialContracts (readPoint readCached)
open SerialConstructorStack
open SerialConstructorCallFrame (slots)
open SerialConstructorState (Frame)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
local instance : Fact (Nat.Prime SerialFieldMul.modulus) := ⟨prime_p⟩

/-- Only live caller ranges, tight input limbs, and contextual 2d readiness
are required; no successful execution or arithmetic helper contract is assumed. -/
theorem contextual_contract (g : SerialConstructor.Globals) :
    SerialConstructorContext.ContextualTableContract g
      (SerialConstructor.kernel serialConstructorPrimitives g).call := by
  intro s out input hg hwf ho hi _ hA
  let args : Vals [.ptr,.ptr] := .cons (.value out) (.cons (.value input) .nil)
  let E : ⟪SerialConstructor.kernel.Γ⟫ := Env.init args.get
  let p := serialConstructorPrimitives
  have hp : SerialCacheExecution.primitives p = p := rfl
  obtain ⟨F,t,hentry,hf,hft,hr,hzero,hs,hd,he0⟩ := SerialConstructorEntry.entry_run p g rfl E s input
    hwf hg hi hA (by simp [E,args,Env.init])
  have he : ∀ j : Fin 8, j.val ≤ 0 →
      readCached t (SerialConstructorStep.record (stackPtr s 7) j.val) =
        SerialConstructorArithmetic.entries (readPoint s input) j.val := by
    intro j hj
    have hz : j.val = 0 := by omega
    simpa [hz,SerialConstructorStep.record] using he0
  obtain ⟨G,u,hloop,hfg,hfu,hreg,hmem,hentries⟩ := SerialConstructorLoop.loop_run p g rfl
    (slots s) (stackPtr s 7) (readPoint s input) hA 7 0 (by decide) F t hr
    (fun _ => hzero) hs hd he
  have htotal : Frame (slots s) (stackPtr s 7) (stack s 8) u := hft.trans hfu
  have hout : NAF.Memory.Buffer u.mem out 1280 := htotal.buffer (stack_existing hwf ho 8)
  have hargs : G.read (%arg0) = .value out := by
    have hfg' := hf.trans (hfg.mono (by decide))
    change G.args 0 = .value out
    rw [hfg'.1]
    simp [initial,constants,E,args,Env.init,Env.write_args]
  have hentryMath : ∀ k : Fin 8,
      SerialPoint.PointBounded (readCached u (SerialConstructorStep.record (stackPtr s 7) k.val)) ∧
      SerialPoint.pointValue (readCached u (SerialConstructorStep.record (stackPtr s 7) k.val)) =
        PointArithmetic.serialCache (K := ZMod SerialFieldMul.modulus) _root_.Ed25519.d
          (serialWidth5 (K := ZMod SerialFieldMul.modulus) _root_.Ed25519.d
            (SerialPoint.pointValue (readPoint s input)) k) := by
    intro k
    rw [hentries k]
    exact SerialConstructorArithmetic.width5 _ hA k
  obtain ⟨hreturn,houtFrame,hvalues⟩ := SerialConstructorReturn.return_contract
    (SerialCacheExecution.primitives p) g G u out (stackPtr s 7) hmem.wf hout hmem.tableBuffer
    (stack_separate_caller hwf ho 7).symm hargs (SerialPoint.pointValue (readPoint s input)) hentryMath
  rw [hreg.returnInput] at hreturn
  let final := SerialConstructorReturn.copyState u out (stackPtr s 7)
  have hrun : (SerialConstructor.kernel p g).run args s = .value (.nil,final) := by
    change (SerialConstructor.kernel p g).runFrom E 0 s = _
    rw [← hp]
    exact hentry.trans (hloop.trans hreturn)
  let after : GlobalState := {final with mem := final.mem.eraseFrom s.alloc.nextFreeBlock}
  refine ⟨after, Func.call_of_run hrun,
    SerialConstructorCallFrame.caller_frame s u final out hwf htotal houtFrame, ?_⟩
  intro k
  have hcaller : (out.add (BitVec.ofNat 64 (160*k.val))).id.id < s.alloc.nextFreeBlock := by
    simpa only [Pointer.add_id] using hwf.lt ho.fits.mem
  rw [SerialConstructorCallFrame.erase_cached s final _ hcaller]
  exact hvalues k

/-- The serial double-base call0 is exactly the constructor just proved. -/
theorem linked_contract (g : SerialConstructor.Globals) (panic : DoubleBase.RIR.SerialPanic) :
    SerialConstructorContext.ContextualTableContract g
      (DoubleBase.RIR.serialLinkedPrimitives g panic).call0 := contextual_contract g

end Agave.Ed25519.Tables.SerialConstructorContract

open Lean in
run_cmd do
  for endpoint in [
      `Agave.Ed25519.Tables.SerialConstructorContract.contextual_contract,
      `Agave.Ed25519.Tables.SerialConstructorContract.linked_contract] do
    for dependency in (← collectAxioms endpoint) do
      unless [`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{endpoint} depends on forbidden axiom {dependency}"

#print axioms Agave.Ed25519.Tables.SerialConstructorContract.contextual_contract
#print axioms Agave.Ed25519.Tables.SerialConstructorContract.linked_contract
