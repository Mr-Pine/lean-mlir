import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorPrefix
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorLoop
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorReturn
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCallFrame
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Contracts

/-! The actual AVX2 width-five table constructor: normalized input, initial
cache and doubling, all seven source iterations, return memcpy, and caller
frame erasure. The resulting contract has no helper-execution assumption. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Contract
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases
open Avx2FieldMul.Execution (readBlocks)
open DoubleBase.ExecutionAvx2 (TableContract TableFrame packedPoint args2)
open State (slots Frame)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime SerialFieldMul.modulus) := ⟨prime_p⟩

/-- The unchanged imported constructor satisfies the ordinary eight-record
contract using only its live caller ranges and tight serial input limbs. -/
theorem contract : TableContract (kernel Double.actual).call := by
  intro out a s hwf ho ha _ htight
  let args := args2 out a
  let E : ⟪kernel.Γ⟫ := Env.init args.get
  let P := Normalization.normalizedPoint (Loads.point s.mem a)
  obtain ⟨F,t,hentry,hf,hft,hr,hzero,hs,hP,hvalue,hd,he0⟩ :=
    Prefix.entry_run E s a hwf ha htight (by rfl)
  have he : ∀ j : Fin 8, j.val ≤ 0 →
      readBlocks t.mem ((Stack.pointer s 8).add (BitVec.ofNat 64 (160*j.val))) =
        packPoint (Arithmetic.entries P j.val) := by
    intro j hj
    have hz : j.val = 0 := by omega
    simpa [hz] using he0
  obtain ⟨G,u,hloop,hfg,hfu,hreg,hmem,hentries⟩ :=
    Loop.loop_run (slots s) (Stack.pointer s 8) P hP 7 0 (by decide)
      F t hr (fun _ => hzero) hs hd he
  have htotal : Frame (slots s) (Stack.pointer s 8) (Stack.state s 9) u := hft.trans hfu
  have hout : NAF.Memory.Buffer u.mem out 1280 :=
    htotal.buffer (Stack.live hwf ho 9)
  have hargs : G.read (%arg0) = .value out := by
    change G.args 0 = .value out
    rw [hfg.arguments, hf.arguments]
    rfl
  have hentryMath : ∀ k : Fin 8,
      pointReduced (packedPoint u.mem ((Stack.pointer s 8).add (BitVec.ofNat 64 (160*k.val)))) ∧
      pointValue (packedPoint u.mem ((Stack.pointer s 8).add (BitVec.ofNat 64 (160*k.val)))) =
        PointArithmetic.avx2Cache (avx2Width5 (Conformance.BackendExecution.readPoint s a) k) := by
    intro k
    have hread : packedPoint u.mem ((Stack.pointer s 8).add (BitVec.ofNat 64 (160*k.val))) =
        Arithmetic.entries P k.val :=
      readPoint_of_packed (pointReduced_wide (Arithmetic.entries_reduced hP k.val))
        u.mem _ (hentries k)
    rw [hread, ← hvalue]
    exact Arithmetic.width5 hP k
  obtain ⟨hreturn,houtFrame,hvalues⟩ := Return.return_contract Double.actual G u out
    (Stack.pointer s 8) hmem.wf hout hmem.tableBuffer
    (Stack.separate_caller hwf ho 8).symm hargs
    (Conformance.BackendExecution.readPoint s a) hentryMath
  rw [hreg.returnInput] at hreturn
  let final := Return.copyState u out (Stack.pointer s 8)
  have hrun : (kernel Double.actual).run args s = .value (.nil,final) := by
    change (kernel Double.actual).runFrom E 0 s = _
    exact hentry.trans (hloop.trans hreturn)
  let after : GlobalState := {final with mem := final.mem.eraseFrom s.alloc.nextFreeBlock}
  refine ⟨after, Func.call_of_run hrun,
    CallFrame.caller_frame s u final out hwf htotal houtFrame, ?_⟩
  intro k
  have hcaller : (out.add (BitVec.ofNat 64 (160*k.val))).id.id < s.alloc.nextFreeBlock := by
    simpa only [Pointer.add_id] using hwf.lt ho.fits.mem
  rw [CallFrame.erase_packedPoint s final _ hcaller]
  exact hvalues k

/-- The double-base call0 is definitionally this checked constructor call. -/
theorem linked_contract (panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals [])) :
    TableContract (DoubleBase.ExecutionAvx2.linkedArithmetic (kernel Double.actual).call panic).call0 :=
  contract

/-- All three arithmetic helpers now have concrete imported implementations;
the panic effect remains a separate source-boundary parameter. -/
theorem linked_helpers (panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals [])) :
    DoubleBase.ExecutionAvx2.HelperContracts
      (DoubleBase.ExecutionAvx2.linkedArithmetic (kernel Double.actual).call panic) :=
  DoubleBase.ExecutionAvx2.linkedArithmetic_contracts _ panic contract

end Agave.Ed25519.Tables.Avx2Constructor.Contract

open Lean in
run_cmd do
  for endpoint in [
      `Agave.Ed25519.Tables.Avx2Constructor.Contract.contract,
      `Agave.Ed25519.Tables.Avx2Constructor.Contract.linked_contract,
      `Agave.Ed25519.Tables.Avx2Constructor.Contract.linked_helpers] do
    for dependency in (← collectAxioms endpoint) do
      unless [`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{endpoint} depends on forbidden axiom {dependency}"
    logInfo m!"standard-three audit passed: {endpoint}"
