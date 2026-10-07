import SSA.Projects.Agave.Ed25519.Proof.Tables.ConstructorMemory
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2ContractDefs
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialContracts
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CallMemory

/-! The actual AVX2 constructor return copy transfers every packed record and
writes only the caller's output range. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Return
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open DoubleBase.SerialContracts (WritesOnly)
open DoubleBase.ExecutionAvx2 (packedPoint)
open Avx2FieldMul.Execution (readBlocks)
local instance : Fact (Nat.Prime SerialFieldMul.modulus) := ⟨prime_p⟩
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def copyState (s : GlobalState) (out table : Pointer) : GlobalState :=
  {s with mem := s.mem.storeAt out (s.mem.readAt table 10240)}

theorem copyState_writesOnly (s : GlobalState) (out table : Pointer) (hwf : s.WF) :
    WritesOnly out 1280 s (copyState s out table) := by
  refine ⟨hwf.storeAt, le_refl _, ?_, ?_⟩
  · intro id
    exact SerialPoint.Execution.storeAt_allocationShape s.mem out _ id
  · intro q bits hd
    exact MemoryState.readAt_storeAt_disjoint hd.symm _

/-- All five 256-bit blocks of each of the eight physical records are copied
exactly. The offset bounds come from the source and destination allocations. -/
theorem copyState_readBlocks (s : GlobalState) (out table : Pointer)
    (hout : SmallRange s.mem out 1280) (htable : SmallRange s.mem table 1280)
    (k : Fin 8) :
    readBlocks (copyState s out table).mem (out.add (BitVec.ofNat 64 (160*k.val))) =
      readBlocks s.mem (table.add (BitVec.ofNat 64 (160*k.val))) := by
  have hblock (i : Fin 5) :
      (copyState s out table).mem.readAt
          (out.add (BitVec.ofNat 64 (160*k.val + 32*i.val))) 256 =
        s.mem.readAt (table.add (BitVec.ofNat 64 (160*k.val + 32*i.val))) 256 := by
    have hk : 160*k.val + 32*i.val < 2^64 := by omega
    have hbits : (BitVec.ofNat 64 (160*k.val + 32*i.val)).toNat * 8 + 256 ≤ 10240 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
      omega
    unfold copyState
    rw [MemoryState.readAt_storeAt_add hout.fits
      (hout.no_wrap (k := 160*k.val + 32*i.val) (by omega)) hbits]
    exact (MemoryState.readAt_add_of_readAt htable.fits
      (htable.no_wrap (k := 160*k.val + 32*i.val) (by omega)) hbits rfl).symm
  funext i
  simp only [readBlocks, Pointer.add_add, ← BitVec.ofNat_add, hblock]

theorem copyState_packedPoint (s : GlobalState) (out table : Pointer)
    (hout : SmallRange s.mem out 1280) (htable : SmallRange s.mem table 1280)
    (k : Fin 8) :
    packedPoint (copyState s out table).mem (out.add (BitVec.ofNat 64 (160*k.val))) =
      packedPoint s.mem (table.add (BitVec.ofNat 64 (160*k.val))) := by
  simp only [packedPoint, copyState_readBlocks s out table hout htable k]

/-- Execute the unchanged return block and transfer the established table
contents to the caller's output. This does not assume return execution. -/
theorem return_contract (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (out table : Pointer)
    (hwf : s.WF) (hout : SmallRange s.mem out 1280) (htable : SmallRange s.mem table 1280)
    (hne : out.id ≠ table.id) (harg : E.read (%arg0) = .value out)
    (A : PointArithmetic.Extended (ZMod SerialFieldMul.modulus))
    (hentries : ∀ k : Fin 8,
      Avx2PointAdd.pointReduced (packedPoint s.mem (table.add (BitVec.ofNat 64 (160*k.val)))) ∧
      Avx2PointAdd.pointValue (packedPoint s.mem (table.add (BitVec.ofNat 64 (160*k.val)))) =
        PointArithmetic.avx2Cache (avx2Width5 A k)) :
    let final := copyState s out table
    (kernel p).runFrom (ConstructorMemory.avx2ReturnInput E table) 1 s =
      .value (.nil, final) ∧ WritesOnly out 1280 s final ∧
      ∀ k : Fin 8,
        Avx2PointAdd.pointReduced (packedPoint final.mem (out.add (BitVec.ofNat 64 (160*k.val)))) ∧
        Avx2PointAdd.pointValue (packedPoint final.mem (out.add (BitVec.ofNat 64 (160*k.val)))) =
          PointArithmetic.avx2Cache (avx2Width5 A k) := by
  refine ⟨ConstructorMemory.avx2_return_run p E s out table hout htable hne harg,
    copyState_writesOnly s out table hwf, ?_⟩
  intro k
  rw [copyState_packedPoint s out table hout htable k]
  exact hentries k

end Agave.Ed25519.Tables.Avx2Constructor.Return

open Lean in
run_cmd do
  for endpoint in [
      `Agave.Ed25519.Tables.Avx2Constructor.Return.return_contract,
      `Agave.Ed25519.Tables.Avx2Constructor.Return.copyState_readBlocks,
      `Agave.Ed25519.Tables.Avx2Constructor.Return.copyState_writesOnly] do
    for dependency in (← collectAxioms endpoint) do
      unless [`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{endpoint} depends on forbidden axiom {dependency}"
    logInfo m!"standard-three audit passed: {endpoint}"
