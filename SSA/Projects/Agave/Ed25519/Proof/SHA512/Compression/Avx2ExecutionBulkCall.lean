import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkOddCall
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkZeroMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.FinalizationDispatchLinked

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization
open Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Every live block count follows the emitted parity split and returns the
streaming SHA-512 result, with all three private allocations erased. -/
theorem bulk_call (g : Globals) (mem : GlobalState) (chain data : Pointer) (count : BitVec 64)
    (hwf : mem.WF) (hc : SmallRange mem.mem chain 64)
    (hd : SmallRange mem.mem data (128*count.toNat))
    (hk : PairConstants mem.mem g.address0) (hchainK : chain.id ≠ g.address0.id)
    (hdis : (Range.of chain 512).Disjoint (Range.of data (8*(128*count.toNat)))) :
    (program g).call (bulkArgs chain data count) mem = .value (.nil, {
      alloc := ⟨mem.alloc.nextFreeBlock+3⟩,
      mem := mem.mem.storeAt chain (Spec.run (mem.mem.readAt chain 512)
        (readBytes mem.mem data (128*count.toNat)))}) := by
  have hb := compress_count_bound mem data count hd
  by_cases hz : count.toNat = 0
  · have heq : count = 0#64 := BitVec.eq_of_toNat_eq hz
    subst count
    have hh := bulk_zero_call g mem chain data hwf
    simpa only [bulkArgs,BitVec.toNat_ofNat,Nat.zero_mod,Nat.mul_zero,readBytes,List.ofFn_zero,
      Spec.run_empty,store_read_self] using hh
  by_cases h1 : count.toNat = 1
  · have heq : count = 1#64 := BitVec.eq_of_toNat_eq h1
    subst count
    exact count_one_call_spec g mem chain data hwf hc hd hk
  let k := count.toNat / 2 - 1
  have hpos : 0 < count.toNat/2 := by omega
  have hkval : k+1 = count.toNat/2 := by dsimp [k]; omega
  by_cases heven : count.toNat % 2 = 0
  · have hn : count.toNat = 2*(k+1) := by omega
    have heq : count = BitVec.ofNat 64 (2*(k+1)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      exact hn
    have hlen : 128*count.toNat = 256*(k+1) := by omega
    have hd' : SmallRange mem.mem data (256*(k+1)) := by simpa only [hlen] using hd
    rw [hlen,heq]
    exact bulk_even_call g mem chain data k hwf hc hd' hk (by omega)
  · have hn : count.toNat = 1+2*(k+1) := by omega
    have heq : count = BitVec.ofNat 64 (1+2*(k+1)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      exact hn
    have hd' : SmallRange mem.mem data (128*(1+2*(k+1))) := by simpa only [hn] using hd
    have hdis' : (Range.of chain 512).Disjoint (Range.of data (8*(128*(1+2*(k+1))))) :=
      by simpa only [hn] using hdis
    rw [hn,heq]
    exact bulk_odd_call g mem chain data k hwf hc hd' hk hchainK hdis' (by omega)

/-- The direct AVX2 backend discharges the dispatcher/finalizer's exact call interface. -/
theorem bulk_call_equation (g : CompressionGlobals) :
    Dispatch.Finalization.Avx2BulkCallEquation g := by
  intro mem chain data count hwf hc hd hk hchain hdis
  exact bulk_call ⟨g.constantsPtr⟩ mem chain data count hwf hc hd hk hchain hdis

theorem bulk_contract (g : CompressionGlobals) :
    CompressContractUnder g (program ⟨g.constantsPtr⟩).call Spec.compression :=
  Dispatch.Finalization.avx2_contract_of_call_equation g (bulk_call_equation g)

end Agave.Ed25519.SHA512.Execution.Avx2
