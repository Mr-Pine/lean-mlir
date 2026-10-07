import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.InitializerLink
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerParameterizedReady

/-!
The parameterized Firedancer SHA contracts can use exactly the independently
proved FIPS K64 data. No Firedancer SHA initializer body or round-constant
initializer is imported in this development: `HoldsGlobal` is the remaining
actual-loader obligation. The explicit `withGlobal` model demonstrates that
obligation is satisfiable and freshness supplies separation from the SHA
context. Neither the legacy signature-only programs nor their determinism
axioms are used by these results.
-/
namespace Agave.Ed25519.Bridge

open LeanMLIR SLLVM Firedancer Firedancer.Common
open Agave.Ed25519.SHA512.InitializerData
open Agave.Ed25519.Verifier.Execution.SHA512Finalization

/-- Native little-endian standard K64 bytes, proved equal to the pinned Agave
compiler global by `extracted_k64_eq`. -/
def sha512StandardK64 : BitVec (80 * 64) := k64Memory.bytes

theorem firedancer_source_k64_eq : k64Bytes = sha512StandardK64 := extracted_k64_eq

/-- A real Firedancer loader need only establish its symbol and concrete
pinned bytes; the values required by the standard contract follow. -/
theorem firedancerK64_standard_of_loaded (state : GlobalState) (q : Pointer)
    (hload : HoldsGlobal state "fd_sha512_core_ref.K" q k64Bytes) :
    HoldsGlobal state "fd_sha512_core_ref.K" q sha512StandardK64 := by
  rw [← firedancer_source_k64_eq]
  exact hload

/-- Explicit loader model, not an assertion that an unimported Firedancer
initializer function has executed. -/
def firedancerWithK64 (state : GlobalState) : GlobalState :=
  state.withGlobal "fd_sha512_core_ref.K" k64Bytes

theorem firedancerWithK64_holds (state : GlobalState) :
    HoldsGlobal (firedancerWithK64 state) "fd_sha512_core_ref.K"
      ⟨⟨state.alloc.nextFreeBlock⟩, 0⟩ sha512StandardK64 :=
  firedancerK64_standard_of_loaded _ _ (holdsGlobal_withGlobal _ _ _)

theorem firedancerWithK64_wf (state : GlobalState) (hwf : state.WF) :
    (firedancerWithK64 state).WF := hwf.withGlobal _ _

/-- Loading before allocating the SHA context discharges K64 readiness and
its provenance separation without any additional disjointness hypothesis. -/
theorem firedancer_loadedK64_fresh_ready (state : GlobalState) (hwf : state.WF) :
    Sha512KHolds (firedancerWithSha (firedancerWithK64 state))
      (firedancerFreshSha (firedancerWithK64 state)) sha512StandardK64 := by
  obtain ⟨hp, hf, hv⟩ := firedancerWithK64_holds state
  have hwf' := firedancerWithK64_wf state hwf
  obtain ⟨hf', hv'⟩ := readWord_of_live?_eq
    (live?_afterAlloca_of_fits hwf' (256 * 8) hf) hf
  exact ⟨_, ⟨hp, hf', hv'.trans hv⟩, (firedancerFreshSha_apart hwf' hf).symm⟩

/-- The existing verifier readiness endpoint now takes a fixed, proved K64
value. Only actual global loading and the separate curve/table facts remain. -/
theorem firedancerGlobalsReady_of_source_k64 (state : GlobalState)
    (href : state.RefWF [])
    (hload : ∃ q, HoldsGlobal state "fd_sha512_core_ref.K" q k64Bytes)
    (htable : Firedancer.Ref.BaseTableHolds state firedancerBaseTable) :
    FiredancerGlobalsReady state sha512StandardK64 := by
  obtain ⟨q, hq⟩ := hload
  exact ⟨href, ⟨q, firedancerK64_standard_of_loaded state q hq⟩, htable⟩

/-- A contract proved against the actual imported source bytes is exactly a
contract at the independently specified standard constant values. -/
theorem firedancerShaAppendBy_source_iff (programs : FiredancerShaPrograms) (append) :
    FiredancerShaAppendBy programs k64Bytes append ↔
      FiredancerShaAppendBy programs sha512StandardK64 append := by
  rw [firedancer_source_k64_eq]

theorem firedancerShaFinishBy_source_iff (programs : FiredancerShaPrograms) (finish block) :
    FiredancerShaFinishBy programs k64Bytes finish block ↔
      FiredancerShaFinishBy programs sha512StandardK64 finish block := by
  rw [firedancer_source_k64_eq]

/-- The supplied initializer program's actual successful call preserves the
standard K64 readiness for the next append call. The initializer contract is
explicit because this development has no imported Firedancer SHA body. -/
theorem firedancerShaInit_preserves_k64 (programs : FiredancerShaPrograms) (init)
    (hinit : FiredancerShaInitBy programs init)
    (state : GlobalState) (sha : Pointer) (hwf : state.WF)
    (hsha : IsSha512Ptr state.mem sha)
    (hk : Sha512KHolds state sha sha512StandardK64)
    (blk : Option LiveBlock) (hr : init (state.mem.live? sha.id) sha.offset = some blk) :
    ∃ after,
      StateT.run (runFunction (programs.init.denote
        (Ctxt.Valuation.singleton (.value sha)))) state = .value ([.value sha]ₕ, after) ∧
      after.WF ∧ Sha512KHolds after sha sha512StandardK64 ∧
      after.mem.live? sha.id = blk := by
  obtain ⟨after, hcall, hw, _, hg, hl, hb⟩ := (hinit sha state hwf hsha).1 blk hr
  exact ⟨after, hcall, hw, hk.of_live?_eq hwf hg (fun b hb _ => hl b hb), hb⟩

/-- The same constants survive every successful supplied append call, so a
single loader fact serves the entire R || A || message streaming sequence. -/
theorem firedancerShaAppend_preserves_k64 (programs : FiredancerShaPrograms) (append)
    (happend : FiredancerShaAppendBy programs sha512StandardK64 append)
    (state : GlobalState) (sha data : Pointer) (sz : BitVec 64) (hwf : state.WF)
    (hoff : data.offset.toNat + sz.toNat ≤ 2 ^ 64) (hne : sha.id ≠ data.id)
    (hk : Sha512KHolds state sha sha512StandardK64)
    (hdata : Fits state.mem data (sz.toNat * 8))
    (blk : Option LiveBlock)
    (hr : append (state.mem.live? sha.id) sha.offset (bytesOf (readWord hdata)) = some blk) :
    ∃ after,
      StateT.run (runFunction (programs.append.denote
        (Ctxt.Valuation.ofHVector [.value sz, .value data, .value sha]ₕ))) state =
          .value ([.value sha]ₕ, after) ∧
      after.WF ∧ Sha512KHolds after sha sha512StandardK64 ∧
      after.mem.live? sha.id = blk := by
  obtain ⟨after, hcall, hw, _, hg, hl, hb⟩ :=
    (happend sha data sz state hwf hoff hne hk hdata).1 blk hr
  exact ⟨after, hcall, hw, hk.of_live?_eq hwf hg (fun b hb _ => hl b hb), hb⟩

/-- Finishing also preserves the table when the caller's output has different
provenance. The extra separation is necessary: its contract permits writes to
the digest allocation, which must not be K64's allocation. -/
theorem firedancerShaFinish_preserves_k64 (programs : FiredancerShaPrograms) (finish block)
    (hfinish : FiredancerShaFinishBy programs sha512StandardK64 finish block)
    (state : GlobalState) (sha hash q : Pointer) (hwf : state.WF)
    (hhash : Fits state.mem hash (64 * 8))
    (hoff : hash.offset.toNat + 64 ≤ 2 ^ 64) (hne : sha.id ≠ hash.id)
    (hq : HoldsGlobal state "fd_sha512_core_ref.K" q sha512StandardK64)
    (hqs : q.id ≠ sha.id) (hqh : q.id ≠ hash.id) (digest : BitVec 512)
    (hr : finish (state.mem.live? sha.id) sha.offset
      (state.mem.live? hash.id) hash.offset = some digest) :
    ∃ after,
      StateT.run (runFunction (programs.finish.denote
        (Ctxt.Valuation.ofHVector [.value hash, .value sha]ₕ))) state =
          .value ([.value hash]ₕ, after) ∧
      after.WF ∧ Sha512KHolds after sha sha512StandardK64 ∧
      ∃ h : Fits after.mem hash (64 * 8), readWord h = digest := by
  obtain ⟨after, hcall, hw, _, hg, hl, _, hd⟩ :=
    (hfinish sha hash state hwf hhash hoff hne ⟨q, hq, hqs⟩).1 digest hr
  obtain ⟨hp, hf, hv⟩ := hq
  obtain ⟨hf', hv'⟩ := readWord_of_live?_eq (hl q.id (by tauto)) hf
  refine ⟨after, hcall, hw, ⟨q, ⟨?_, hf', hv'.trans hv⟩, hqs⟩, hd⟩
  unfold GlobalPtr at hp ⊢
  rw [hg]
  exact hp

end Agave.Ed25519.Bridge
