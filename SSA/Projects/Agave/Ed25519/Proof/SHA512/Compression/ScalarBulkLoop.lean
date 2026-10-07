import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkStep

/-! Arbitrarily many live blocks in the imported scalar SHA-512 loop. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open ScalarFull
open Spec

/-- The original bb4 loop computes the full specification fold, then performs
its single final chaining-state store and returns through bb5 and bb7. -/
theorem scalar_loop_positive (p : Primitives) (g : Globals)
    (state : GlobalState) (chain kp : Pointer)
    (hc : SmallRange state.mem chain 64) (hk : KRead state.mem kp)
    (n : Nat) (E : Env program.Γ) (data : Pointer) (initial : Spec.State)
    (hd : SmallRange state.mem data (128 * (n + 1)))
    (hi : InitialReady E initial) (hs : StoreReady E chain) (hconst : Constants E kp)
    (hdata : E.read (%200) = .value data)
    (hend : E.read (%176) = .value (data.add (BitVec.ofNat 64 (128 * (n + 1))))) :
    (program p g).runFrom E 4 state = .value (.nil,
      {state with mem := state.mem.storeAt chain (Spec.run (pack initial) (readBytes state.mem data (128 * (n + 1))))}) := by
  induction n generalizing E data initial with
  | zero =>
    simpa only [Nat.zero_add, Nat.mul_one, Spec.run_one_block _ _ (readBytes_length _ _ _),
      compressBlockBytes, unpack_pack] using
      scalar_backend_one p g E state chain data kp initial hc hd hi hs hconst hk hdata hend
  | succ n ih =>
    obtain ⟨E', hstep, hi', hs', hconst', hdata', hend'⟩ :=
      scalar_continue E state chain data kp initial n hd hi hs hconst hk hdata hend
    have hd' : SmallRange state.mem (data.add 128#64) (128 * (n + 1)) :=
      subrange hd (offset := 128) (by omega)
    have hr := ih E' (data.add 128#64)
      (compressBlock initial (readBytes state.mem data 128)) hd' hi' hs' hconst' hdata' hend'
    rw [Func.runFrom_eq]
    change (program.bb4.run program.blockParams E state >>= _) = _
    rw [hstep]
    change (program p g).runFrom E' 4 state = _
    rw [run_readBytes_succ initial state.mem data (n + 1)]
    exact hr

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
