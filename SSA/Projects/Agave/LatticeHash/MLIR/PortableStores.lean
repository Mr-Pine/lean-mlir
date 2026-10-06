import SSA.Projects.Agave.LatticeHash.MLIR.PortableOutputRead

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionExit

/-- Fold one scalar output store while keeping intermediate states opaque. -/
theorem portableStateStep (out : Pointer) (v : State Word)
    (s : GlobalState) (k : Nat) (prev next : GlobalState)
    (hprev : prev = {s with mem := outputMem out (fun i => #v[v i]) k s.mem})
    (hnext : next = {prev with mem := prev.mem.splice (out.withOffset (BitVec.ofNat 64 (4*k))) (v (Fin.ofNat 16 k))}) :
    next = {s with mem := outputMem out (fun i => #v[v i]) (k+1) s.mem} := by
  rw [hnext, hprev]
  simp only [outputMem, packBits_singleton]

end AgaveLatticeHash.MLIR
