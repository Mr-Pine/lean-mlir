import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlaceProof
import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlaceMemoryRead
namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer Blake3Compression
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace PortableInPlace

theorem cvMemory_fits (m : MemoryState) (cvp : Pointer) (x : State Word)
    {p : Pointer} {w : Nat} (h : Fits m p w) : Fits (cvMemory m cvp x) p w :=
  CompressionExit.fits_outputMem cvp (fun i => #v[x i]) 8 h

theorem cvMemory_frame (m : MemoryState) (cvp : Pointer) (x : State Word)
    (q : BlockId) (hq : q ≠ cvp.id) : (cvMemory m cvp x).live? q = m.live? q :=
  CompressionExit.outputMem_frame cvp (fun i => #v[x i]) 8 m q hq

end PortableInPlace

/-- The exact eight writebacks are the scalar BLAKE3 chaining value. -/
theorem portable_in_place_readback (s : GlobalState) (cvp msg : Pointer)
    (cv : CV Word) (m : State Word) (counter : BitVec 64) (len flags : BitVec 8)
    (hcvp : Fits s.mem cvp 256) (hmsg : Fits s.mem msg 512)
    (hwrap : msg.offset.toNat + 64 ≤ 2^64)
    (hcvwrap : cvp.offset.toNat + 32 ≤ 2^64)
    (rcv : ∀ i : Fin 8, readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (cv i))
    (rmsg : ∀ i : Fin 16, readWord? (msg.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (m i)) :
    ∃ t : GlobalState,
      StateT.run (agave_portable_compress_in_place.denote (Ctxt.Valuation.ofHVector
        [.value flags, .value counter, .value len, .value msg, .value cvp]ₕ)) s = .value ([]ₕ, t) ∧
      (∀ i : Fin 8, readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 t.mem =
        some (scalarCompressCV cv m counter (len.zeroExtend 32) (flags.zeroExtend 32) i)) ∧
      (∀ q, q ≠ cvp.id → t.mem.live? q = s.mem.live? q) := by
  obtain ⟨v, hv⟩ : ∃ v : State Word,
      v = scalarCompress cv m counter (len.zeroExtend 32) (flags.zeroExtend 32) := ⟨_, rfl⟩
  have hr := portable_in_place_run s cvp msg cv m counter len flags hcvp hmsg hwrap rcv rmsg
  rw [← hv] at hr
  refine ⟨{s with mem := PortableInPlace.cvMemory s.mem cvp v}, hr, ?_, ?_⟩
  · intro i
    rw [scalarCompressCV, ← hv]
    dsimp only []
    exact PortableInPlace.cvMemory_read s.mem cvp v hcvp hcvwrap i
  · intro q hq
    dsimp only []
    exact PortableInPlace.cvMemory_frame s.mem cvp v q hq

end AgaveLatticeHash.MLIR
