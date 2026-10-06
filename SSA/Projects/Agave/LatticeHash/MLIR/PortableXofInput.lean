/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofData
import SSA.Projects.Agave.LatticeHash.MLIR.PortableMemory
import SSA.Projects.Agave.LatticeHash.MLIR.PortableCasts
namespace AgaveLatticeHash.MLIR.PortableXof
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def inputValuation (out cvp msg : Pointer) (cv : CV Word) (m : State Word)
    (counter : BitVec 64) (len flags : BitVec 8) : preInput.middle.Valuation :=
  Ctxt.Valuation.ofHVector (
    .value (flags.zeroExtend 32) ::ₕ
    .value (len.zeroExtend 32) ::ₕ
    .value (counter.extractLsb' 32 32) ::ₕ
    .value (counter >>> (32 : BitVec 64)) ::ₕ
    .value (counter.extractLsb' 0 32) ::ₕ
    .value (cv 7) ::ₕ
    .value (cvp.withOffset 28) ::ₕ
    .value (cv 6) ::ₕ
    .value (cvp.withOffset 24) ::ₕ
    .value (cv 5) ::ₕ
    .value (cvp.withOffset 20) ::ₕ
    .value (cv 4) ::ₕ
    .value (cvp.withOffset 16) ::ₕ
    .value (cv 3) ::ₕ
    .value (cvp.withOffset 12) ::ₕ
    .value (cv 2) ::ₕ
    .value (cvp.withOffset 8) ::ₕ
    .value (cv 1) ::ₕ
    .value (cvp.withOffset 4) ::ₕ
    .value (cv 0) ::ₕ
    .value (m 15) ::ₕ
    .value (msg.withOffset 60) ::ₕ
    .value (m 14) ::ₕ
    .value (msg.withOffset 56) ::ₕ
    .value (m 13) ::ₕ
    .value (msg.withOffset 52) ::ₕ
    .value (m 12) ::ₕ
    .value (msg.withOffset 48) ::ₕ
    .value (m 11) ::ₕ
    .value (msg.withOffset 44) ::ₕ
    .value (m 10) ::ₕ
    .value (msg.withOffset 40) ::ₕ
    .value (m 9) ::ₕ
    .value (msg.withOffset 36) ::ₕ
    .value (m 8) ::ₕ
    .value (msg.withOffset 32) ::ₕ
    .value (m 7) ::ₕ
    .value (msg.withOffset 28) ::ₕ
    .value (m 6) ::ₕ
    .value (msg.withOffset 24) ::ₕ
    .value (m 5) ::ₕ
    .value (msg.withOffset 20) ::ₕ
    .value (m 4) ::ₕ
    .value (msg.withOffset 16) ::ₕ
    .value (m 3) ::ₕ
    .value (msg.withOffset 12) ::ₕ
    .value (m 2) ::ₕ
    .value (msg.withOffset 8) ::ₕ
    .value (m 1) ::ₕ
    .value (msg.withOffset 4) ::ₕ
    .value (m 0) ::ₕ
    .value (-1521486534 : BitVec 32) ::ₕ
    .value (1013904242 : BitVec 32) ::ₕ
    .value (-1150833019 : BitVec 32) ::ₕ
    .value (25 : BitVec 32) ::ₕ
    .value (24 : BitVec 32) ::ₕ
    .value (20 : BitVec 32) ::ₕ
    .value (1779033703 : BitVec 32) ::ₕ
    .value (16 : BitVec 32) ::ₕ
    .value (60 : BitVec 64) ::ₕ
    .value (56 : BitVec 64) ::ₕ
    .value (52 : BitVec 64) ::ₕ
    .value (48 : BitVec 64) ::ₕ
    .value (44 : BitVec 64) ::ₕ
    .value (40 : BitVec 64) ::ₕ
    .value (36 : BitVec 64) ::ₕ
    .value (32 : BitVec 64) ::ₕ
    .value (28 : BitVec 64) ::ₕ
    .value (24 : BitVec 64) ::ₕ
    .value (20 : BitVec 64) ::ₕ
    .value (16 : BitVec 64) ::ₕ
    .value (12 : BitVec 64) ::ₕ
    .value (8 : BitVec 64) ::ₕ
    .value (4 : BitVec 64) ::ₕ
    .value flags ::ₕ
    .value counter ::ₕ
    .value len ::ₕ
    .value msg ::ₕ
    .value cvp ::ₕ
    .value out ::ₕ HVector.nil)

def inputBlock : BlockCom (Ctxt.ofList [SLLVM.Ty.bitvec 8, SLLVM.Ty.bitvec 64,
    SLLVM.Ty.bitvec 8, SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) preInput.middle [] [] :=
  preInput.pre.append (.term (.ret .nil))

/-- Actual input loads and casts, before the pure shared compression rounds. -/
theorem input_run (s : GlobalState) (out cvp msg : Pointer)
    (cv : CV Word) (m : State Word) (counter : BitVec 64) (len flags : BitVec 8)
    (hcvp : Fits s.mem cvp 256) (hmsg : Fits s.mem msg 512)
    (rcv : ∀ i : Fin 8, readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (cv i))
    (rmsg : ∀ i : Fin 16, readWord? (msg.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (m i)) :
    StateT.run (inputBlock.denote (Ctxt.Valuation.ofHVector
      [.value flags, .value counter, .value len, .value msg, .value cvp, .value out]ₕ) >>= pure) s =
    .value ((inputValuation out cvp msg cv m counter len flags, .inl []ₕ), s) := by
  dsimp only [inputBlock, preInput, BlockPrefix.append]
  denote_step_reduce v 22 [LLVM.const?]
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17 hv18 hv19 hv20 hv21 hv22
  rw [BlockCom.run_bind_denote_var_of_nil (s' := s)
    (by simp [Expr.denoteOp, simp_denote, simp_sllvm])]
  have read_msg0 : readWord? msg 32 s.mem = some (m 0) := by
    simpa [Pointer.withOffset] using rmsg (0 : Fin 16)
  peel_portable_word (m 0), msg, (Fits.mono hmsg (by omega)), read_msg0, s
  peel_gep 4 with msg, hmsg, s as msg1
  have read_msg1 : readWord? msg1 32 s.mem = some (m 1) := by
    simpa [msg1, Pointer.withOffset] using rmsg (1 : Fin 16)
  peel_portable_word (m 1), msg1, (Fits.mono hmsg1 (by omega)), read_msg1, s
  peel_gep 8 with msg, hmsg, s as msg2
  have read_msg2 : readWord? msg2 32 s.mem = some (m 2) := by
    simpa [msg2, Pointer.withOffset] using rmsg (2 : Fin 16)
  peel_portable_word (m 2), msg2, (Fits.mono hmsg2 (by omega)), read_msg2, s
  peel_gep 12 with msg, hmsg, s as msg3
  have read_msg3 : readWord? msg3 32 s.mem = some (m 3) := by
    simpa [msg3, Pointer.withOffset] using rmsg (3 : Fin 16)
  peel_portable_word (m 3), msg3, (Fits.mono hmsg3 (by omega)), read_msg3, s
  peel_gep 16 with msg, hmsg, s as msg4
  have read_msg4 : readWord? msg4 32 s.mem = some (m 4) := by
    simpa [msg4, Pointer.withOffset] using rmsg (4 : Fin 16)
  peel_portable_word (m 4), msg4, (Fits.mono hmsg4 (by omega)), read_msg4, s
  peel_gep 20 with msg, hmsg, s as msg5
  have read_msg5 : readWord? msg5 32 s.mem = some (m 5) := by
    simpa [msg5, Pointer.withOffset] using rmsg (5 : Fin 16)
  peel_portable_word (m 5), msg5, (Fits.mono hmsg5 (by omega)), read_msg5, s
  peel_gep 24 with msg, hmsg, s as msg6
  have read_msg6 : readWord? msg6 32 s.mem = some (m 6) := by
    simpa [msg6, Pointer.withOffset] using rmsg (6 : Fin 16)
  peel_portable_word (m 6), msg6, (Fits.mono hmsg6 (by omega)), read_msg6, s
  peel_gep 28 with msg, hmsg, s as msg7
  have read_msg7 : readWord? msg7 32 s.mem = some (m 7) := by
    simpa [msg7, Pointer.withOffset] using rmsg (7 : Fin 16)
  peel_portable_word (m 7), msg7, (Fits.mono hmsg7 (by omega)), read_msg7, s
  peel_gep 32 with msg, hmsg, s as msg8
  have read_msg8 : readWord? msg8 32 s.mem = some (m 8) := by
    simpa [msg8, Pointer.withOffset] using rmsg (8 : Fin 16)
  peel_portable_word (m 8), msg8, (Fits.mono hmsg8 (by omega)), read_msg8, s
  peel_gep 36 with msg, hmsg, s as msg9
  have read_msg9 : readWord? msg9 32 s.mem = some (m 9) := by
    simpa [msg9, Pointer.withOffset] using rmsg (9 : Fin 16)
  peel_portable_word (m 9), msg9, (Fits.mono hmsg9 (by omega)), read_msg9, s
  peel_gep 40 with msg, hmsg, s as msg10
  have read_msg10 : readWord? msg10 32 s.mem = some (m 10) := by
    simpa [msg10, Pointer.withOffset] using rmsg (10 : Fin 16)
  peel_portable_word (m 10), msg10, (Fits.mono hmsg10 (by omega)), read_msg10, s
  peel_gep 44 with msg, hmsg, s as msg11
  have read_msg11 : readWord? msg11 32 s.mem = some (m 11) := by
    simpa [msg11, Pointer.withOffset] using rmsg (11 : Fin 16)
  peel_portable_word (m 11), msg11, (Fits.mono hmsg11 (by omega)), read_msg11, s
  peel_gep 48 with msg, hmsg, s as msg12
  have read_msg12 : readWord? msg12 32 s.mem = some (m 12) := by
    simpa [msg12, Pointer.withOffset] using rmsg (12 : Fin 16)
  peel_portable_word (m 12), msg12, (Fits.mono hmsg12 (by omega)), read_msg12, s
  peel_gep 52 with msg, hmsg, s as msg13
  have read_msg13 : readWord? msg13 32 s.mem = some (m 13) := by
    simpa [msg13, Pointer.withOffset] using rmsg (13 : Fin 16)
  peel_portable_word (m 13), msg13, (Fits.mono hmsg13 (by omega)), read_msg13, s
  peel_gep 56 with msg, hmsg, s as msg14
  have read_msg14 : readWord? msg14 32 s.mem = some (m 14) := by
    simpa [msg14, Pointer.withOffset] using rmsg (14 : Fin 16)
  peel_portable_word (m 14), msg14, (Fits.mono hmsg14 (by omega)), read_msg14, s
  peel_gep 60 with msg, hmsg, s as msg15
  have read_msg15 : readWord? msg15 32 s.mem = some (m 15) := by
    simpa [msg15, Pointer.withOffset] using rmsg (15 : Fin 16)
  peel_portable_word (m 15), msg15, (Fits.mono hmsg15 (by omega)), read_msg15, s
  have read_cvp0 : readWord? cvp 32 s.mem = some (cv 0) := by
    simpa [Pointer.withOffset] using rcv (0 : Fin 8)
  peel_portable_word (cv 0), cvp, (Fits.mono hcvp (by omega)), read_cvp0, s
  peel_gep 4 with cvp, hcvp, s as cvp1
  have read_cvp1 : readWord? cvp1 32 s.mem = some (cv 1) := by
    simpa [cvp1, Pointer.withOffset] using rcv (1 : Fin 8)
  peel_portable_word (cv 1), cvp1, (Fits.mono hcvp1 (by omega)), read_cvp1, s
  peel_gep 8 with cvp, hcvp, s as cvp2
  have read_cvp2 : readWord? cvp2 32 s.mem = some (cv 2) := by
    simpa [cvp2, Pointer.withOffset] using rcv (2 : Fin 8)
  peel_portable_word (cv 2), cvp2, (Fits.mono hcvp2 (by omega)), read_cvp2, s
  peel_gep 12 with cvp, hcvp, s as cvp3
  have read_cvp3 : readWord? cvp3 32 s.mem = some (cv 3) := by
    simpa [cvp3, Pointer.withOffset] using rcv (3 : Fin 8)
  peel_portable_word (cv 3), cvp3, (Fits.mono hcvp3 (by omega)), read_cvp3, s
  peel_gep 16 with cvp, hcvp, s as cvp4
  have read_cvp4 : readWord? cvp4 32 s.mem = some (cv 4) := by
    simpa [cvp4, Pointer.withOffset] using rcv (4 : Fin 8)
  peel_portable_word (cv 4), cvp4, (Fits.mono hcvp4 (by omega)), read_cvp4, s
  peel_gep 20 with cvp, hcvp, s as cvp5
  have read_cvp5 : readWord? cvp5 32 s.mem = some (cv 5) := by
    simpa [cvp5, Pointer.withOffset] using rcv (5 : Fin 8)
  peel_portable_word (cv 5), cvp5, (Fits.mono hcvp5 (by omega)), read_cvp5, s
  peel_gep 24 with cvp, hcvp, s as cvp6
  have read_cvp6 : readWord? cvp6 32 s.mem = some (cv 6) := by
    simpa [cvp6, Pointer.withOffset] using rcv (6 : Fin 8)
  peel_portable_word (cv 6), cvp6, (Fits.mono hcvp6 (by omega)), read_cvp6, s
  peel_gep 28 with cvp, hcvp, s as cvp7
  have read_cvp7 : readWord? cvp7 32 s.mem = some (cv 7) := by
    simpa [cvp7, Pointer.withOffset] using rcv (7 : Fin 8)
  peel_portable_word (cv 7), cvp7, (Fits.mono hcvp7 (by omega)), read_cvp7, s
  denote_step_all v 73
  denote_eval v 69 73
  have vlo : v69 = .value (counter.extractLsb' 0 32) := by simp [hv69, simp_llvm, simp_llvm_option, BitVec.extractLsb']
  have vhi : v71 = .value (counter.extractLsb' 32 32) := by
    simp only [hv71, hv70]
    exact portable_counter_high counter
  have vlen : v72 = .value (len.zeroExtend 32) := by simp [hv72, simp_llvm, simp_llvm_option]
  have vflags : v73 = .value (flags.zeroExtend 32) := by simp [hv73, simp_llvm, simp_llvm_option]
  rw [vlo, vhi, vlen, vflags]
  simp_return
  simp [inputValuation, hv70, simp_llvm, simp_llvm_option, msg1, msg2, msg3, msg4, msg5, msg6, msg7, msg8, msg9, msg10, msg11, msg12, msg13, msg14, msg15, cvp1, cvp2, cvp3, cvp4, cvp5, cvp6, cvp7]

end AgaveLatticeHash.MLIR.PortableXof
