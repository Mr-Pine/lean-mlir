import SSA.Projects.Agave.LatticeHash.MLIR.agave_portable_compress_pre
import SSA.Projects.Agave.LatticeHash.MLIR.PortableMemory
import SSA.Projects.Agave.LatticeHash.MLIR.GArithmetic
import SSA.Projects.Agave.LatticeHash.MLIR.PortableCasts
import SSA.Projects.Agave.LatticeHash.MLIR.PortableRounds
import SSA.Projects.Agave.LatticeHash.MLIR.PortableStores
namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open Blake3Compression
set_option maxRecDepth 8192 in
set_option maxHeartbeats 96000000 in
/-- Execute the independently compiled portable compression on arbitrary words.
The read hypotheses describe the actual byte-backed source memory; no result or
compression correctness premise is supplied. -/
theorem portable_compression_run (s : GlobalState) (out cvp msg : Pointer)
    (cv : CV Word) (m : State Word) (counter : BitVec 64) (len flags : BitVec 8)
    (hout : Fits s.mem out 512) (hcvp : Fits s.mem cvp 256) (hmsg : Fits s.mem msg 512)
    (rcv : ∀ i : Fin 8, readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (cv i))
    (rmsg : ∀ i : Fin 16, readWord? (msg.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (m i)) :
    StateT.run (agave_portable_compress_pre.denote (Ctxt.Valuation.ofHVector
      [.value flags, .value counter, .value len, .value msg, .value cvp, .value out]ₕ)) s =
    .value ([]ₕ, {s with mem := portableCompressionMemory s.mem out (scalarCompressPre cv m counter (len.zeroExtend 32) (flags.zeroExtend 32))}) := by
  first
  | rw [Cfg.denote]
    unfold agave_portable_compress_pre
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
    obtain ⟨q0, hq0⟩ : ∃ q : Quad Word, q = scalarG (cv 0) (cv 4) (1779033703 : Word) (counter.extractLsb' 0 32) (m 0) (m 1) := ⟨_, rfl⟩
    denote_step_all v 87
    denote_eval v 74 87
    have eq0a : v82 = .value q0.a := by
      simp only [hv87, hv86, hv85, hv84, hv83, hv82, hv81, hv80, hv79, hv78, hv77, hv76, hv75, hv74]
      simp only [hq0, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq0d : v84 = .value q0.d := by
      simp only [hv87, hv86, hv85, hv84, hv83, hv82, hv81, hv80, hv79, hv78, hv77, hv76, hv75, hv74]
      simp only [hq0, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq0c : v85 = .value q0.c := by
      simp only [hv87, hv86, hv85, hv84, hv83, hv82, hv81, hv80, hv79, hv78, hv77, hv76, hv75, hv74]
      simp only [hq0, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq0b : v87 = .value q0.b := by
      simp only [hv87, hv86, hv85, hv84, hv83, hv82, hv81, hv80, hv79, hv78, hv77, hv76, hv75, hv74]
      simp only [hq0, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq0a, eq0d, eq0c, eq0b]
    obtain ⟨q1, hq1⟩ : ∃ q : Quad Word, q = scalarG (cv 1) (cv 5) (3144134277 : Word) (counter.extractLsb' 32 32) (m 2) (m 3) := ⟨_, rfl⟩
    denote_step_all v 101
    denote_eval v 88 101
    have eq1a : v96 = .value q1.a := by
      simp only [hv101, hv100, hv99, hv98, hv97, hv96, hv95, hv94, hv93, hv92, hv91, hv90, hv89, hv88]
      simp only [hq1, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq1d : v98 = .value q1.d := by
      simp only [hv101, hv100, hv99, hv98, hv97, hv96, hv95, hv94, hv93, hv92, hv91, hv90, hv89, hv88]
      simp only [hq1, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq1c : v99 = .value q1.c := by
      simp only [hv101, hv100, hv99, hv98, hv97, hv96, hv95, hv94, hv93, hv92, hv91, hv90, hv89, hv88]
      simp only [hq1, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq1b : v101 = .value q1.b := by
      simp only [hv101, hv100, hv99, hv98, hv97, hv96, hv95, hv94, hv93, hv92, hv91, hv90, hv89, hv88]
      simp only [hq1, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq1a, eq1d, eq1c, eq1b]
    obtain ⟨q2, hq2⟩ : ∃ q : Quad Word, q = scalarG (cv 2) (cv 6) (1013904242 : Word) (len.zeroExtend 32) (m 4) (m 5) := ⟨_, rfl⟩
    denote_step_all v 115
    denote_eval v 102 115
    have eq2a : v110 = .value q2.a := by
      simp only [hv115, hv114, hv113, hv112, hv111, hv110, hv109, hv108, hv107, hv106, hv105, hv104, hv103, hv102]
      simp only [hq2, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq2d : v112 = .value q2.d := by
      simp only [hv115, hv114, hv113, hv112, hv111, hv110, hv109, hv108, hv107, hv106, hv105, hv104, hv103, hv102]
      simp only [hq2, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq2c : v113 = .value q2.c := by
      simp only [hv115, hv114, hv113, hv112, hv111, hv110, hv109, hv108, hv107, hv106, hv105, hv104, hv103, hv102]
      simp only [hq2, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq2b : v115 = .value q2.b := by
      simp only [hv115, hv114, hv113, hv112, hv111, hv110, hv109, hv108, hv107, hv106, hv105, hv104, hv103, hv102]
      simp only [hq2, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq2a, eq2d, eq2c, eq2b]
    obtain ⟨q3, hq3⟩ : ∃ q : Quad Word, q = scalarG (cv 3) (cv 7) (2773480762 : Word) (flags.zeroExtend 32) (m 6) (m 7) := ⟨_, rfl⟩
    denote_step_all v 129
    denote_eval v 116 129
    have eq3a : v124 = .value q3.a := by
      simp only [hv129, hv128, hv127, hv126, hv125, hv124, hv123, hv122, hv121, hv120, hv119, hv118, hv117, hv116]
      simp only [hq3, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq3d : v126 = .value q3.d := by
      simp only [hv129, hv128, hv127, hv126, hv125, hv124, hv123, hv122, hv121, hv120, hv119, hv118, hv117, hv116]
      simp only [hq3, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq3c : v127 = .value q3.c := by
      simp only [hv129, hv128, hv127, hv126, hv125, hv124, hv123, hv122, hv121, hv120, hv119, hv118, hv117, hv116]
      simp only [hq3, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq3b : v129 = .value q3.b := by
      simp only [hv129, hv128, hv127, hv126, hv125, hv124, hv123, hv122, hv121, hv120, hv119, hv118, hv117, hv116]
      simp only [hq3, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq3a, eq3d, eq3c, eq3b]
    obtain ⟨q4, hq4⟩ : ∃ q : Quad Word, q = scalarG q0.a q1.b q2.c q3.d (m 8) (m 9) := ⟨_, rfl⟩
    denote_step_all v 143
    denote_eval v 130 143
    have eq4a : v138 = .value q4.a := by
      simp only [hv143, hv142, hv141, hv140, hv139, hv138, hv137, hv136, hv135, hv134, hv133, hv132, hv131, hv130]
      simp only [hq4, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq4d : v140 = .value q4.d := by
      simp only [hv143, hv142, hv141, hv140, hv139, hv138, hv137, hv136, hv135, hv134, hv133, hv132, hv131, hv130]
      simp only [hq4, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq4c : v141 = .value q4.c := by
      simp only [hv143, hv142, hv141, hv140, hv139, hv138, hv137, hv136, hv135, hv134, hv133, hv132, hv131, hv130]
      simp only [hq4, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq4b : v143 = .value q4.b := by
      simp only [hv143, hv142, hv141, hv140, hv139, hv138, hv137, hv136, hv135, hv134, hv133, hv132, hv131, hv130]
      simp only [hq4, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq4a, eq4d, eq4c, eq4b]
    obtain ⟨q5, hq5⟩ : ∃ q : Quad Word, q = scalarG q1.a q2.b q3.c q0.d (m 10) (m 11) := ⟨_, rfl⟩
    denote_step_all v 157
    denote_eval v 144 157
    have eq5a : v152 = .value q5.a := by
      simp only [hv157, hv156, hv155, hv154, hv153, hv152, hv151, hv150, hv149, hv148, hv147, hv146, hv145, hv144]
      simp only [hq5, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq5d : v154 = .value q5.d := by
      simp only [hv157, hv156, hv155, hv154, hv153, hv152, hv151, hv150, hv149, hv148, hv147, hv146, hv145, hv144]
      simp only [hq5, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq5c : v155 = .value q5.c := by
      simp only [hv157, hv156, hv155, hv154, hv153, hv152, hv151, hv150, hv149, hv148, hv147, hv146, hv145, hv144]
      simp only [hq5, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq5b : v157 = .value q5.b := by
      simp only [hv157, hv156, hv155, hv154, hv153, hv152, hv151, hv150, hv149, hv148, hv147, hv146, hv145, hv144]
      simp only [hq5, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq5a, eq5d, eq5c, eq5b]
    obtain ⟨q6, hq6⟩ : ∃ q : Quad Word, q = scalarG q2.a q3.b q0.c q1.d (m 12) (m 13) := ⟨_, rfl⟩
    denote_step_all v 171
    denote_eval v 158 171
    have eq6a : v166 = .value q6.a := by
      simp only [hv171, hv170, hv169, hv168, hv167, hv166, hv165, hv164, hv163, hv162, hv161, hv160, hv159, hv158]
      simp only [hq6, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq6d : v168 = .value q6.d := by
      simp only [hv171, hv170, hv169, hv168, hv167, hv166, hv165, hv164, hv163, hv162, hv161, hv160, hv159, hv158]
      simp only [hq6, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq6c : v169 = .value q6.c := by
      simp only [hv171, hv170, hv169, hv168, hv167, hv166, hv165, hv164, hv163, hv162, hv161, hv160, hv159, hv158]
      simp only [hq6, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq6b : v171 = .value q6.b := by
      simp only [hv171, hv170, hv169, hv168, hv167, hv166, hv165, hv164, hv163, hv162, hv161, hv160, hv159, hv158]
      simp only [hq6, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq6a, eq6d, eq6c, eq6b]
    obtain ⟨q7, hq7⟩ : ∃ q : Quad Word, q = scalarG q3.a q0.b q1.c q2.d (m 14) (m 15) := ⟨_, rfl⟩
    denote_step_all v 185
    denote_eval v 172 185
    have eq7a : v180 = .value q7.a := by
      simp only [hv185, hv184, hv183, hv182, hv181, hv180, hv179, hv178, hv177, hv176, hv175, hv174, hv173, hv172]
      simp only [hq7, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq7d : v182 = .value q7.d := by
      simp only [hv185, hv184, hv183, hv182, hv181, hv180, hv179, hv178, hv177, hv176, hv175, hv174, hv173, hv172]
      simp only [hq7, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq7c : v183 = .value q7.c := by
      simp only [hv185, hv184, hv183, hv182, hv181, hv180, hv179, hv178, hv177, hv176, hv175, hv174, hv173, hv172]
      simp only [hq7, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq7b : v185 = .value q7.b := by
      simp only [hv185, hv184, hv183, hv182, hv181, hv180, hv179, hv178, hv177, hv176, hv175, hv174, hv173, hv172]
      simp only [hq7, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq7a, eq7d, eq7c, eq7b]
    obtain ⟨q8, hq8⟩ : ∃ q : Quad Word, q = scalarG q4.a q7.b q6.c q5.d (m 2) (m 6) := ⟨_, rfl⟩
    denote_step_all v 199
    denote_eval v 186 199
    have eq8a : v194 = .value q8.a := by
      simp only [hv199, hv198, hv197, hv196, hv195, hv194, hv193, hv192, hv191, hv190, hv189, hv188, hv187, hv186]
      simp only [hq8, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq8d : v196 = .value q8.d := by
      simp only [hv199, hv198, hv197, hv196, hv195, hv194, hv193, hv192, hv191, hv190, hv189, hv188, hv187, hv186]
      simp only [hq8, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq8c : v197 = .value q8.c := by
      simp only [hv199, hv198, hv197, hv196, hv195, hv194, hv193, hv192, hv191, hv190, hv189, hv188, hv187, hv186]
      simp only [hq8, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq8b : v199 = .value q8.b := by
      simp only [hv199, hv198, hv197, hv196, hv195, hv194, hv193, hv192, hv191, hv190, hv189, hv188, hv187, hv186]
      simp only [hq8, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq8a, eq8d, eq8c, eq8b]
    obtain ⟨q9, hq9⟩ : ∃ q : Quad Word, q = scalarG q5.a q4.b q7.c q6.d (m 3) (m 10) := ⟨_, rfl⟩
    denote_step_all v 213
    denote_eval v 200 213
    have eq9a : v208 = .value q9.a := by
      simp only [hv213, hv212, hv211, hv210, hv209, hv208, hv207, hv206, hv205, hv204, hv203, hv202, hv201, hv200]
      simp only [hq9, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq9d : v210 = .value q9.d := by
      simp only [hv213, hv212, hv211, hv210, hv209, hv208, hv207, hv206, hv205, hv204, hv203, hv202, hv201, hv200]
      simp only [hq9, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq9c : v211 = .value q9.c := by
      simp only [hv213, hv212, hv211, hv210, hv209, hv208, hv207, hv206, hv205, hv204, hv203, hv202, hv201, hv200]
      simp only [hq9, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq9b : v213 = .value q9.b := by
      simp only [hv213, hv212, hv211, hv210, hv209, hv208, hv207, hv206, hv205, hv204, hv203, hv202, hv201, hv200]
      simp only [hq9, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq9a, eq9d, eq9c, eq9b]
    obtain ⟨q10, hq10⟩ : ∃ q : Quad Word, q = scalarG q6.a q5.b q4.c q7.d (m 7) (m 0) := ⟨_, rfl⟩
    denote_step_all v 227
    denote_eval v 214 227
    have eq10a : v222 = .value q10.a := by
      simp only [hv227, hv226, hv225, hv224, hv223, hv222, hv221, hv220, hv219, hv218, hv217, hv216, hv215, hv214]
      simp only [hq10, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq10d : v224 = .value q10.d := by
      simp only [hv227, hv226, hv225, hv224, hv223, hv222, hv221, hv220, hv219, hv218, hv217, hv216, hv215, hv214]
      simp only [hq10, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq10c : v225 = .value q10.c := by
      simp only [hv227, hv226, hv225, hv224, hv223, hv222, hv221, hv220, hv219, hv218, hv217, hv216, hv215, hv214]
      simp only [hq10, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq10b : v227 = .value q10.b := by
      simp only [hv227, hv226, hv225, hv224, hv223, hv222, hv221, hv220, hv219, hv218, hv217, hv216, hv215, hv214]
      simp only [hq10, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq10a, eq10d, eq10c, eq10b]
    obtain ⟨q11, hq11⟩ : ∃ q : Quad Word, q = scalarG q7.a q6.b q5.c q4.d (m 4) (m 13) := ⟨_, rfl⟩
    denote_step_all v 241
    denote_eval v 228 241
    have eq11a : v236 = .value q11.a := by
      simp only [hv241, hv240, hv239, hv238, hv237, hv236, hv235, hv234, hv233, hv232, hv231, hv230, hv229, hv228]
      simp only [hq11, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq11d : v238 = .value q11.d := by
      simp only [hv241, hv240, hv239, hv238, hv237, hv236, hv235, hv234, hv233, hv232, hv231, hv230, hv229, hv228]
      simp only [hq11, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq11c : v239 = .value q11.c := by
      simp only [hv241, hv240, hv239, hv238, hv237, hv236, hv235, hv234, hv233, hv232, hv231, hv230, hv229, hv228]
      simp only [hq11, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq11b : v241 = .value q11.b := by
      simp only [hv241, hv240, hv239, hv238, hv237, hv236, hv235, hv234, hv233, hv232, hv231, hv230, hv229, hv228]
      simp only [hq11, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq11a, eq11d, eq11c, eq11b]
    obtain ⟨q12, hq12⟩ : ∃ q : Quad Word, q = scalarG q8.a q9.b q10.c q11.d (m 1) (m 11) := ⟨_, rfl⟩
    denote_step_all v 255
    denote_eval v 242 255
    have eq12a : v250 = .value q12.a := by
      simp only [hv255, hv254, hv253, hv252, hv251, hv250, hv249, hv248, hv247, hv246, hv245, hv244, hv243, hv242]
      simp only [hq12, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq12d : v252 = .value q12.d := by
      simp only [hv255, hv254, hv253, hv252, hv251, hv250, hv249, hv248, hv247, hv246, hv245, hv244, hv243, hv242]
      simp only [hq12, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq12c : v253 = .value q12.c := by
      simp only [hv255, hv254, hv253, hv252, hv251, hv250, hv249, hv248, hv247, hv246, hv245, hv244, hv243, hv242]
      simp only [hq12, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq12b : v255 = .value q12.b := by
      simp only [hv255, hv254, hv253, hv252, hv251, hv250, hv249, hv248, hv247, hv246, hv245, hv244, hv243, hv242]
      simp only [hq12, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq12a, eq12d, eq12c, eq12b]
    obtain ⟨q13, hq13⟩ : ∃ q : Quad Word, q = scalarG q9.a q10.b q11.c q8.d (m 12) (m 5) := ⟨_, rfl⟩
    denote_step_all v 269
    denote_eval v 256 269
    have eq13a : v264 = .value q13.a := by
      simp only [hv269, hv268, hv267, hv266, hv265, hv264, hv263, hv262, hv261, hv260, hv259, hv258, hv257, hv256]
      simp only [hq13, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq13d : v266 = .value q13.d := by
      simp only [hv269, hv268, hv267, hv266, hv265, hv264, hv263, hv262, hv261, hv260, hv259, hv258, hv257, hv256]
      simp only [hq13, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq13c : v267 = .value q13.c := by
      simp only [hv269, hv268, hv267, hv266, hv265, hv264, hv263, hv262, hv261, hv260, hv259, hv258, hv257, hv256]
      simp only [hq13, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq13b : v269 = .value q13.b := by
      simp only [hv269, hv268, hv267, hv266, hv265, hv264, hv263, hv262, hv261, hv260, hv259, hv258, hv257, hv256]
      simp only [hq13, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq13a, eq13d, eq13c, eq13b]
    obtain ⟨q14, hq14⟩ : ∃ q : Quad Word, q = scalarG q10.a q11.b q8.c q9.d (m 9) (m 14) := ⟨_, rfl⟩
    denote_step_all v 283
    denote_eval v 270 283
    have eq14a : v278 = .value q14.a := by
      simp only [hv283, hv282, hv281, hv280, hv279, hv278, hv277, hv276, hv275, hv274, hv273, hv272, hv271, hv270]
      simp only [hq14, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq14d : v280 = .value q14.d := by
      simp only [hv283, hv282, hv281, hv280, hv279, hv278, hv277, hv276, hv275, hv274, hv273, hv272, hv271, hv270]
      simp only [hq14, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq14c : v281 = .value q14.c := by
      simp only [hv283, hv282, hv281, hv280, hv279, hv278, hv277, hv276, hv275, hv274, hv273, hv272, hv271, hv270]
      simp only [hq14, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq14b : v283 = .value q14.b := by
      simp only [hv283, hv282, hv281, hv280, hv279, hv278, hv277, hv276, hv275, hv274, hv273, hv272, hv271, hv270]
      simp only [hq14, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq14a, eq14d, eq14c, eq14b]
    obtain ⟨q15, hq15⟩ : ∃ q : Quad Word, q = scalarG q11.a q8.b q9.c q10.d (m 15) (m 8) := ⟨_, rfl⟩
    denote_step_all v 297
    denote_eval v 284 297
    have eq15a : v292 = .value q15.a := by
      simp only [hv297, hv296, hv295, hv294, hv293, hv292, hv291, hv290, hv289, hv288, hv287, hv286, hv285, hv284]
      simp only [hq15, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq15d : v294 = .value q15.d := by
      simp only [hv297, hv296, hv295, hv294, hv293, hv292, hv291, hv290, hv289, hv288, hv287, hv286, hv285, hv284]
      simp only [hq15, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq15c : v295 = .value q15.c := by
      simp only [hv297, hv296, hv295, hv294, hv293, hv292, hv291, hv290, hv289, hv288, hv287, hv286, hv285, hv284]
      simp only [hq15, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq15b : v297 = .value q15.b := by
      simp only [hv297, hv296, hv295, hv294, hv293, hv292, hv291, hv290, hv289, hv288, hv287, hv286, hv285, hv284]
      simp only [hq15, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq15a, eq15d, eq15c, eq15b]
    obtain ⟨q16, hq16⟩ : ∃ q : Quad Word, q = scalarG q12.a q15.b q14.c q13.d (m 3) (m 4) := ⟨_, rfl⟩
    denote_step_all v 311
    denote_eval v 298 311
    have eq16a : v306 = .value q16.a := by
      simp only [hv311, hv310, hv309, hv308, hv307, hv306, hv305, hv304, hv303, hv302, hv301, hv300, hv299, hv298]
      simp only [hq16, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq16d : v308 = .value q16.d := by
      simp only [hv311, hv310, hv309, hv308, hv307, hv306, hv305, hv304, hv303, hv302, hv301, hv300, hv299, hv298]
      simp only [hq16, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq16c : v309 = .value q16.c := by
      simp only [hv311, hv310, hv309, hv308, hv307, hv306, hv305, hv304, hv303, hv302, hv301, hv300, hv299, hv298]
      simp only [hq16, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq16b : v311 = .value q16.b := by
      simp only [hv311, hv310, hv309, hv308, hv307, hv306, hv305, hv304, hv303, hv302, hv301, hv300, hv299, hv298]
      simp only [hq16, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq16a, eq16d, eq16c, eq16b]
    obtain ⟨q17, hq17⟩ : ∃ q : Quad Word, q = scalarG q13.a q12.b q15.c q14.d (m 10) (m 12) := ⟨_, rfl⟩
    denote_step_all v 325
    denote_eval v 312 325
    have eq17a : v320 = .value q17.a := by
      simp only [hv325, hv324, hv323, hv322, hv321, hv320, hv319, hv318, hv317, hv316, hv315, hv314, hv313, hv312]
      simp only [hq17, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq17d : v322 = .value q17.d := by
      simp only [hv325, hv324, hv323, hv322, hv321, hv320, hv319, hv318, hv317, hv316, hv315, hv314, hv313, hv312]
      simp only [hq17, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq17c : v323 = .value q17.c := by
      simp only [hv325, hv324, hv323, hv322, hv321, hv320, hv319, hv318, hv317, hv316, hv315, hv314, hv313, hv312]
      simp only [hq17, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq17b : v325 = .value q17.b := by
      simp only [hv325, hv324, hv323, hv322, hv321, hv320, hv319, hv318, hv317, hv316, hv315, hv314, hv313, hv312]
      simp only [hq17, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq17a, eq17d, eq17c, eq17b]
    obtain ⟨q18, hq18⟩ : ∃ q : Quad Word, q = scalarG q14.a q13.b q12.c q15.d (m 13) (m 2) := ⟨_, rfl⟩
    denote_step_all v 339
    denote_eval v 326 339
    have eq18a : v334 = .value q18.a := by
      simp only [hv339, hv338, hv337, hv336, hv335, hv334, hv333, hv332, hv331, hv330, hv329, hv328, hv327, hv326]
      simp only [hq18, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq18d : v336 = .value q18.d := by
      simp only [hv339, hv338, hv337, hv336, hv335, hv334, hv333, hv332, hv331, hv330, hv329, hv328, hv327, hv326]
      simp only [hq18, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq18c : v337 = .value q18.c := by
      simp only [hv339, hv338, hv337, hv336, hv335, hv334, hv333, hv332, hv331, hv330, hv329, hv328, hv327, hv326]
      simp only [hq18, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq18b : v339 = .value q18.b := by
      simp only [hv339, hv338, hv337, hv336, hv335, hv334, hv333, hv332, hv331, hv330, hv329, hv328, hv327, hv326]
      simp only [hq18, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq18a, eq18d, eq18c, eq18b]
    obtain ⟨q19, hq19⟩ : ∃ q : Quad Word, q = scalarG q15.a q14.b q13.c q12.d (m 7) (m 14) := ⟨_, rfl⟩
    denote_step_all v 353
    denote_eval v 340 353
    have eq19a : v348 = .value q19.a := by
      simp only [hv353, hv352, hv351, hv350, hv349, hv348, hv347, hv346, hv345, hv344, hv343, hv342, hv341, hv340]
      simp only [hq19, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq19d : v350 = .value q19.d := by
      simp only [hv353, hv352, hv351, hv350, hv349, hv348, hv347, hv346, hv345, hv344, hv343, hv342, hv341, hv340]
      simp only [hq19, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq19c : v351 = .value q19.c := by
      simp only [hv353, hv352, hv351, hv350, hv349, hv348, hv347, hv346, hv345, hv344, hv343, hv342, hv341, hv340]
      simp only [hq19, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq19b : v353 = .value q19.b := by
      simp only [hv353, hv352, hv351, hv350, hv349, hv348, hv347, hv346, hv345, hv344, hv343, hv342, hv341, hv340]
      simp only [hq19, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq19a, eq19d, eq19c, eq19b]
    obtain ⟨q20, hq20⟩ : ∃ q : Quad Word, q = scalarG q16.a q17.b q18.c q19.d (m 6) (m 5) := ⟨_, rfl⟩
    denote_step_all v 367
    denote_eval v 354 367
    have eq20a : v362 = .value q20.a := by
      simp only [hv367, hv366, hv365, hv364, hv363, hv362, hv361, hv360, hv359, hv358, hv357, hv356, hv355, hv354]
      simp only [hq20, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq20d : v364 = .value q20.d := by
      simp only [hv367, hv366, hv365, hv364, hv363, hv362, hv361, hv360, hv359, hv358, hv357, hv356, hv355, hv354]
      simp only [hq20, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq20c : v365 = .value q20.c := by
      simp only [hv367, hv366, hv365, hv364, hv363, hv362, hv361, hv360, hv359, hv358, hv357, hv356, hv355, hv354]
      simp only [hq20, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq20b : v367 = .value q20.b := by
      simp only [hv367, hv366, hv365, hv364, hv363, hv362, hv361, hv360, hv359, hv358, hv357, hv356, hv355, hv354]
      simp only [hq20, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq20a, eq20d, eq20c, eq20b]
    obtain ⟨q21, hq21⟩ : ∃ q : Quad Word, q = scalarG q17.a q18.b q19.c q16.d (m 9) (m 0) := ⟨_, rfl⟩
    denote_step_all v 381
    denote_eval v 368 381
    have eq21a : v376 = .value q21.a := by
      simp only [hv381, hv380, hv379, hv378, hv377, hv376, hv375, hv374, hv373, hv372, hv371, hv370, hv369, hv368]
      simp only [hq21, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq21d : v378 = .value q21.d := by
      simp only [hv381, hv380, hv379, hv378, hv377, hv376, hv375, hv374, hv373, hv372, hv371, hv370, hv369, hv368]
      simp only [hq21, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq21c : v379 = .value q21.c := by
      simp only [hv381, hv380, hv379, hv378, hv377, hv376, hv375, hv374, hv373, hv372, hv371, hv370, hv369, hv368]
      simp only [hq21, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq21b : v381 = .value q21.b := by
      simp only [hv381, hv380, hv379, hv378, hv377, hv376, hv375, hv374, hv373, hv372, hv371, hv370, hv369, hv368]
      simp only [hq21, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq21a, eq21d, eq21c, eq21b]
    obtain ⟨q22, hq22⟩ : ∃ q : Quad Word, q = scalarG q18.a q19.b q16.c q17.d (m 11) (m 15) := ⟨_, rfl⟩
    denote_step_all v 395
    denote_eval v 382 395
    have eq22a : v390 = .value q22.a := by
      simp only [hv395, hv394, hv393, hv392, hv391, hv390, hv389, hv388, hv387, hv386, hv385, hv384, hv383, hv382]
      simp only [hq22, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq22d : v392 = .value q22.d := by
      simp only [hv395, hv394, hv393, hv392, hv391, hv390, hv389, hv388, hv387, hv386, hv385, hv384, hv383, hv382]
      simp only [hq22, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq22c : v393 = .value q22.c := by
      simp only [hv395, hv394, hv393, hv392, hv391, hv390, hv389, hv388, hv387, hv386, hv385, hv384, hv383, hv382]
      simp only [hq22, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq22b : v395 = .value q22.b := by
      simp only [hv395, hv394, hv393, hv392, hv391, hv390, hv389, hv388, hv387, hv386, hv385, hv384, hv383, hv382]
      simp only [hq22, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq22a, eq22d, eq22c, eq22b]
    obtain ⟨q23, hq23⟩ : ∃ q : Quad Word, q = scalarG q19.a q16.b q17.c q18.d (m 8) (m 1) := ⟨_, rfl⟩
    denote_step_all v 409
    denote_eval v 396 409
    have eq23a : v404 = .value q23.a := by
      simp only [hv409, hv408, hv407, hv406, hv405, hv404, hv403, hv402, hv401, hv400, hv399, hv398, hv397, hv396]
      simp only [hq23, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq23d : v406 = .value q23.d := by
      simp only [hv409, hv408, hv407, hv406, hv405, hv404, hv403, hv402, hv401, hv400, hv399, hv398, hv397, hv396]
      simp only [hq23, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq23c : v407 = .value q23.c := by
      simp only [hv409, hv408, hv407, hv406, hv405, hv404, hv403, hv402, hv401, hv400, hv399, hv398, hv397, hv396]
      simp only [hq23, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq23b : v409 = .value q23.b := by
      simp only [hv409, hv408, hv407, hv406, hv405, hv404, hv403, hv402, hv401, hv400, hv399, hv398, hv397, hv396]
      simp only [hq23, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq23a, eq23d, eq23c, eq23b]
    obtain ⟨q24, hq24⟩ : ∃ q : Quad Word, q = scalarG q20.a q23.b q22.c q21.d (m 10) (m 7) := ⟨_, rfl⟩
    denote_step_all v 423
    denote_eval v 410 423
    have eq24a : v418 = .value q24.a := by
      simp only [hv423, hv422, hv421, hv420, hv419, hv418, hv417, hv416, hv415, hv414, hv413, hv412, hv411, hv410]
      simp only [hq24, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq24d : v420 = .value q24.d := by
      simp only [hv423, hv422, hv421, hv420, hv419, hv418, hv417, hv416, hv415, hv414, hv413, hv412, hv411, hv410]
      simp only [hq24, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq24c : v421 = .value q24.c := by
      simp only [hv423, hv422, hv421, hv420, hv419, hv418, hv417, hv416, hv415, hv414, hv413, hv412, hv411, hv410]
      simp only [hq24, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq24b : v423 = .value q24.b := by
      simp only [hv423, hv422, hv421, hv420, hv419, hv418, hv417, hv416, hv415, hv414, hv413, hv412, hv411, hv410]
      simp only [hq24, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq24a, eq24d, eq24c, eq24b]
    obtain ⟨q25, hq25⟩ : ∃ q : Quad Word, q = scalarG q21.a q20.b q23.c q22.d (m 12) (m 9) := ⟨_, rfl⟩
    denote_step_all v 437
    denote_eval v 424 437
    have eq25a : v432 = .value q25.a := by
      simp only [hv437, hv436, hv435, hv434, hv433, hv432, hv431, hv430, hv429, hv428, hv427, hv426, hv425, hv424]
      simp only [hq25, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq25d : v434 = .value q25.d := by
      simp only [hv437, hv436, hv435, hv434, hv433, hv432, hv431, hv430, hv429, hv428, hv427, hv426, hv425, hv424]
      simp only [hq25, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq25c : v435 = .value q25.c := by
      simp only [hv437, hv436, hv435, hv434, hv433, hv432, hv431, hv430, hv429, hv428, hv427, hv426, hv425, hv424]
      simp only [hq25, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq25b : v437 = .value q25.b := by
      simp only [hv437, hv436, hv435, hv434, hv433, hv432, hv431, hv430, hv429, hv428, hv427, hv426, hv425, hv424]
      simp only [hq25, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq25a, eq25d, eq25c, eq25b]
    obtain ⟨q26, hq26⟩ : ∃ q : Quad Word, q = scalarG q22.a q21.b q20.c q23.d (m 14) (m 3) := ⟨_, rfl⟩
    denote_step_all v 451
    denote_eval v 438 451
    have eq26a : v446 = .value q26.a := by
      simp only [hv451, hv450, hv449, hv448, hv447, hv446, hv445, hv444, hv443, hv442, hv441, hv440, hv439, hv438]
      simp only [hq26, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq26d : v448 = .value q26.d := by
      simp only [hv451, hv450, hv449, hv448, hv447, hv446, hv445, hv444, hv443, hv442, hv441, hv440, hv439, hv438]
      simp only [hq26, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq26c : v449 = .value q26.c := by
      simp only [hv451, hv450, hv449, hv448, hv447, hv446, hv445, hv444, hv443, hv442, hv441, hv440, hv439, hv438]
      simp only [hq26, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq26b : v451 = .value q26.b := by
      simp only [hv451, hv450, hv449, hv448, hv447, hv446, hv445, hv444, hv443, hv442, hv441, hv440, hv439, hv438]
      simp only [hq26, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq26a, eq26d, eq26c, eq26b]
    obtain ⟨q27, hq27⟩ : ∃ q : Quad Word, q = scalarG q23.a q22.b q21.c q20.d (m 13) (m 15) := ⟨_, rfl⟩
    denote_step_all v 465
    denote_eval v 452 465
    have eq27a : v460 = .value q27.a := by
      simp only [hv465, hv464, hv463, hv462, hv461, hv460, hv459, hv458, hv457, hv456, hv455, hv454, hv453, hv452]
      simp only [hq27, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq27d : v462 = .value q27.d := by
      simp only [hv465, hv464, hv463, hv462, hv461, hv460, hv459, hv458, hv457, hv456, hv455, hv454, hv453, hv452]
      simp only [hq27, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq27c : v463 = .value q27.c := by
      simp only [hv465, hv464, hv463, hv462, hv461, hv460, hv459, hv458, hv457, hv456, hv455, hv454, hv453, hv452]
      simp only [hq27, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq27b : v465 = .value q27.b := by
      simp only [hv465, hv464, hv463, hv462, hv461, hv460, hv459, hv458, hv457, hv456, hv455, hv454, hv453, hv452]
      simp only [hq27, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq27a, eq27d, eq27c, eq27b]
    obtain ⟨q28, hq28⟩ : ∃ q : Quad Word, q = scalarG q24.a q25.b q26.c q27.d (m 4) (m 0) := ⟨_, rfl⟩
    denote_step_all v 479
    denote_eval v 466 479
    have eq28a : v474 = .value q28.a := by
      simp only [hv479, hv478, hv477, hv476, hv475, hv474, hv473, hv472, hv471, hv470, hv469, hv468, hv467, hv466]
      simp only [hq28, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq28d : v476 = .value q28.d := by
      simp only [hv479, hv478, hv477, hv476, hv475, hv474, hv473, hv472, hv471, hv470, hv469, hv468, hv467, hv466]
      simp only [hq28, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq28c : v477 = .value q28.c := by
      simp only [hv479, hv478, hv477, hv476, hv475, hv474, hv473, hv472, hv471, hv470, hv469, hv468, hv467, hv466]
      simp only [hq28, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq28b : v479 = .value q28.b := by
      simp only [hv479, hv478, hv477, hv476, hv475, hv474, hv473, hv472, hv471, hv470, hv469, hv468, hv467, hv466]
      simp only [hq28, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq28a, eq28d, eq28c, eq28b]
    obtain ⟨q29, hq29⟩ : ∃ q : Quad Word, q = scalarG q25.a q26.b q27.c q24.d (m 11) (m 2) := ⟨_, rfl⟩
    denote_step_all v 493
    denote_eval v 480 493
    have eq29a : v488 = .value q29.a := by
      simp only [hv493, hv492, hv491, hv490, hv489, hv488, hv487, hv486, hv485, hv484, hv483, hv482, hv481, hv480]
      simp only [hq29, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq29d : v490 = .value q29.d := by
      simp only [hv493, hv492, hv491, hv490, hv489, hv488, hv487, hv486, hv485, hv484, hv483, hv482, hv481, hv480]
      simp only [hq29, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq29c : v491 = .value q29.c := by
      simp only [hv493, hv492, hv491, hv490, hv489, hv488, hv487, hv486, hv485, hv484, hv483, hv482, hv481, hv480]
      simp only [hq29, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq29b : v493 = .value q29.b := by
      simp only [hv493, hv492, hv491, hv490, hv489, hv488, hv487, hv486, hv485, hv484, hv483, hv482, hv481, hv480]
      simp only [hq29, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq29a, eq29d, eq29c, eq29b]
    obtain ⟨q30, hq30⟩ : ∃ q : Quad Word, q = scalarG q26.a q27.b q24.c q25.d (m 5) (m 8) := ⟨_, rfl⟩
    denote_step_all v 507
    denote_eval v 494 507
    have eq30a : v502 = .value q30.a := by
      simp only [hv507, hv506, hv505, hv504, hv503, hv502, hv501, hv500, hv499, hv498, hv497, hv496, hv495, hv494]
      simp only [hq30, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq30d : v504 = .value q30.d := by
      simp only [hv507, hv506, hv505, hv504, hv503, hv502, hv501, hv500, hv499, hv498, hv497, hv496, hv495, hv494]
      simp only [hq30, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq30c : v505 = .value q30.c := by
      simp only [hv507, hv506, hv505, hv504, hv503, hv502, hv501, hv500, hv499, hv498, hv497, hv496, hv495, hv494]
      simp only [hq30, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq30b : v507 = .value q30.b := by
      simp only [hv507, hv506, hv505, hv504, hv503, hv502, hv501, hv500, hv499, hv498, hv497, hv496, hv495, hv494]
      simp only [hq30, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq30a, eq30d, eq30c, eq30b]
    obtain ⟨q31, hq31⟩ : ∃ q : Quad Word, q = scalarG q27.a q24.b q25.c q26.d (m 1) (m 6) := ⟨_, rfl⟩
    denote_step_all v 521
    denote_eval v 508 521
    have eq31a : v516 = .value q31.a := by
      simp only [hv521, hv520, hv519, hv518, hv517, hv516, hv515, hv514, hv513, hv512, hv511, hv510, hv509, hv508]
      simp only [hq31, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq31d : v518 = .value q31.d := by
      simp only [hv521, hv520, hv519, hv518, hv517, hv516, hv515, hv514, hv513, hv512, hv511, hv510, hv509, hv508]
      simp only [hq31, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq31c : v519 = .value q31.c := by
      simp only [hv521, hv520, hv519, hv518, hv517, hv516, hv515, hv514, hv513, hv512, hv511, hv510, hv509, hv508]
      simp only [hq31, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq31b : v521 = .value q31.b := by
      simp only [hv521, hv520, hv519, hv518, hv517, hv516, hv515, hv514, hv513, hv512, hv511, hv510, hv509, hv508]
      simp only [hq31, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq31a, eq31d, eq31c, eq31b]
    obtain ⟨q32, hq32⟩ : ∃ q : Quad Word, q = scalarG q28.a q31.b q30.c q29.d (m 12) (m 13) := ⟨_, rfl⟩
    denote_step_all v 535
    denote_eval v 522 535
    have eq32a : v530 = .value q32.a := by
      simp only [hv535, hv534, hv533, hv532, hv531, hv530, hv529, hv528, hv527, hv526, hv525, hv524, hv523, hv522]
      simp only [hq32, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq32d : v532 = .value q32.d := by
      simp only [hv535, hv534, hv533, hv532, hv531, hv530, hv529, hv528, hv527, hv526, hv525, hv524, hv523, hv522]
      simp only [hq32, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq32c : v533 = .value q32.c := by
      simp only [hv535, hv534, hv533, hv532, hv531, hv530, hv529, hv528, hv527, hv526, hv525, hv524, hv523, hv522]
      simp only [hq32, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq32b : v535 = .value q32.b := by
      simp only [hv535, hv534, hv533, hv532, hv531, hv530, hv529, hv528, hv527, hv526, hv525, hv524, hv523, hv522]
      simp only [hq32, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq32a, eq32d, eq32c, eq32b]
    obtain ⟨q33, hq33⟩ : ∃ q : Quad Word, q = scalarG q29.a q28.b q31.c q30.d (m 9) (m 11) := ⟨_, rfl⟩
    denote_step_all v 549
    denote_eval v 536 549
    have eq33a : v544 = .value q33.a := by
      simp only [hv549, hv548, hv547, hv546, hv545, hv544, hv543, hv542, hv541, hv540, hv539, hv538, hv537, hv536]
      simp only [hq33, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq33d : v546 = .value q33.d := by
      simp only [hv549, hv548, hv547, hv546, hv545, hv544, hv543, hv542, hv541, hv540, hv539, hv538, hv537, hv536]
      simp only [hq33, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq33c : v547 = .value q33.c := by
      simp only [hv549, hv548, hv547, hv546, hv545, hv544, hv543, hv542, hv541, hv540, hv539, hv538, hv537, hv536]
      simp only [hq33, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq33b : v549 = .value q33.b := by
      simp only [hv549, hv548, hv547, hv546, hv545, hv544, hv543, hv542, hv541, hv540, hv539, hv538, hv537, hv536]
      simp only [hq33, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq33a, eq33d, eq33c, eq33b]
    obtain ⟨q34, hq34⟩ : ∃ q : Quad Word, q = scalarG q30.a q29.b q28.c q31.d (m 15) (m 10) := ⟨_, rfl⟩
    denote_step_all v 563
    denote_eval v 550 563
    have eq34a : v558 = .value q34.a := by
      simp only [hv563, hv562, hv561, hv560, hv559, hv558, hv557, hv556, hv555, hv554, hv553, hv552, hv551, hv550]
      simp only [hq34, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq34d : v560 = .value q34.d := by
      simp only [hv563, hv562, hv561, hv560, hv559, hv558, hv557, hv556, hv555, hv554, hv553, hv552, hv551, hv550]
      simp only [hq34, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq34c : v561 = .value q34.c := by
      simp only [hv563, hv562, hv561, hv560, hv559, hv558, hv557, hv556, hv555, hv554, hv553, hv552, hv551, hv550]
      simp only [hq34, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq34b : v563 = .value q34.b := by
      simp only [hv563, hv562, hv561, hv560, hv559, hv558, hv557, hv556, hv555, hv554, hv553, hv552, hv551, hv550]
      simp only [hq34, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq34a, eq34d, eq34c, eq34b]
    obtain ⟨q35, hq35⟩ : ∃ q : Quad Word, q = scalarG q31.a q30.b q29.c q28.d (m 14) (m 8) := ⟨_, rfl⟩
    denote_step_all v 577
    denote_eval v 564 577
    have eq35a : v572 = .value q35.a := by
      simp only [hv577, hv576, hv575, hv574, hv573, hv572, hv571, hv570, hv569, hv568, hv567, hv566, hv565, hv564]
      simp only [hq35, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq35d : v574 = .value q35.d := by
      simp only [hv577, hv576, hv575, hv574, hv573, hv572, hv571, hv570, hv569, hv568, hv567, hv566, hv565, hv564]
      simp only [hq35, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq35c : v575 = .value q35.c := by
      simp only [hv577, hv576, hv575, hv574, hv573, hv572, hv571, hv570, hv569, hv568, hv567, hv566, hv565, hv564]
      simp only [hq35, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq35b : v577 = .value q35.b := by
      simp only [hv577, hv576, hv575, hv574, hv573, hv572, hv571, hv570, hv569, hv568, hv567, hv566, hv565, hv564]
      simp only [hq35, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq35a, eq35d, eq35c, eq35b]
    obtain ⟨q36, hq36⟩ : ∃ q : Quad Word, q = scalarG q32.a q33.b q34.c q35.d (m 7) (m 2) := ⟨_, rfl⟩
    denote_step_all v 591
    denote_eval v 578 591
    have eq36a : v586 = .value q36.a := by
      simp only [hv591, hv590, hv589, hv588, hv587, hv586, hv585, hv584, hv583, hv582, hv581, hv580, hv579, hv578]
      simp only [hq36, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq36d : v588 = .value q36.d := by
      simp only [hv591, hv590, hv589, hv588, hv587, hv586, hv585, hv584, hv583, hv582, hv581, hv580, hv579, hv578]
      simp only [hq36, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq36c : v589 = .value q36.c := by
      simp only [hv591, hv590, hv589, hv588, hv587, hv586, hv585, hv584, hv583, hv582, hv581, hv580, hv579, hv578]
      simp only [hq36, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq36b : v591 = .value q36.b := by
      simp only [hv591, hv590, hv589, hv588, hv587, hv586, hv585, hv584, hv583, hv582, hv581, hv580, hv579, hv578]
      simp only [hq36, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq36a, eq36d, eq36c, eq36b]
    obtain ⟨q37, hq37⟩ : ∃ q : Quad Word, q = scalarG q33.a q34.b q35.c q32.d (m 5) (m 3) := ⟨_, rfl⟩
    denote_step_all v 605
    denote_eval v 592 605
    have eq37a : v600 = .value q37.a := by
      simp only [hv605, hv604, hv603, hv602, hv601, hv600, hv599, hv598, hv597, hv596, hv595, hv594, hv593, hv592]
      simp only [hq37, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq37d : v602 = .value q37.d := by
      simp only [hv605, hv604, hv603, hv602, hv601, hv600, hv599, hv598, hv597, hv596, hv595, hv594, hv593, hv592]
      simp only [hq37, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq37c : v603 = .value q37.c := by
      simp only [hv605, hv604, hv603, hv602, hv601, hv600, hv599, hv598, hv597, hv596, hv595, hv594, hv593, hv592]
      simp only [hq37, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq37b : v605 = .value q37.b := by
      simp only [hv605, hv604, hv603, hv602, hv601, hv600, hv599, hv598, hv597, hv596, hv595, hv594, hv593, hv592]
      simp only [hq37, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq37a, eq37d, eq37c, eq37b]
    obtain ⟨q38, hq38⟩ : ∃ q : Quad Word, q = scalarG q34.a q35.b q32.c q33.d (m 0) (m 1) := ⟨_, rfl⟩
    denote_step_all v 619
    denote_eval v 606 619
    have eq38a : v614 = .value q38.a := by
      simp only [hv619, hv618, hv617, hv616, hv615, hv614, hv613, hv612, hv611, hv610, hv609, hv608, hv607, hv606]
      simp only [hq38, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq38d : v616 = .value q38.d := by
      simp only [hv619, hv618, hv617, hv616, hv615, hv614, hv613, hv612, hv611, hv610, hv609, hv608, hv607, hv606]
      simp only [hq38, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq38c : v617 = .value q38.c := by
      simp only [hv619, hv618, hv617, hv616, hv615, hv614, hv613, hv612, hv611, hv610, hv609, hv608, hv607, hv606]
      simp only [hq38, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq38b : v619 = .value q38.b := by
      simp only [hv619, hv618, hv617, hv616, hv615, hv614, hv613, hv612, hv611, hv610, hv609, hv608, hv607, hv606]
      simp only [hq38, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq38a, eq38d, eq38c, eq38b]
    obtain ⟨q39, hq39⟩ : ∃ q : Quad Word, q = scalarG q35.a q32.b q33.c q34.d (m 6) (m 4) := ⟨_, rfl⟩
    denote_step_all v 633
    denote_eval v 620 633
    have eq39a : v628 = .value q39.a := by
      simp only [hv633, hv632, hv631, hv630, hv629, hv628, hv627, hv626, hv625, hv624, hv623, hv622, hv621, hv620]
      simp only [hq39, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq39d : v630 = .value q39.d := by
      simp only [hv633, hv632, hv631, hv630, hv629, hv628, hv627, hv626, hv625, hv624, hv623, hv622, hv621, hv620]
      simp only [hq39, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq39c : v631 = .value q39.c := by
      simp only [hv633, hv632, hv631, hv630, hv629, hv628, hv627, hv626, hv625, hv624, hv623, hv622, hv621, hv620]
      simp only [hq39, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq39b : v633 = .value q39.b := by
      simp only [hv633, hv632, hv631, hv630, hv629, hv628, hv627, hv626, hv625, hv624, hv623, hv622, hv621, hv620]
      simp only [hq39, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq39a, eq39d, eq39c, eq39b]
    obtain ⟨q40, hq40⟩ : ∃ q : Quad Word, q = scalarG q36.a q39.b q38.c q37.d (m 9) (m 14) := ⟨_, rfl⟩
    denote_step_all v 647
    denote_eval v 634 647
    have eq40a : v642 = .value q40.a := by
      simp only [hv647, hv646, hv645, hv644, hv643, hv642, hv641, hv640, hv639, hv638, hv637, hv636, hv635, hv634]
      simp only [hq40, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq40d : v644 = .value q40.d := by
      simp only [hv647, hv646, hv645, hv644, hv643, hv642, hv641, hv640, hv639, hv638, hv637, hv636, hv635, hv634]
      simp only [hq40, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq40c : v645 = .value q40.c := by
      simp only [hv647, hv646, hv645, hv644, hv643, hv642, hv641, hv640, hv639, hv638, hv637, hv636, hv635, hv634]
      simp only [hq40, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq40b : v647 = .value q40.b := by
      simp only [hv647, hv646, hv645, hv644, hv643, hv642, hv641, hv640, hv639, hv638, hv637, hv636, hv635, hv634]
      simp only [hq40, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq40a, eq40d, eq40c, eq40b]
    obtain ⟨q41, hq41⟩ : ∃ q : Quad Word, q = scalarG q37.a q36.b q39.c q38.d (m 11) (m 5) := ⟨_, rfl⟩
    denote_step_all v 661
    denote_eval v 648 661
    have eq41a : v656 = .value q41.a := by
      simp only [hv661, hv660, hv659, hv658, hv657, hv656, hv655, hv654, hv653, hv652, hv651, hv650, hv649, hv648]
      simp only [hq41, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq41d : v658 = .value q41.d := by
      simp only [hv661, hv660, hv659, hv658, hv657, hv656, hv655, hv654, hv653, hv652, hv651, hv650, hv649, hv648]
      simp only [hq41, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq41c : v659 = .value q41.c := by
      simp only [hv661, hv660, hv659, hv658, hv657, hv656, hv655, hv654, hv653, hv652, hv651, hv650, hv649, hv648]
      simp only [hq41, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq41b : v661 = .value q41.b := by
      simp only [hv661, hv660, hv659, hv658, hv657, hv656, hv655, hv654, hv653, hv652, hv651, hv650, hv649, hv648]
      simp only [hq41, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq41a, eq41d, eq41c, eq41b]
    obtain ⟨q42, hq42⟩ : ∃ q : Quad Word, q = scalarG q38.a q37.b q36.c q39.d (m 8) (m 12) := ⟨_, rfl⟩
    denote_step_all v 675
    denote_eval v 662 675
    have eq42a : v670 = .value q42.a := by
      simp only [hv675, hv674, hv673, hv672, hv671, hv670, hv669, hv668, hv667, hv666, hv665, hv664, hv663, hv662]
      simp only [hq42, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq42d : v672 = .value q42.d := by
      simp only [hv675, hv674, hv673, hv672, hv671, hv670, hv669, hv668, hv667, hv666, hv665, hv664, hv663, hv662]
      simp only [hq42, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq42c : v673 = .value q42.c := by
      simp only [hv675, hv674, hv673, hv672, hv671, hv670, hv669, hv668, hv667, hv666, hv665, hv664, hv663, hv662]
      simp only [hq42, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq42b : v675 = .value q42.b := by
      simp only [hv675, hv674, hv673, hv672, hv671, hv670, hv669, hv668, hv667, hv666, hv665, hv664, hv663, hv662]
      simp only [hq42, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq42a, eq42d, eq42c, eq42b]
    obtain ⟨q43, hq43⟩ : ∃ q : Quad Word, q = scalarG q39.a q38.b q37.c q36.d (m 15) (m 1) := ⟨_, rfl⟩
    denote_step_all v 689
    denote_eval v 676 689
    have eq43a : v684 = .value q43.a := by
      simp only [hv689, hv688, hv687, hv686, hv685, hv684, hv683, hv682, hv681, hv680, hv679, hv678, hv677, hv676]
      simp only [hq43, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq43d : v686 = .value q43.d := by
      simp only [hv689, hv688, hv687, hv686, hv685, hv684, hv683, hv682, hv681, hv680, hv679, hv678, hv677, hv676]
      simp only [hq43, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq43c : v687 = .value q43.c := by
      simp only [hv689, hv688, hv687, hv686, hv685, hv684, hv683, hv682, hv681, hv680, hv679, hv678, hv677, hv676]
      simp only [hq43, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq43b : v689 = .value q43.b := by
      simp only [hv689, hv688, hv687, hv686, hv685, hv684, hv683, hv682, hv681, hv680, hv679, hv678, hv677, hv676]
      simp only [hq43, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq43a, eq43d, eq43c, eq43b]
    obtain ⟨q44, hq44⟩ : ∃ q : Quad Word, q = scalarG q40.a q41.b q42.c q43.d (m 13) (m 3) := ⟨_, rfl⟩
    denote_step_all v 703
    denote_eval v 690 703
    have eq44a : v698 = .value q44.a := by
      simp only [hv703, hv702, hv701, hv700, hv699, hv698, hv697, hv696, hv695, hv694, hv693, hv692, hv691, hv690]
      simp only [hq44, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq44d : v700 = .value q44.d := by
      simp only [hv703, hv702, hv701, hv700, hv699, hv698, hv697, hv696, hv695, hv694, hv693, hv692, hv691, hv690]
      simp only [hq44, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq44c : v701 = .value q44.c := by
      simp only [hv703, hv702, hv701, hv700, hv699, hv698, hv697, hv696, hv695, hv694, hv693, hv692, hv691, hv690]
      simp only [hq44, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq44b : v703 = .value q44.b := by
      simp only [hv703, hv702, hv701, hv700, hv699, hv698, hv697, hv696, hv695, hv694, hv693, hv692, hv691, hv690]
      simp only [hq44, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq44a, eq44d, eq44c, eq44b]
    obtain ⟨q45, hq45⟩ : ∃ q : Quad Word, q = scalarG q41.a q42.b q43.c q40.d (m 0) (m 10) := ⟨_, rfl⟩
    denote_step_all v 717
    denote_eval v 704 717
    have eq45a : v712 = .value q45.a := by
      simp only [hv717, hv716, hv715, hv714, hv713, hv712, hv711, hv710, hv709, hv708, hv707, hv706, hv705, hv704]
      simp only [hq45, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq45d : v714 = .value q45.d := by
      simp only [hv717, hv716, hv715, hv714, hv713, hv712, hv711, hv710, hv709, hv708, hv707, hv706, hv705, hv704]
      simp only [hq45, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq45c : v715 = .value q45.c := by
      simp only [hv717, hv716, hv715, hv714, hv713, hv712, hv711, hv710, hv709, hv708, hv707, hv706, hv705, hv704]
      simp only [hq45, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq45b : v717 = .value q45.b := by
      simp only [hv717, hv716, hv715, hv714, hv713, hv712, hv711, hv710, hv709, hv708, hv707, hv706, hv705, hv704]
      simp only [hq45, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq45a, eq45d, eq45c, eq45b]
    obtain ⟨q46, hq46⟩ : ∃ q : Quad Word, q = scalarG q42.a q43.b q40.c q41.d (m 2) (m 6) := ⟨_, rfl⟩
    denote_step_all v 731
    denote_eval v 718 731
    have eq46a : v726 = .value q46.a := by
      simp only [hv731, hv730, hv729, hv728, hv727, hv726, hv725, hv724, hv723, hv722, hv721, hv720, hv719, hv718]
      simp only [hq46, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq46d : v728 = .value q46.d := by
      simp only [hv731, hv730, hv729, hv728, hv727, hv726, hv725, hv724, hv723, hv722, hv721, hv720, hv719, hv718]
      simp only [hq46, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq46c : v729 = .value q46.c := by
      simp only [hv731, hv730, hv729, hv728, hv727, hv726, hv725, hv724, hv723, hv722, hv721, hv720, hv719, hv718]
      simp only [hq46, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq46b : v731 = .value q46.b := by
      simp only [hv731, hv730, hv729, hv728, hv727, hv726, hv725, hv724, hv723, hv722, hv721, hv720, hv719, hv718]
      simp only [hq46, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq46a, eq46d, eq46c, eq46b]
    obtain ⟨q47, hq47⟩ : ∃ q : Quad Word, q = scalarG q43.a q40.b q41.c q42.d (m 4) (m 7) := ⟨_, rfl⟩
    denote_step_all v 745
    denote_eval v 732 745
    have eq47a : v740 = .value q47.a := by
      simp only [hv745, hv744, hv743, hv742, hv741, hv740, hv739, hv738, hv737, hv736, hv735, hv734, hv733, hv732]
      simp only [hq47, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq47d : v742 = .value q47.d := by
      simp only [hv745, hv744, hv743, hv742, hv741, hv740, hv739, hv738, hv737, hv736, hv735, hv734, hv733, hv732]
      simp only [hq47, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq47c : v743 = .value q47.c := by
      simp only [hv745, hv744, hv743, hv742, hv741, hv740, hv739, hv738, hv737, hv736, hv735, hv734, hv733, hv732]
      simp only [hq47, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq47b : v745 = .value q47.b := by
      simp only [hv745, hv744, hv743, hv742, hv741, hv740, hv739, hv738, hv737, hv736, hv735, hv734, hv733, hv732]
      simp only [hq47, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq47a, eq47d, eq47c, eq47b]
    obtain ⟨q48, hq48⟩ : ∃ q : Quad Word, q = scalarG q44.a q47.b q46.c q45.d (m 11) (m 15) := ⟨_, rfl⟩
    denote_step_all v 759
    denote_eval v 746 759
    have eq48a : v754 = .value q48.a := by
      simp only [hv759, hv758, hv757, hv756, hv755, hv754, hv753, hv752, hv751, hv750, hv749, hv748, hv747, hv746]
      simp only [hq48, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq48d : v756 = .value q48.d := by
      simp only [hv759, hv758, hv757, hv756, hv755, hv754, hv753, hv752, hv751, hv750, hv749, hv748, hv747, hv746]
      simp only [hq48, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq48c : v757 = .value q48.c := by
      simp only [hv759, hv758, hv757, hv756, hv755, hv754, hv753, hv752, hv751, hv750, hv749, hv748, hv747, hv746]
      simp only [hq48, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq48b : v759 = .value q48.b := by
      simp only [hv759, hv758, hv757, hv756, hv755, hv754, hv753, hv752, hv751, hv750, hv749, hv748, hv747, hv746]
      simp only [hq48, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq48a, eq48d, eq48c, eq48b]
    obtain ⟨q49, hq49⟩ : ∃ q : Quad Word, q = scalarG q45.a q44.b q47.c q46.d (m 5) (m 0) := ⟨_, rfl⟩
    denote_step_all v 773
    denote_eval v 760 773
    have eq49a : v768 = .value q49.a := by
      simp only [hv773, hv772, hv771, hv770, hv769, hv768, hv767, hv766, hv765, hv764, hv763, hv762, hv761, hv760]
      simp only [hq49, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq49d : v770 = .value q49.d := by
      simp only [hv773, hv772, hv771, hv770, hv769, hv768, hv767, hv766, hv765, hv764, hv763, hv762, hv761, hv760]
      simp only [hq49, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq49c : v771 = .value q49.c := by
      simp only [hv773, hv772, hv771, hv770, hv769, hv768, hv767, hv766, hv765, hv764, hv763, hv762, hv761, hv760]
      simp only [hq49, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq49b : v773 = .value q49.b := by
      simp only [hv773, hv772, hv771, hv770, hv769, hv768, hv767, hv766, hv765, hv764, hv763, hv762, hv761, hv760]
      simp only [hq49, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq49a, eq49d, eq49c, eq49b]
    obtain ⟨q50, hq50⟩ : ∃ q : Quad Word, q = scalarG q46.a q45.b q44.c q47.d (m 1) (m 9) := ⟨_, rfl⟩
    denote_step_all v 787
    denote_eval v 774 787
    have eq50a : v782 = .value q50.a := by
      simp only [hv787, hv786, hv785, hv784, hv783, hv782, hv781, hv780, hv779, hv778, hv777, hv776, hv775, hv774]
      simp only [hq50, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq50d : v784 = .value q50.d := by
      simp only [hv787, hv786, hv785, hv784, hv783, hv782, hv781, hv780, hv779, hv778, hv777, hv776, hv775, hv774]
      simp only [hq50, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq50c : v785 = .value q50.c := by
      simp only [hv787, hv786, hv785, hv784, hv783, hv782, hv781, hv780, hv779, hv778, hv777, hv776, hv775, hv774]
      simp only [hq50, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq50b : v787 = .value q50.b := by
      simp only [hv787, hv786, hv785, hv784, hv783, hv782, hv781, hv780, hv779, hv778, hv777, hv776, hv775, hv774]
      simp only [hq50, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq50a, eq50d, eq50c, eq50b]
    obtain ⟨q51, hq51⟩ : ∃ q : Quad Word, q = scalarG q47.a q46.b q45.c q44.d (m 8) (m 6) := ⟨_, rfl⟩
    denote_step_all v 801
    denote_eval v 788 801
    have eq51a : v796 = .value q51.a := by
      simp only [hv801, hv800, hv799, hv798, hv797, hv796, hv795, hv794, hv793, hv792, hv791, hv790, hv789, hv788]
      simp only [hq51, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq51d : v798 = .value q51.d := by
      simp only [hv801, hv800, hv799, hv798, hv797, hv796, hv795, hv794, hv793, hv792, hv791, hv790, hv789, hv788]
      simp only [hq51, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq51c : v799 = .value q51.c := by
      simp only [hv801, hv800, hv799, hv798, hv797, hv796, hv795, hv794, hv793, hv792, hv791, hv790, hv789, hv788]
      simp only [hq51, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq51b : v801 = .value q51.b := by
      simp only [hv801, hv800, hv799, hv798, hv797, hv796, hv795, hv794, hv793, hv792, hv791, hv790, hv789, hv788]
      simp only [hq51, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq51a, eq51d, eq51c, eq51b]
    obtain ⟨q52, hq52⟩ : ∃ q : Quad Word, q = scalarG q48.a q49.b q50.c q51.d (m 14) (m 10) := ⟨_, rfl⟩
    denote_step_all v 815
    denote_eval v 802 815
    have eq52a : v810 = .value q52.a := by
      simp only [hv815, hv814, hv813, hv812, hv811, hv810, hv809, hv808, hv807, hv806, hv805, hv804, hv803, hv802]
      simp only [hq52, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq52d : v812 = .value q52.d := by
      simp only [hv815, hv814, hv813, hv812, hv811, hv810, hv809, hv808, hv807, hv806, hv805, hv804, hv803, hv802]
      simp only [hq52, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq52c : v813 = .value q52.c := by
      simp only [hv815, hv814, hv813, hv812, hv811, hv810, hv809, hv808, hv807, hv806, hv805, hv804, hv803, hv802]
      simp only [hq52, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq52b : v815 = .value q52.b := by
      simp only [hv815, hv814, hv813, hv812, hv811, hv810, hv809, hv808, hv807, hv806, hv805, hv804, hv803, hv802]
      simp only [hq52, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq52a, eq52d, eq52c, eq52b]
    obtain ⟨q53, hq53⟩ : ∃ q : Quad Word, q = scalarG q49.a q50.b q51.c q48.d (m 2) (m 12) := ⟨_, rfl⟩
    denote_step_all v 829
    denote_eval v 816 829
    have eq53a : v824 = .value q53.a := by
      simp only [hv829, hv828, hv827, hv826, hv825, hv824, hv823, hv822, hv821, hv820, hv819, hv818, hv817, hv816]
      simp only [hq53, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq53d : v826 = .value q53.d := by
      simp only [hv829, hv828, hv827, hv826, hv825, hv824, hv823, hv822, hv821, hv820, hv819, hv818, hv817, hv816]
      simp only [hq53, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq53c : v827 = .value q53.c := by
      simp only [hv829, hv828, hv827, hv826, hv825, hv824, hv823, hv822, hv821, hv820, hv819, hv818, hv817, hv816]
      simp only [hq53, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq53b : v829 = .value q53.b := by
      simp only [hv829, hv828, hv827, hv826, hv825, hv824, hv823, hv822, hv821, hv820, hv819, hv818, hv817, hv816]
      simp only [hq53, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq53a, eq53d, eq53c, eq53b]
    obtain ⟨q54, hq54⟩ : ∃ q : Quad Word, q = scalarG q50.a q51.b q48.c q49.d (m 3) (m 4) := ⟨_, rfl⟩
    denote_step_all v 843
    denote_eval v 830 843
    have eq54a : v838 = .value q54.a := by
      simp only [hv843, hv842, hv841, hv840, hv839, hv838, hv837, hv836, hv835, hv834, hv833, hv832, hv831, hv830]
      simp only [hq54, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq54d : v840 = .value q54.d := by
      simp only [hv843, hv842, hv841, hv840, hv839, hv838, hv837, hv836, hv835, hv834, hv833, hv832, hv831, hv830]
      simp only [hq54, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq54c : v841 = .value q54.c := by
      simp only [hv843, hv842, hv841, hv840, hv839, hv838, hv837, hv836, hv835, hv834, hv833, hv832, hv831, hv830]
      simp only [hq54, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq54b : v843 = .value q54.b := by
      simp only [hv843, hv842, hv841, hv840, hv839, hv838, hv837, hv836, hv835, hv834, hv833, hv832, hv831, hv830]
      simp only [hq54, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq54a, eq54d, eq54c, eq54b]
    obtain ⟨q55, hq55⟩ : ∃ q : Quad Word, q = scalarG q51.a q48.b q49.c q50.d (m 7) (m 13) := ⟨_, rfl⟩
    denote_step_all v 857
    denote_eval v 844 857
    have eq55a : v852 = .value q55.a := by
      simp only [hv857, hv856, hv855, hv854, hv853, hv852, hv851, hv850, hv849, hv848, hv847, hv846, hv845, hv844]
      simp only [hq55, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq55d : v854 = .value q55.d := by
      simp only [hv857, hv856, hv855, hv854, hv853, hv852, hv851, hv850, hv849, hv848, hv847, hv846, hv845, hv844]
      simp only [hq55, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq55c : v855 = .value q55.c := by
      simp only [hv857, hv856, hv855, hv854, hv853, hv852, hv851, hv850, hv849, hv848, hv847, hv846, hv845, hv844]
      simp only [hq55, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    have eq55b : v857 = .value q55.b := by
      simp only [hv857, hv856, hv855, hv854, hv853, hv852, hv851, hv850, hv849, hv848, hv847, hv846, hv845, hv844]
      simp only [hq55, ← compiledG_eq]
      simp [compiledG, simp_llvm, simp_llvm_option, fshl]
    rw [eq55a, eq55d, eq55c, eq55b]
    obtain ⟨s1, hs1⟩ : ∃ t : GlobalState, t = { s with mem := s.mem.splice out q52.a } := ⟨_, rfl⟩
    peel_store q52.a, out, hout, s as s1 := hs1
    have hout_prev1 : Fits s1.mem out 512 := by
      rw [hs1]
      exact fits_splice hout
    peel_gep 4 with out, hout_prev1, s1 as out1
    obtain ⟨s2, hs2⟩ : ∃ t : GlobalState, t = { s1 with mem := s1.mem.splice out1 q53.a } := ⟨_, rfl⟩
    peel_store q53.a, out1, hout1, s1 as s2 := hs2
    have hout_prev2 : Fits s2.mem out 512 := by
      rw [hs2]
      exact fits_splice hout_prev1
    peel_gep 8 with out, hout_prev2, s2 as out2
    obtain ⟨s3, hs3⟩ : ∃ t : GlobalState, t = { s2 with mem := s2.mem.splice out2 q54.a } := ⟨_, rfl⟩
    peel_store q54.a, out2, hout2, s2 as s3 := hs3
    have hout_prev3 : Fits s3.mem out 512 := by
      rw [hs3]
      exact fits_splice hout_prev2
    peel_gep 12 with out, hout_prev3, s3 as out3
    obtain ⟨s4, hs4⟩ : ∃ t : GlobalState, t = { s3 with mem := s3.mem.splice out3 q55.a } := ⟨_, rfl⟩
    peel_store q55.a, out3, hout3, s3 as s4 := hs4
    have hout_prev4 : Fits s4.mem out 512 := by
      rw [hs4]
      exact fits_splice hout_prev3
    peel_gep 16 with out, hout_prev4, s4 as out4
    obtain ⟨s5, hs5⟩ : ∃ t : GlobalState, t = { s4 with mem := s4.mem.splice out4 q55.b } := ⟨_, rfl⟩
    peel_store q55.b, out4, hout4, s4 as s5 := hs5
    have hout_prev5 : Fits s5.mem out 512 := by
      rw [hs5]
      exact fits_splice hout_prev4
    peel_gep 20 with out, hout_prev5, s5 as out5
    obtain ⟨s6, hs6⟩ : ∃ t : GlobalState, t = { s5 with mem := s5.mem.splice out5 q52.b } := ⟨_, rfl⟩
    peel_store q52.b, out5, hout5, s5 as s6 := hs6
    have hout_prev6 : Fits s6.mem out 512 := by
      rw [hs6]
      exact fits_splice hout_prev5
    peel_gep 24 with out, hout_prev6, s6 as out6
    obtain ⟨s7, hs7⟩ : ∃ t : GlobalState, t = { s6 with mem := s6.mem.splice out6 q53.b } := ⟨_, rfl⟩
    peel_store q53.b, out6, hout6, s6 as s7 := hs7
    have hout_prev7 : Fits s7.mem out 512 := by
      rw [hs7]
      exact fits_splice hout_prev6
    peel_gep 28 with out, hout_prev7, s7 as out7
    obtain ⟨s8, hs8⟩ : ∃ t : GlobalState, t = { s7 with mem := s7.mem.splice out7 q54.b } := ⟨_, rfl⟩
    peel_store q54.b, out7, hout7, s7 as s8 := hs8
    have hout_prev8 : Fits s8.mem out 512 := by
      rw [hs8]
      exact fits_splice hout_prev7
    peel_gep 32 with out, hout_prev8, s8 as out8
    obtain ⟨s9, hs9⟩ : ∃ t : GlobalState, t = { s8 with mem := s8.mem.splice out8 q54.c } := ⟨_, rfl⟩
    peel_store q54.c, out8, hout8, s8 as s9 := hs9
    have hout_prev9 : Fits s9.mem out 512 := by
      rw [hs9]
      exact fits_splice hout_prev8
    peel_gep 36 with out, hout_prev9, s9 as out9
    obtain ⟨s10, hs10⟩ : ∃ t : GlobalState, t = { s9 with mem := s9.mem.splice out9 q55.c } := ⟨_, rfl⟩
    peel_store q55.c, out9, hout9, s9 as s10 := hs10
    have hout_prev10 : Fits s10.mem out 512 := by
      rw [hs10]
      exact fits_splice hout_prev9
    peel_gep 40 with out, hout_prev10, s10 as out10
    obtain ⟨s11, hs11⟩ : ∃ t : GlobalState, t = { s10 with mem := s10.mem.splice out10 q52.c } := ⟨_, rfl⟩
    peel_store q52.c, out10, hout10, s10 as s11 := hs11
    have hout_prev11 : Fits s11.mem out 512 := by
      rw [hs11]
      exact fits_splice hout_prev10
    peel_gep 44 with out, hout_prev11, s11 as out11
    obtain ⟨s12, hs12⟩ : ∃ t : GlobalState, t = { s11 with mem := s11.mem.splice out11 q53.c } := ⟨_, rfl⟩
    peel_store q53.c, out11, hout11, s11 as s12 := hs12
    have hout_prev12 : Fits s12.mem out 512 := by
      rw [hs12]
      exact fits_splice hout_prev11
    peel_gep 48 with out, hout_prev12, s12 as out12
    obtain ⟨s13, hs13⟩ : ∃ t : GlobalState, t = { s12 with mem := s12.mem.splice out12 q53.d } := ⟨_, rfl⟩
    peel_store q53.d, out12, hout12, s12 as s13 := hs13
    have hout_prev13 : Fits s13.mem out 512 := by
      rw [hs13]
      exact fits_splice hout_prev12
    peel_gep 52 with out, hout_prev13, s13 as out13
    obtain ⟨s14, hs14⟩ : ∃ t : GlobalState, t = { s13 with mem := s13.mem.splice out13 q54.d } := ⟨_, rfl⟩
    peel_store q54.d, out13, hout13, s13 as s14 := hs14
    have hout_prev14 : Fits s14.mem out 512 := by
      rw [hs14]
      exact fits_splice hout_prev13
    peel_gep 56 with out, hout_prev14, s14 as out14
    obtain ⟨s15, hs15⟩ : ∃ t : GlobalState, t = { s14 with mem := s14.mem.splice out14 q55.d } := ⟨_, rfl⟩
    peel_store q55.d, out14, hout14, s14 as s15 := hs15
    have hout_prev15 : Fits s15.mem out 512 := by
      rw [hs15]
      exact fits_splice hout_prev14
    peel_gep 60 with out, hout_prev15, s15 as out15
    obtain ⟨s16, hs16⟩ : ∃ t : GlobalState, t = { s15 with mem := s15.mem.splice out15 q52.d } := ⟨_, rfl⟩
    peel_store q52.d, out15, hout15, s15 as s16 := hs16
    have hresult := portableRounds_eq cv m counter len flags
      q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55
      hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 hq10 hq11 hq12 hq13 hq14 hq15 hq16 hq17 hq18 hq19 hq20 hq21 hq22 hq23 hq24 hq25 hq26 hq27 hq28 hq29 hq30 hq31 hq32 hq33 hq34 hq35 hq36 hq37 hq38 hq39 hq40 hq41 hq42 hq43 hq44 hq45 hq46 hq47 hq48 hq49 hq50 hq51 hq52 hq53 hq54 hq55
    rw [← hresult]
    simp_return
    have state1 : s1 = {s with mem := CompressionExit.outputMem out (fun j => #v[portableRoundState q52 q53 q54 q55 j]) 1 s.mem} :=
      portableStateStep out (portableRoundState q52 q53 q54 q55) s 0 s s1 rfl (by simpa [portableRoundState, Pointer.withOffset] using hs1)
    have state2 : s2 = {s with mem := CompressionExit.outputMem out (fun j => #v[portableRoundState q52 q53 q54 q55 j]) 2 s.mem} :=
      portableStateStep out (portableRoundState q52 q53 q54 q55) s 1 s1 s2 state1 (by simpa [portableRoundState, Pointer.withOffset, out1] using hs2)
    have state3 : s3 = {s with mem := CompressionExit.outputMem out (fun j => #v[portableRoundState q52 q53 q54 q55 j]) 3 s.mem} :=
      portableStateStep out (portableRoundState q52 q53 q54 q55) s 2 s2 s3 state2 (by simpa [portableRoundState, Pointer.withOffset, out2] using hs3)
    have state4 : s4 = {s with mem := CompressionExit.outputMem out (fun j => #v[portableRoundState q52 q53 q54 q55 j]) 4 s.mem} :=
      portableStateStep out (portableRoundState q52 q53 q54 q55) s 3 s3 s4 state3 (by simpa [portableRoundState, Pointer.withOffset, out3] using hs4)
    have state5 : s5 = {s with mem := CompressionExit.outputMem out (fun j => #v[portableRoundState q52 q53 q54 q55 j]) 5 s.mem} :=
      portableStateStep out (portableRoundState q52 q53 q54 q55) s 4 s4 s5 state4 (by simpa [portableRoundState, Pointer.withOffset, out4] using hs5)
    have state6 : s6 = {s with mem := CompressionExit.outputMem out (fun j => #v[portableRoundState q52 q53 q54 q55 j]) 6 s.mem} :=
      portableStateStep out (portableRoundState q52 q53 q54 q55) s 5 s5 s6 state5 (by simpa [portableRoundState, Pointer.withOffset, out5] using hs6)
    have state7 : s7 = {s with mem := CompressionExit.outputMem out (fun j => #v[portableRoundState q52 q53 q54 q55 j]) 7 s.mem} :=
      portableStateStep out (portableRoundState q52 q53 q54 q55) s 6 s6 s7 state6 (by simpa [portableRoundState, Pointer.withOffset, out6] using hs7)
    have state8 : s8 = {s with mem := CompressionExit.outputMem out (fun j => #v[portableRoundState q52 q53 q54 q55 j]) 8 s.mem} :=
      portableStateStep out (portableRoundState q52 q53 q54 q55) s 7 s7 s8 state7 (by simpa [portableRoundState, Pointer.withOffset, out7] using hs8)
    have state9 : s9 = {s with mem := CompressionExit.outputMem out (fun j => #v[portableRoundState q52 q53 q54 q55 j]) 9 s.mem} :=
      portableStateStep out (portableRoundState q52 q53 q54 q55) s 8 s8 s9 state8 (by simpa [portableRoundState, Pointer.withOffset, out8] using hs9)
    have state10 : s10 = {s with mem := CompressionExit.outputMem out (fun j => #v[portableRoundState q52 q53 q54 q55 j]) 10 s.mem} :=
      portableStateStep out (portableRoundState q52 q53 q54 q55) s 9 s9 s10 state9 (by simpa [portableRoundState, Pointer.withOffset, out9] using hs10)
    have state11 : s11 = {s with mem := CompressionExit.outputMem out (fun j => #v[portableRoundState q52 q53 q54 q55 j]) 11 s.mem} :=
      portableStateStep out (portableRoundState q52 q53 q54 q55) s 10 s10 s11 state10 (by simpa [portableRoundState, Pointer.withOffset, out10] using hs11)
    have state12 : s12 = {s with mem := CompressionExit.outputMem out (fun j => #v[portableRoundState q52 q53 q54 q55 j]) 12 s.mem} :=
      portableStateStep out (portableRoundState q52 q53 q54 q55) s 11 s11 s12 state11 (by simpa [portableRoundState, Pointer.withOffset, out11] using hs12)
    have state13 : s13 = {s with mem := CompressionExit.outputMem out (fun j => #v[portableRoundState q52 q53 q54 q55 j]) 13 s.mem} :=
      portableStateStep out (portableRoundState q52 q53 q54 q55) s 12 s12 s13 state12 (by simpa [portableRoundState, Pointer.withOffset, out12] using hs13)
    have state14 : s14 = {s with mem := CompressionExit.outputMem out (fun j => #v[portableRoundState q52 q53 q54 q55 j]) 14 s.mem} :=
      portableStateStep out (portableRoundState q52 q53 q54 q55) s 13 s13 s14 state13 (by simpa [portableRoundState, Pointer.withOffset, out13] using hs14)
    have state15 : s15 = {s with mem := CompressionExit.outputMem out (fun j => #v[portableRoundState q52 q53 q54 q55 j]) 15 s.mem} :=
      portableStateStep out (portableRoundState q52 q53 q54 q55) s 14 s14 s15 state14 (by simpa [portableRoundState, Pointer.withOffset, out14] using hs15)
    have state16 : s16 = {s with mem := CompressionExit.outputMem out (fun j => #v[portableRoundState q52 q53 q54 q55 j]) 16 s.mem} :=
      portableStateStep out (portableRoundState q52 q53 q54 q55) s 15 s15 s16 state15 (by simpa [portableRoundState, Pointer.withOffset, out15] using hs16)
    rw [state16, ← portableCompressionMemory_eq_outputMem]

end AgaveLatticeHash.MLIR
