import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Frame

/-! The actual digest-buffer volatile stores and all 65 single-thread fences,
split into eight word-sized proof cutpoints. -/
namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Challenge

def clearBytes (m : MemoryState) (dst : Pointer) (start : Nat) : Nat → MemoryState
  | 0 => m
  | n + 1 => (clearBytes m dst start n).storeAt
      (dst.add (BitVec.ofNat 64 (start + n))) 0#8

theorem clearBytes_live (m : MemoryState) (dst p : Pointer) (start n count : Nat)
    (h : SmallRange m p count) : SmallRange (clearBytes m dst start n) p count := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.storeAt _ _

theorem clearBytes_add (m : MemoryState) (dst : Pointer) (start n k : Nat) :
    clearBytes m dst start (n + k) =
      clearBytes (clearBytes m dst start n) dst (start + n) k := by
  induction k with
  | zero => simp [clearBytes]
  | succ k ih => simp [clearBytes, ih, Nat.add_assoc]

theorem clearBytes_frame (m : MemoryState) (dst : Pointer) (start n mark : Nat)
    (hinternal : mark ≤ dst.id.id) :
    (clearBytes m dst start n).eraseFrom mark = m.eraseFrom mark := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact erase_internal_store _ _ _ _ _ ih hinternal

def clearChunkState (s : GlobalState) (dst : Pointer) (start : Nat) : GlobalState :=
  {s with mem := clearBytes s.mem dst start 8}

set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

def clearChunkEnv0 (E : Env program.Γ) (dst : Pointer) : Env program.Γ :=
  E[%198 := .value (dst.add 1#64),
    %199 := .value (dst.add 2#64),
    %200 := .value (dst.add 3#64),
    %201 := .value (dst.add 4#64),
    %202 := .value (dst.add 5#64),
    %203 := .value (dst.add 6#64),
    %204 := .value (dst.add 7#64)]

/-- Imported bb3 instructions 107 through 130. -/
theorem digest_zero_chunk0 (p : Primitives) (E : Env program.Γ) (s : GlobalState)
    (dst : Pointer) (hd : SmallRange s.mem dst 64)
    (hptr : E.read (%85) = .value dst)
    (hbase : E.read (%85) = .value (dst.add 0#64))
    (hz : E.read (%8) = .value 0#8) :
    (List.foldlM Instr.run E (((program.bb3 p).body.drop 107).take 24) :
      EffectM (Env program.Γ)) s =
      .value (clearChunkEnv0 E dst, clearChunkState s dst 0) := by
  have hl0 := clearBytes_live s.mem dst dst 0 0 64 hd
  have hf0 : Fits (clearBytes s.mem dst 0 0) (dst.add 0#64) 8 :=
    hl0.fits_add (k := 0) (count := 1) (by decide)
  have hl1 := clearBytes_live s.mem dst dst 0 1 64 hd
  have hf1 : Fits (clearBytes s.mem dst 0 1) (dst.add 1#64) 8 :=
    hl1.fits_add (k := 1) (count := 1) (by decide)
  have hg1 : Operation.gepInboundsLive (clearBytes s.mem dst 0 1)
      (.value dst) [.value (1 : Int)] = .value (dst.add 1#64) :=
    hl1.gep (k := 1) (by decide)
  have hl2 := clearBytes_live s.mem dst dst 0 2 64 hd
  have hf2 : Fits (clearBytes s.mem dst 0 2) (dst.add 2#64) 8 :=
    hl2.fits_add (k := 2) (count := 1) (by decide)
  have hg2 : Operation.gepInboundsLive (clearBytes s.mem dst 0 2)
      (.value dst) [.value (2 : Int)] = .value (dst.add 2#64) :=
    hl2.gep (k := 2) (by decide)
  have hl3 := clearBytes_live s.mem dst dst 0 3 64 hd
  have hf3 : Fits (clearBytes s.mem dst 0 3) (dst.add 3#64) 8 :=
    hl3.fits_add (k := 3) (count := 1) (by decide)
  have hg3 : Operation.gepInboundsLive (clearBytes s.mem dst 0 3)
      (.value dst) [.value (3 : Int)] = .value (dst.add 3#64) :=
    hl3.gep (k := 3) (by decide)
  have hl4 := clearBytes_live s.mem dst dst 0 4 64 hd
  have hf4 : Fits (clearBytes s.mem dst 0 4) (dst.add 4#64) 8 :=
    hl4.fits_add (k := 4) (count := 1) (by decide)
  have hg4 : Operation.gepInboundsLive (clearBytes s.mem dst 0 4)
      (.value dst) [.value (4 : Int)] = .value (dst.add 4#64) :=
    hl4.gep (k := 4) (by decide)
  have hl5 := clearBytes_live s.mem dst dst 0 5 64 hd
  have hf5 : Fits (clearBytes s.mem dst 0 5) (dst.add 5#64) 8 :=
    hl5.fits_add (k := 5) (count := 1) (by decide)
  have hg5 : Operation.gepInboundsLive (clearBytes s.mem dst 0 5)
      (.value dst) [.value (5 : Int)] = .value (dst.add 5#64) :=
    hl5.gep (k := 5) (by decide)
  have hl6 := clearBytes_live s.mem dst dst 0 6 64 hd
  have hf6 : Fits (clearBytes s.mem dst 0 6) (dst.add 6#64) 8 :=
    hl6.fits_add (k := 6) (count := 1) (by decide)
  have hg6 : Operation.gepInboundsLive (clearBytes s.mem dst 0 6)
      (.value dst) [.value (6 : Int)] = .value (dst.add 6#64) :=
    hl6.gep (k := 6) (by decide)
  have hl7 := clearBytes_live s.mem dst dst 0 7 64 hd
  have hf7 : Fits (clearBytes s.mem dst 0 7) (dst.add 7#64) 8 :=
    hl7.fits_add (k := 7) (count := 1) (by decide)
  have hg7 : Operation.gepInboundsLive (clearBytes s.mem dst 0 7)
      (.value dst) [.value (7 : Int)] = .value (dst.add 7#64) :=
    hl7.gep (k := 7) (by decide)
  simp [clearBytes] at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hg1 hg2 hg3 hg4 hg5 hg6 hg7
  simp [program.bb3, clearChunkEnv0, clearChunkState, clearBytes,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    hptr, hbase, hz, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hg1, hg2, hg3, hg4, hg5, hg6, hg7, throwUBIf]

def clearChunkEnv1 (E : Env program.Γ) (dst : Pointer) : Env program.Γ :=
  E[%205 := .value (dst.add 9#64),
    %206 := .value (dst.add 10#64),
    %207 := .value (dst.add 11#64),
    %208 := .value (dst.add 12#64),
    %209 := .value (dst.add 13#64),
    %210 := .value (dst.add 14#64),
    %211 := .value (dst.add 15#64)]

/-- Imported bb3 instructions 131 through 153. -/
theorem digest_zero_chunk1 (p : Primitives) (E : Env program.Γ) (s : GlobalState)
    (dst : Pointer) (hd : SmallRange s.mem dst 64)
    (hptr : E.read (%85) = .value dst)
    (hbase : E.read (%191) = .value (dst.add 8#64))
    (hz : E.read (%8) = .value 0#8) :
    (List.foldlM Instr.run E (((program.bb3 p).body.drop 131).take 23) :
      EffectM (Env program.Γ)) s =
      .value (clearChunkEnv1 E dst, clearChunkState s dst 8) := by
  have hl0 := clearBytes_live s.mem dst dst 8 0 64 hd
  have hf0 : Fits (clearBytes s.mem dst 8 0) (dst.add 8#64) 8 :=
    hl0.fits_add (k := 8) (count := 1) (by decide)
  have hl1 := clearBytes_live s.mem dst dst 8 1 64 hd
  have hf1 : Fits (clearBytes s.mem dst 8 1) (dst.add 9#64) 8 :=
    hl1.fits_add (k := 9) (count := 1) (by decide)
  have hg1 : Operation.gepInboundsLive (clearBytes s.mem dst 8 1)
      (.value dst) [.value (9 : Int)] = .value (dst.add 9#64) :=
    hl1.gep (k := 9) (by decide)
  have hl2 := clearBytes_live s.mem dst dst 8 2 64 hd
  have hf2 : Fits (clearBytes s.mem dst 8 2) (dst.add 10#64) 8 :=
    hl2.fits_add (k := 10) (count := 1) (by decide)
  have hg2 : Operation.gepInboundsLive (clearBytes s.mem dst 8 2)
      (.value dst) [.value (10 : Int)] = .value (dst.add 10#64) :=
    hl2.gep (k := 10) (by decide)
  have hl3 := clearBytes_live s.mem dst dst 8 3 64 hd
  have hf3 : Fits (clearBytes s.mem dst 8 3) (dst.add 11#64) 8 :=
    hl3.fits_add (k := 11) (count := 1) (by decide)
  have hg3 : Operation.gepInboundsLive (clearBytes s.mem dst 8 3)
      (.value dst) [.value (11 : Int)] = .value (dst.add 11#64) :=
    hl3.gep (k := 11) (by decide)
  have hl4 := clearBytes_live s.mem dst dst 8 4 64 hd
  have hf4 : Fits (clearBytes s.mem dst 8 4) (dst.add 12#64) 8 :=
    hl4.fits_add (k := 12) (count := 1) (by decide)
  have hg4 : Operation.gepInboundsLive (clearBytes s.mem dst 8 4)
      (.value dst) [.value (12 : Int)] = .value (dst.add 12#64) :=
    hl4.gep (k := 12) (by decide)
  have hl5 := clearBytes_live s.mem dst dst 8 5 64 hd
  have hf5 : Fits (clearBytes s.mem dst 8 5) (dst.add 13#64) 8 :=
    hl5.fits_add (k := 13) (count := 1) (by decide)
  have hg5 : Operation.gepInboundsLive (clearBytes s.mem dst 8 5)
      (.value dst) [.value (13 : Int)] = .value (dst.add 13#64) :=
    hl5.gep (k := 13) (by decide)
  have hl6 := clearBytes_live s.mem dst dst 8 6 64 hd
  have hf6 : Fits (clearBytes s.mem dst 8 6) (dst.add 14#64) 8 :=
    hl6.fits_add (k := 14) (count := 1) (by decide)
  have hg6 : Operation.gepInboundsLive (clearBytes s.mem dst 8 6)
      (.value dst) [.value (14 : Int)] = .value (dst.add 14#64) :=
    hl6.gep (k := 14) (by decide)
  have hl7 := clearBytes_live s.mem dst dst 8 7 64 hd
  have hf7 : Fits (clearBytes s.mem dst 8 7) (dst.add 15#64) 8 :=
    hl7.fits_add (k := 15) (count := 1) (by decide)
  have hg7 : Operation.gepInboundsLive (clearBytes s.mem dst 8 7)
      (.value dst) [.value (15 : Int)] = .value (dst.add 15#64) :=
    hl7.gep (k := 15) (by decide)
  simp [clearBytes] at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hg1 hg2 hg3 hg4 hg5 hg6 hg7
  simp [program.bb3, clearChunkEnv1, clearChunkState, clearBytes,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    hptr, hbase, hz, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hg1, hg2, hg3, hg4, hg5, hg6, hg7, throwUBIf]

def clearChunkEnv2 (E : Env program.Γ) (dst : Pointer) : Env program.Γ :=
  E[%212 := .value (dst.add 17#64),
    %213 := .value (dst.add 18#64),
    %214 := .value (dst.add 19#64),
    %215 := .value (dst.add 20#64),
    %216 := .value (dst.add 21#64),
    %217 := .value (dst.add 22#64),
    %218 := .value (dst.add 23#64)]

/-- Imported bb3 instructions 154 through 176. -/
theorem digest_zero_chunk2 (p : Primitives) (E : Env program.Γ) (s : GlobalState)
    (dst : Pointer) (hd : SmallRange s.mem dst 64)
    (hptr : E.read (%85) = .value dst)
    (hbase : E.read (%192) = .value (dst.add 16#64))
    (hz : E.read (%8) = .value 0#8) :
    (List.foldlM Instr.run E (((program.bb3 p).body.drop 154).take 23) :
      EffectM (Env program.Γ)) s =
      .value (clearChunkEnv2 E dst, clearChunkState s dst 16) := by
  have hl0 := clearBytes_live s.mem dst dst 16 0 64 hd
  have hf0 : Fits (clearBytes s.mem dst 16 0) (dst.add 16#64) 8 :=
    hl0.fits_add (k := 16) (count := 1) (by decide)
  have hl1 := clearBytes_live s.mem dst dst 16 1 64 hd
  have hf1 : Fits (clearBytes s.mem dst 16 1) (dst.add 17#64) 8 :=
    hl1.fits_add (k := 17) (count := 1) (by decide)
  have hg1 : Operation.gepInboundsLive (clearBytes s.mem dst 16 1)
      (.value dst) [.value (17 : Int)] = .value (dst.add 17#64) :=
    hl1.gep (k := 17) (by decide)
  have hl2 := clearBytes_live s.mem dst dst 16 2 64 hd
  have hf2 : Fits (clearBytes s.mem dst 16 2) (dst.add 18#64) 8 :=
    hl2.fits_add (k := 18) (count := 1) (by decide)
  have hg2 : Operation.gepInboundsLive (clearBytes s.mem dst 16 2)
      (.value dst) [.value (18 : Int)] = .value (dst.add 18#64) :=
    hl2.gep (k := 18) (by decide)
  have hl3 := clearBytes_live s.mem dst dst 16 3 64 hd
  have hf3 : Fits (clearBytes s.mem dst 16 3) (dst.add 19#64) 8 :=
    hl3.fits_add (k := 19) (count := 1) (by decide)
  have hg3 : Operation.gepInboundsLive (clearBytes s.mem dst 16 3)
      (.value dst) [.value (19 : Int)] = .value (dst.add 19#64) :=
    hl3.gep (k := 19) (by decide)
  have hl4 := clearBytes_live s.mem dst dst 16 4 64 hd
  have hf4 : Fits (clearBytes s.mem dst 16 4) (dst.add 20#64) 8 :=
    hl4.fits_add (k := 20) (count := 1) (by decide)
  have hg4 : Operation.gepInboundsLive (clearBytes s.mem dst 16 4)
      (.value dst) [.value (20 : Int)] = .value (dst.add 20#64) :=
    hl4.gep (k := 20) (by decide)
  have hl5 := clearBytes_live s.mem dst dst 16 5 64 hd
  have hf5 : Fits (clearBytes s.mem dst 16 5) (dst.add 21#64) 8 :=
    hl5.fits_add (k := 21) (count := 1) (by decide)
  have hg5 : Operation.gepInboundsLive (clearBytes s.mem dst 16 5)
      (.value dst) [.value (21 : Int)] = .value (dst.add 21#64) :=
    hl5.gep (k := 21) (by decide)
  have hl6 := clearBytes_live s.mem dst dst 16 6 64 hd
  have hf6 : Fits (clearBytes s.mem dst 16 6) (dst.add 22#64) 8 :=
    hl6.fits_add (k := 22) (count := 1) (by decide)
  have hg6 : Operation.gepInboundsLive (clearBytes s.mem dst 16 6)
      (.value dst) [.value (22 : Int)] = .value (dst.add 22#64) :=
    hl6.gep (k := 22) (by decide)
  have hl7 := clearBytes_live s.mem dst dst 16 7 64 hd
  have hf7 : Fits (clearBytes s.mem dst 16 7) (dst.add 23#64) 8 :=
    hl7.fits_add (k := 23) (count := 1) (by decide)
  have hg7 : Operation.gepInboundsLive (clearBytes s.mem dst 16 7)
      (.value dst) [.value (23 : Int)] = .value (dst.add 23#64) :=
    hl7.gep (k := 23) (by decide)
  simp [clearBytes] at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hg1 hg2 hg3 hg4 hg5 hg6 hg7
  simp [program.bb3, clearChunkEnv2, clearChunkState, clearBytes,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    hptr, hbase, hz, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hg1, hg2, hg3, hg4, hg5, hg6, hg7, throwUBIf]

def clearChunkEnv3 (E : Env program.Γ) (dst : Pointer) : Env program.Γ :=
  E[%219 := .value (dst.add 25#64),
    %220 := .value (dst.add 26#64),
    %221 := .value (dst.add 27#64),
    %222 := .value (dst.add 28#64),
    %223 := .value (dst.add 29#64),
    %224 := .value (dst.add 30#64),
    %225 := .value (dst.add 31#64)]

/-- Imported bb3 instructions 177 through 199. -/
theorem digest_zero_chunk3 (p : Primitives) (E : Env program.Γ) (s : GlobalState)
    (dst : Pointer) (hd : SmallRange s.mem dst 64)
    (hptr : E.read (%85) = .value dst)
    (hbase : E.read (%193) = .value (dst.add 24#64))
    (hz : E.read (%8) = .value 0#8) :
    (List.foldlM Instr.run E (((program.bb3 p).body.drop 177).take 23) :
      EffectM (Env program.Γ)) s =
      .value (clearChunkEnv3 E dst, clearChunkState s dst 24) := by
  have hl0 := clearBytes_live s.mem dst dst 24 0 64 hd
  have hf0 : Fits (clearBytes s.mem dst 24 0) (dst.add 24#64) 8 :=
    hl0.fits_add (k := 24) (count := 1) (by decide)
  have hl1 := clearBytes_live s.mem dst dst 24 1 64 hd
  have hf1 : Fits (clearBytes s.mem dst 24 1) (dst.add 25#64) 8 :=
    hl1.fits_add (k := 25) (count := 1) (by decide)
  have hg1 : Operation.gepInboundsLive (clearBytes s.mem dst 24 1)
      (.value dst) [.value (25 : Int)] = .value (dst.add 25#64) :=
    hl1.gep (k := 25) (by decide)
  have hl2 := clearBytes_live s.mem dst dst 24 2 64 hd
  have hf2 : Fits (clearBytes s.mem dst 24 2) (dst.add 26#64) 8 :=
    hl2.fits_add (k := 26) (count := 1) (by decide)
  have hg2 : Operation.gepInboundsLive (clearBytes s.mem dst 24 2)
      (.value dst) [.value (26 : Int)] = .value (dst.add 26#64) :=
    hl2.gep (k := 26) (by decide)
  have hl3 := clearBytes_live s.mem dst dst 24 3 64 hd
  have hf3 : Fits (clearBytes s.mem dst 24 3) (dst.add 27#64) 8 :=
    hl3.fits_add (k := 27) (count := 1) (by decide)
  have hg3 : Operation.gepInboundsLive (clearBytes s.mem dst 24 3)
      (.value dst) [.value (27 : Int)] = .value (dst.add 27#64) :=
    hl3.gep (k := 27) (by decide)
  have hl4 := clearBytes_live s.mem dst dst 24 4 64 hd
  have hf4 : Fits (clearBytes s.mem dst 24 4) (dst.add 28#64) 8 :=
    hl4.fits_add (k := 28) (count := 1) (by decide)
  have hg4 : Operation.gepInboundsLive (clearBytes s.mem dst 24 4)
      (.value dst) [.value (28 : Int)] = .value (dst.add 28#64) :=
    hl4.gep (k := 28) (by decide)
  have hl5 := clearBytes_live s.mem dst dst 24 5 64 hd
  have hf5 : Fits (clearBytes s.mem dst 24 5) (dst.add 29#64) 8 :=
    hl5.fits_add (k := 29) (count := 1) (by decide)
  have hg5 : Operation.gepInboundsLive (clearBytes s.mem dst 24 5)
      (.value dst) [.value (29 : Int)] = .value (dst.add 29#64) :=
    hl5.gep (k := 29) (by decide)
  have hl6 := clearBytes_live s.mem dst dst 24 6 64 hd
  have hf6 : Fits (clearBytes s.mem dst 24 6) (dst.add 30#64) 8 :=
    hl6.fits_add (k := 30) (count := 1) (by decide)
  have hg6 : Operation.gepInboundsLive (clearBytes s.mem dst 24 6)
      (.value dst) [.value (30 : Int)] = .value (dst.add 30#64) :=
    hl6.gep (k := 30) (by decide)
  have hl7 := clearBytes_live s.mem dst dst 24 7 64 hd
  have hf7 : Fits (clearBytes s.mem dst 24 7) (dst.add 31#64) 8 :=
    hl7.fits_add (k := 31) (count := 1) (by decide)
  have hg7 : Operation.gepInboundsLive (clearBytes s.mem dst 24 7)
      (.value dst) [.value (31 : Int)] = .value (dst.add 31#64) :=
    hl7.gep (k := 31) (by decide)
  simp [clearBytes] at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hg1 hg2 hg3 hg4 hg5 hg6 hg7
  simp [program.bb3, clearChunkEnv3, clearChunkState, clearBytes,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    hptr, hbase, hz, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hg1, hg2, hg3, hg4, hg5, hg6, hg7, throwUBIf]

def clearChunkEnv4 (E : Env program.Γ) (dst : Pointer) : Env program.Γ :=
  E[%226 := .value (dst.add 33#64),
    %227 := .value (dst.add 34#64),
    %228 := .value (dst.add 35#64),
    %229 := .value (dst.add 36#64),
    %230 := .value (dst.add 37#64),
    %231 := .value (dst.add 38#64),
    %232 := .value (dst.add 39#64)]

/-- Imported bb3 instructions 200 through 222. -/
theorem digest_zero_chunk4 (p : Primitives) (E : Env program.Γ) (s : GlobalState)
    (dst : Pointer) (hd : SmallRange s.mem dst 64)
    (hptr : E.read (%85) = .value dst)
    (hbase : E.read (%194) = .value (dst.add 32#64))
    (hz : E.read (%8) = .value 0#8) :
    (List.foldlM Instr.run E (((program.bb3 p).body.drop 200).take 23) :
      EffectM (Env program.Γ)) s =
      .value (clearChunkEnv4 E dst, clearChunkState s dst 32) := by
  have hl0 := clearBytes_live s.mem dst dst 32 0 64 hd
  have hf0 : Fits (clearBytes s.mem dst 32 0) (dst.add 32#64) 8 :=
    hl0.fits_add (k := 32) (count := 1) (by decide)
  have hl1 := clearBytes_live s.mem dst dst 32 1 64 hd
  have hf1 : Fits (clearBytes s.mem dst 32 1) (dst.add 33#64) 8 :=
    hl1.fits_add (k := 33) (count := 1) (by decide)
  have hg1 : Operation.gepInboundsLive (clearBytes s.mem dst 32 1)
      (.value dst) [.value (33 : Int)] = .value (dst.add 33#64) :=
    hl1.gep (k := 33) (by decide)
  have hl2 := clearBytes_live s.mem dst dst 32 2 64 hd
  have hf2 : Fits (clearBytes s.mem dst 32 2) (dst.add 34#64) 8 :=
    hl2.fits_add (k := 34) (count := 1) (by decide)
  have hg2 : Operation.gepInboundsLive (clearBytes s.mem dst 32 2)
      (.value dst) [.value (34 : Int)] = .value (dst.add 34#64) :=
    hl2.gep (k := 34) (by decide)
  have hl3 := clearBytes_live s.mem dst dst 32 3 64 hd
  have hf3 : Fits (clearBytes s.mem dst 32 3) (dst.add 35#64) 8 :=
    hl3.fits_add (k := 35) (count := 1) (by decide)
  have hg3 : Operation.gepInboundsLive (clearBytes s.mem dst 32 3)
      (.value dst) [.value (35 : Int)] = .value (dst.add 35#64) :=
    hl3.gep (k := 35) (by decide)
  have hl4 := clearBytes_live s.mem dst dst 32 4 64 hd
  have hf4 : Fits (clearBytes s.mem dst 32 4) (dst.add 36#64) 8 :=
    hl4.fits_add (k := 36) (count := 1) (by decide)
  have hg4 : Operation.gepInboundsLive (clearBytes s.mem dst 32 4)
      (.value dst) [.value (36 : Int)] = .value (dst.add 36#64) :=
    hl4.gep (k := 36) (by decide)
  have hl5 := clearBytes_live s.mem dst dst 32 5 64 hd
  have hf5 : Fits (clearBytes s.mem dst 32 5) (dst.add 37#64) 8 :=
    hl5.fits_add (k := 37) (count := 1) (by decide)
  have hg5 : Operation.gepInboundsLive (clearBytes s.mem dst 32 5)
      (.value dst) [.value (37 : Int)] = .value (dst.add 37#64) :=
    hl5.gep (k := 37) (by decide)
  have hl6 := clearBytes_live s.mem dst dst 32 6 64 hd
  have hf6 : Fits (clearBytes s.mem dst 32 6) (dst.add 38#64) 8 :=
    hl6.fits_add (k := 38) (count := 1) (by decide)
  have hg6 : Operation.gepInboundsLive (clearBytes s.mem dst 32 6)
      (.value dst) [.value (38 : Int)] = .value (dst.add 38#64) :=
    hl6.gep (k := 38) (by decide)
  have hl7 := clearBytes_live s.mem dst dst 32 7 64 hd
  have hf7 : Fits (clearBytes s.mem dst 32 7) (dst.add 39#64) 8 :=
    hl7.fits_add (k := 39) (count := 1) (by decide)
  have hg7 : Operation.gepInboundsLive (clearBytes s.mem dst 32 7)
      (.value dst) [.value (39 : Int)] = .value (dst.add 39#64) :=
    hl7.gep (k := 39) (by decide)
  simp [clearBytes] at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hg1 hg2 hg3 hg4 hg5 hg6 hg7
  simp [program.bb3, clearChunkEnv4, clearChunkState, clearBytes,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    hptr, hbase, hz, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hg1, hg2, hg3, hg4, hg5, hg6, hg7, throwUBIf]

def clearChunkEnv5 (E : Env program.Γ) (dst : Pointer) : Env program.Γ :=
  E[%233 := .value (dst.add 41#64),
    %234 := .value (dst.add 42#64),
    %235 := .value (dst.add 43#64),
    %236 := .value (dst.add 44#64),
    %237 := .value (dst.add 45#64),
    %238 := .value (dst.add 46#64),
    %239 := .value (dst.add 47#64)]

/-- Imported bb3 instructions 223 through 245. -/
theorem digest_zero_chunk5 (p : Primitives) (E : Env program.Γ) (s : GlobalState)
    (dst : Pointer) (hd : SmallRange s.mem dst 64)
    (hptr : E.read (%85) = .value dst)
    (hbase : E.read (%195) = .value (dst.add 40#64))
    (hz : E.read (%8) = .value 0#8) :
    (List.foldlM Instr.run E (((program.bb3 p).body.drop 223).take 23) :
      EffectM (Env program.Γ)) s =
      .value (clearChunkEnv5 E dst, clearChunkState s dst 40) := by
  have hl0 := clearBytes_live s.mem dst dst 40 0 64 hd
  have hf0 : Fits (clearBytes s.mem dst 40 0) (dst.add 40#64) 8 :=
    hl0.fits_add (k := 40) (count := 1) (by decide)
  have hl1 := clearBytes_live s.mem dst dst 40 1 64 hd
  have hf1 : Fits (clearBytes s.mem dst 40 1) (dst.add 41#64) 8 :=
    hl1.fits_add (k := 41) (count := 1) (by decide)
  have hg1 : Operation.gepInboundsLive (clearBytes s.mem dst 40 1)
      (.value dst) [.value (41 : Int)] = .value (dst.add 41#64) :=
    hl1.gep (k := 41) (by decide)
  have hl2 := clearBytes_live s.mem dst dst 40 2 64 hd
  have hf2 : Fits (clearBytes s.mem dst 40 2) (dst.add 42#64) 8 :=
    hl2.fits_add (k := 42) (count := 1) (by decide)
  have hg2 : Operation.gepInboundsLive (clearBytes s.mem dst 40 2)
      (.value dst) [.value (42 : Int)] = .value (dst.add 42#64) :=
    hl2.gep (k := 42) (by decide)
  have hl3 := clearBytes_live s.mem dst dst 40 3 64 hd
  have hf3 : Fits (clearBytes s.mem dst 40 3) (dst.add 43#64) 8 :=
    hl3.fits_add (k := 43) (count := 1) (by decide)
  have hg3 : Operation.gepInboundsLive (clearBytes s.mem dst 40 3)
      (.value dst) [.value (43 : Int)] = .value (dst.add 43#64) :=
    hl3.gep (k := 43) (by decide)
  have hl4 := clearBytes_live s.mem dst dst 40 4 64 hd
  have hf4 : Fits (clearBytes s.mem dst 40 4) (dst.add 44#64) 8 :=
    hl4.fits_add (k := 44) (count := 1) (by decide)
  have hg4 : Operation.gepInboundsLive (clearBytes s.mem dst 40 4)
      (.value dst) [.value (44 : Int)] = .value (dst.add 44#64) :=
    hl4.gep (k := 44) (by decide)
  have hl5 := clearBytes_live s.mem dst dst 40 5 64 hd
  have hf5 : Fits (clearBytes s.mem dst 40 5) (dst.add 45#64) 8 :=
    hl5.fits_add (k := 45) (count := 1) (by decide)
  have hg5 : Operation.gepInboundsLive (clearBytes s.mem dst 40 5)
      (.value dst) [.value (45 : Int)] = .value (dst.add 45#64) :=
    hl5.gep (k := 45) (by decide)
  have hl6 := clearBytes_live s.mem dst dst 40 6 64 hd
  have hf6 : Fits (clearBytes s.mem dst 40 6) (dst.add 46#64) 8 :=
    hl6.fits_add (k := 46) (count := 1) (by decide)
  have hg6 : Operation.gepInboundsLive (clearBytes s.mem dst 40 6)
      (.value dst) [.value (46 : Int)] = .value (dst.add 46#64) :=
    hl6.gep (k := 46) (by decide)
  have hl7 := clearBytes_live s.mem dst dst 40 7 64 hd
  have hf7 : Fits (clearBytes s.mem dst 40 7) (dst.add 47#64) 8 :=
    hl7.fits_add (k := 47) (count := 1) (by decide)
  have hg7 : Operation.gepInboundsLive (clearBytes s.mem dst 40 7)
      (.value dst) [.value (47 : Int)] = .value (dst.add 47#64) :=
    hl7.gep (k := 47) (by decide)
  simp [clearBytes] at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hg1 hg2 hg3 hg4 hg5 hg6 hg7
  simp [program.bb3, clearChunkEnv5, clearChunkState, clearBytes,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    hptr, hbase, hz, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hg1, hg2, hg3, hg4, hg5, hg6, hg7, throwUBIf]

def clearChunkEnv6 (E : Env program.Γ) (dst : Pointer) : Env program.Γ :=
  E[%240 := .value (dst.add 49#64),
    %241 := .value (dst.add 50#64),
    %242 := .value (dst.add 51#64),
    %243 := .value (dst.add 52#64),
    %244 := .value (dst.add 53#64),
    %245 := .value (dst.add 54#64),
    %246 := .value (dst.add 55#64)]

/-- Imported bb3 instructions 246 through 268. -/
theorem digest_zero_chunk6 (p : Primitives) (E : Env program.Γ) (s : GlobalState)
    (dst : Pointer) (hd : SmallRange s.mem dst 64)
    (hptr : E.read (%85) = .value dst)
    (hbase : E.read (%196) = .value (dst.add 48#64))
    (hz : E.read (%8) = .value 0#8) :
    (List.foldlM Instr.run E (((program.bb3 p).body.drop 246).take 23) :
      EffectM (Env program.Γ)) s =
      .value (clearChunkEnv6 E dst, clearChunkState s dst 48) := by
  have hl0 := clearBytes_live s.mem dst dst 48 0 64 hd
  have hf0 : Fits (clearBytes s.mem dst 48 0) (dst.add 48#64) 8 :=
    hl0.fits_add (k := 48) (count := 1) (by decide)
  have hl1 := clearBytes_live s.mem dst dst 48 1 64 hd
  have hf1 : Fits (clearBytes s.mem dst 48 1) (dst.add 49#64) 8 :=
    hl1.fits_add (k := 49) (count := 1) (by decide)
  have hg1 : Operation.gepInboundsLive (clearBytes s.mem dst 48 1)
      (.value dst) [.value (49 : Int)] = .value (dst.add 49#64) :=
    hl1.gep (k := 49) (by decide)
  have hl2 := clearBytes_live s.mem dst dst 48 2 64 hd
  have hf2 : Fits (clearBytes s.mem dst 48 2) (dst.add 50#64) 8 :=
    hl2.fits_add (k := 50) (count := 1) (by decide)
  have hg2 : Operation.gepInboundsLive (clearBytes s.mem dst 48 2)
      (.value dst) [.value (50 : Int)] = .value (dst.add 50#64) :=
    hl2.gep (k := 50) (by decide)
  have hl3 := clearBytes_live s.mem dst dst 48 3 64 hd
  have hf3 : Fits (clearBytes s.mem dst 48 3) (dst.add 51#64) 8 :=
    hl3.fits_add (k := 51) (count := 1) (by decide)
  have hg3 : Operation.gepInboundsLive (clearBytes s.mem dst 48 3)
      (.value dst) [.value (51 : Int)] = .value (dst.add 51#64) :=
    hl3.gep (k := 51) (by decide)
  have hl4 := clearBytes_live s.mem dst dst 48 4 64 hd
  have hf4 : Fits (clearBytes s.mem dst 48 4) (dst.add 52#64) 8 :=
    hl4.fits_add (k := 52) (count := 1) (by decide)
  have hg4 : Operation.gepInboundsLive (clearBytes s.mem dst 48 4)
      (.value dst) [.value (52 : Int)] = .value (dst.add 52#64) :=
    hl4.gep (k := 52) (by decide)
  have hl5 := clearBytes_live s.mem dst dst 48 5 64 hd
  have hf5 : Fits (clearBytes s.mem dst 48 5) (dst.add 53#64) 8 :=
    hl5.fits_add (k := 53) (count := 1) (by decide)
  have hg5 : Operation.gepInboundsLive (clearBytes s.mem dst 48 5)
      (.value dst) [.value (53 : Int)] = .value (dst.add 53#64) :=
    hl5.gep (k := 53) (by decide)
  have hl6 := clearBytes_live s.mem dst dst 48 6 64 hd
  have hf6 : Fits (clearBytes s.mem dst 48 6) (dst.add 54#64) 8 :=
    hl6.fits_add (k := 54) (count := 1) (by decide)
  have hg6 : Operation.gepInboundsLive (clearBytes s.mem dst 48 6)
      (.value dst) [.value (54 : Int)] = .value (dst.add 54#64) :=
    hl6.gep (k := 54) (by decide)
  have hl7 := clearBytes_live s.mem dst dst 48 7 64 hd
  have hf7 : Fits (clearBytes s.mem dst 48 7) (dst.add 55#64) 8 :=
    hl7.fits_add (k := 55) (count := 1) (by decide)
  have hg7 : Operation.gepInboundsLive (clearBytes s.mem dst 48 7)
      (.value dst) [.value (55 : Int)] = .value (dst.add 55#64) :=
    hl7.gep (k := 55) (by decide)
  simp [clearBytes] at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hg1 hg2 hg3 hg4 hg5 hg6 hg7
  simp [program.bb3, clearChunkEnv6, clearChunkState, clearBytes,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    hptr, hbase, hz, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hg1, hg2, hg3, hg4, hg5, hg6, hg7, throwUBIf]

def clearChunkEnv7 (E : Env program.Γ) (dst : Pointer) : Env program.Γ :=
  E[%247 := .value (dst.add 57#64),
    %248 := .value (dst.add 58#64),
    %249 := .value (dst.add 59#64),
    %250 := .value (dst.add 60#64),
    %251 := .value (dst.add 61#64),
    %252 := .value (dst.add 62#64),
    %253 := .value (dst.add 63#64)]

/-- Imported bb3 instructions 269 through 291. -/
theorem digest_zero_chunk7 (p : Primitives) (E : Env program.Γ) (s : GlobalState)
    (dst : Pointer) (hd : SmallRange s.mem dst 64)
    (hptr : E.read (%85) = .value dst)
    (hbase : E.read (%197) = .value (dst.add 56#64))
    (hz : E.read (%8) = .value 0#8) :
    (List.foldlM Instr.run E (((program.bb3 p).body.drop 269).take 23) :
      EffectM (Env program.Γ)) s =
      .value (clearChunkEnv7 E dst, clearChunkState s dst 56) := by
  have hl0 := clearBytes_live s.mem dst dst 56 0 64 hd
  have hf0 : Fits (clearBytes s.mem dst 56 0) (dst.add 56#64) 8 :=
    hl0.fits_add (k := 56) (count := 1) (by decide)
  have hl1 := clearBytes_live s.mem dst dst 56 1 64 hd
  have hf1 : Fits (clearBytes s.mem dst 56 1) (dst.add 57#64) 8 :=
    hl1.fits_add (k := 57) (count := 1) (by decide)
  have hg1 : Operation.gepInboundsLive (clearBytes s.mem dst 56 1)
      (.value dst) [.value (57 : Int)] = .value (dst.add 57#64) :=
    hl1.gep (k := 57) (by decide)
  have hl2 := clearBytes_live s.mem dst dst 56 2 64 hd
  have hf2 : Fits (clearBytes s.mem dst 56 2) (dst.add 58#64) 8 :=
    hl2.fits_add (k := 58) (count := 1) (by decide)
  have hg2 : Operation.gepInboundsLive (clearBytes s.mem dst 56 2)
      (.value dst) [.value (58 : Int)] = .value (dst.add 58#64) :=
    hl2.gep (k := 58) (by decide)
  have hl3 := clearBytes_live s.mem dst dst 56 3 64 hd
  have hf3 : Fits (clearBytes s.mem dst 56 3) (dst.add 59#64) 8 :=
    hl3.fits_add (k := 59) (count := 1) (by decide)
  have hg3 : Operation.gepInboundsLive (clearBytes s.mem dst 56 3)
      (.value dst) [.value (59 : Int)] = .value (dst.add 59#64) :=
    hl3.gep (k := 59) (by decide)
  have hl4 := clearBytes_live s.mem dst dst 56 4 64 hd
  have hf4 : Fits (clearBytes s.mem dst 56 4) (dst.add 60#64) 8 :=
    hl4.fits_add (k := 60) (count := 1) (by decide)
  have hg4 : Operation.gepInboundsLive (clearBytes s.mem dst 56 4)
      (.value dst) [.value (60 : Int)] = .value (dst.add 60#64) :=
    hl4.gep (k := 60) (by decide)
  have hl5 := clearBytes_live s.mem dst dst 56 5 64 hd
  have hf5 : Fits (clearBytes s.mem dst 56 5) (dst.add 61#64) 8 :=
    hl5.fits_add (k := 61) (count := 1) (by decide)
  have hg5 : Operation.gepInboundsLive (clearBytes s.mem dst 56 5)
      (.value dst) [.value (61 : Int)] = .value (dst.add 61#64) :=
    hl5.gep (k := 61) (by decide)
  have hl6 := clearBytes_live s.mem dst dst 56 6 64 hd
  have hf6 : Fits (clearBytes s.mem dst 56 6) (dst.add 62#64) 8 :=
    hl6.fits_add (k := 62) (count := 1) (by decide)
  have hg6 : Operation.gepInboundsLive (clearBytes s.mem dst 56 6)
      (.value dst) [.value (62 : Int)] = .value (dst.add 62#64) :=
    hl6.gep (k := 62) (by decide)
  have hl7 := clearBytes_live s.mem dst dst 56 7 64 hd
  have hf7 : Fits (clearBytes s.mem dst 56 7) (dst.add 63#64) 8 :=
    hl7.fits_add (k := 63) (count := 1) (by decide)
  have hg7 : Operation.gepInboundsLive (clearBytes s.mem dst 56 7)
      (.value dst) [.value (63 : Int)] = .value (dst.add 63#64) :=
    hl7.gep (k := 63) (by decide)
  simp [clearBytes] at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hg1 hg2 hg3 hg4 hg5 hg6 hg7
  simp [program.bb3, clearChunkEnv7, clearChunkState, clearBytes,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    hptr, hbase, hz, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hg1, hg2, hg3, hg4, hg5, hg6, hg7, throwUBIf]

/-- The trailing lifetime markers preserve the complete machine state. -/
theorem final_lifetimes (p : Primitives) (E : Env program.Γ) (s : GlobalState) :
    (program.bb3 p).runBodyFrom E 292 s = .value (E, s) := by
  simp [BasicBlock.runBodyFrom, program.bb3, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
