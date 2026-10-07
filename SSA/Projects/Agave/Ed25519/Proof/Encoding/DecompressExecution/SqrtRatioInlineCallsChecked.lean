import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineCallsBody

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
attribute [local irreducible] callsState callWords machine Pow2k.iterateSquare

theorem checked_arithmetic_calls (s : GlobalState) (u v : Pointer) (hwf : s.WF)
    (hu : SmallRange s.mem u 40) (hv : SmallRange s.mem v 40) :
    ArithmeticCalls s u v (callsState s (callWords (readLimbs s u) (readLimbs s v))
      (callExtra (readLimbs s u) (readLimbs s v))) := by
  let values := callWords (readLimbs s u) (readLimbs s v)
  let extra := callExtra (readLimbs s u) (readLimbs s v)
  change ArithmeticCalls s u v (callsState s values extra)
  have hread (i n : Nat) (hi : i < n) (hn : n ≤ 13) :=
    callsState_words_written s values extra hwf hi hn
  have hread0 (n : Nat) (hi : 0 < n) (hn : n ≤ 13) :
      readLimbs (callsState s values extra n) (slot s 20) = values 0 := hread 0 n hi hn
  have hread1 (n : Nat) (hi : 1 < n) (hn : n ≤ 13) :
      readLimbs (callsState s values extra n) (slot s 21) = values 1 := hread 1 n hi hn
  have hread2 (n : Nat) (hi : 2 < n) (hn : n ≤ 13) :
      readLimbs (callsState s values extra n) (slot s 18) = values 2 := hread 2 n hi hn
  have hread3 (n : Nat) (hi : 3 < n) (hn : n ≤ 13) :
      readLimbs (callsState s values extra n) (slot s 19) = values 3 := hread 3 n hi hn
  have hread4 (n : Nat) (hi : 4 < n) (hn : n ≤ 13) :
      readLimbs (callsState s values extra n) (slot s 16) = values 4 := hread 4 n hi hn
  have hread5 (n : Nat) (hi : 5 < n) (hn : n ≤ 13) :
      readLimbs (callsState s values extra n) (slot s 14) = values 5 := hread 5 n hi hn
  have hread6 (n : Nat) (hi : 6 < n) (hn : n ≤ 13) :
      readLimbs (callsState s values extra n) (slot s 7) = values 6 := hread 6 n hi hn
  have hread7 (n : Nat) (hi : 7 < n) (hn : n ≤ 13) :
      readLimbs (callsState s values extra n) (slot s 8) = values 7 := hread 7 n hi hn
  have hread8 (n : Nat) (hi : 8 < n) (hn : n ≤ 13) :
      readLimbs (callsState s values extra n) (slot s 6) = values 8 := hread 8 n hi hn
  have hread9 (n : Nat) (hi : 9 < n) (hn : n ≤ 13) :
      readLimbs (callsState s values extra n) (slot s 15) = values 9 := hread 9 n hi hn
  have hread10 (n : Nat) (hi : 10 < n) (hn : n ≤ 13) :
      readLimbs (callsState s values extra n) (slot s 17) = values 10 := hread 10 n hi hn
  have hread11 (n : Nat) (hi : 11 < n) (hn : n ≤ 13) :
      readLimbs (callsState s values extra n) (slot s 12) = values 11 := hread 11 n hi hn
  have hread12 (n : Nat) (hi : 12 < n) (hn : n ≤ 13) :
      readLimbs (callsState s values extra n) (slot s 13) = values 12 := hread 12 n hi hn
  have hold (p : Pointer) (hp : SmallRange s.mem p 40) (n : Nat) :=
    callsState_words_old s values extra hwf hp n
  have hlive (i : Nat) (hi : i < 13) :=
    call_destination_live s values extra hwf i 0 hi
  simp only [callsState] at hlive
  have hlu := allocate_live s hwf allocationSizes hu
  have hlv := allocate_live s hwf allocationSizes hv
  have c0 := calls_square s values extra hwf 0 1 (by decide) (by decide)
    (by decide) (by decide) v hlv (by
      rw [hold v hv 0]
      exact callWords0 _ _)
  have c1 := calls_mul s values extra hwf 1 (by decide) (by decide)
    (slot s 20) v (hlive 0 (by decide)) hlv (by
      rw [hread0 1 (by decide) (by decide), hold v hv 1]
      exact callWords1 _ _)
  have c2 := calls_square s values extra hwf 2 1 (by decide) (by decide)
    (by decide) (by decide) (slot s 21) (hlive 1 (by decide)) (by
      rw [hread1 2 (by decide) (by decide)]
      exact callWords2 _ _)
  have c3 := calls_mul s values extra hwf 3 (by decide) (by decide)
    (slot s 18) v (hlive 2 (by decide)) hlv (by
      rw [hread2 3 (by decide) (by decide), hold v hv 3]
      exact callWords3 _ _)
  have c4 := calls_mul s values extra hwf 4 (by decide) (by decide)
    u (slot s 21) hlu (hlive 1 (by decide)) (by
      rw [hold u hu 4, hread1 4 (by decide) (by decide)]
      exact callWords4 _ _)
  have c5 := calls_mul s values extra hwf 5 (by decide) (by decide)
    u (slot s 19) hlu (hlive 3 (by decide)) (by
      rw [hold u hu 5, hread3 5 (by decide) (by decide)]
      exact callWords5 _ _)
  have c6 := calls_pow s values extra hwf (callWords_pow _ _)
  have c7 (E : Env program.Γ) := calls_copy s values extra hwf (callWords7 _ _) E
  have c8 := calls_square s values extra hwf 8 2 (by decide) (by decide)
    (by decide) (by decide) (slot s 8) (hlive 7 (by decide)) (by
      rw [hread7 8 (by decide) (by decide)]
      exact callWords8 _ _)
  have c9 := calls_mul s values extra hwf 9 (by decide) (by decide)
    (slot s 14) (slot s 6) (hlive 5 (by decide)) (hlive 8 (by decide)) (by
      rw [hread5 9 (by decide) (by decide), hread8 9 (by decide) (by decide)]
      exact callWords9 _ _)
  have c10 := calls_mul s values extra hwf 10 (by decide) (by decide)
    (slot s 16) (slot s 15) (hlive 4 (by decide)) (hlive 9 (by decide)) (by
      rw [hread4 10 (by decide) (by decide), hread9 10 (by decide) (by decide)]
      exact callWords10 _ _)
  have c11 := calls_square s values extra hwf 11 1 (by decide) (by decide)
    (by decide) (by decide) (slot s 17) (hlive 10 (by decide)) (by
      rw [hread10 11 (by decide) (by decide)]
      exact callWords11 _ _)
  have c12 := calls_mul s values extra hwf 12 (by decide) (by decide)
    v (slot s 12) hlv (hlive 11 (by decide)) (by
      rw [hold v hv 12, hread11 12 (by decide) (by decide)]
      exact callWords12 _ _)
  exact ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12⟩

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
