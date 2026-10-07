import SSA.Projects.Agave.Ed25519.Proof.NAF.Iteration

/-!
# Total execution of the imported NAF loops

The induction follows the actual compiler backedges. The loop's cursor and
carry are derived from the source transition; all word and byte accesses are
justified by the two outer allocation bounds. A disjoint allocation identifier
keeps the scratch scalar unchanged by every output store.
-/
namespace Agave.Ed25519.NAF.RIR

open LeanMLIR.RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000

private theorem state_eq_of_fields {a b : State}
    (ht : a.tail = b.tail) (hc : a.carry = b.carry) : a = b := by
  cases a
  cases b
  simp_all

private theorem storeLoop_outside (width : Nat) (out : Pointer) (fuel pos : Nat)
    (state : State) (mem : MemoryState) (hpos : ¬pos < 256) :
    Memory.storeLoop width out fuel pos state mem = mem := by
  cases fuel <;> simp [Memory.storeLoop, hpos]

theorem mask5_scalar (scalar : BitVec 256) (pos : Fin 256) :
    (mask5 (WordWindow.rawWindow (WordWindow.scalarBuffer scalar) pos.val 5)).val =
      (scalar.toNat / 2 ^ pos.val) % 32 := by
  exact WordWindow.scalar_window_eq_tail scalar pos.val 5 (Or.inl rfl)

theorem even_step5 (tail : Nat) (carry : Fin 2)
    (heven : (tail % 32 + carry.val) % 2 = 0) :
    step 5 ⟨tail, carry.val⟩ = ⟨0, 1, ⟨tail / 2, carry.val⟩⟩ := by
  have hzero : (carry.val + tail % 2 ^ 5) % 2 = 0 := by
    simpa only [Nat.add_comm, Nat.reducePow] using heven
  simp only [step, hzero, ite_true]

/-- Finite arithmetic only: the odd branch writes a nonzero signed digit,
advances by the source width, and sets exactly the source's next carry. -/
theorem odd_step5_finite : ∀ raw : Fin 32, ∀ carry : Fin 2,
    ¬(sum5 raw carry).val % 2 = 0 →
      (step 5 ⟨raw.val, carry.val⟩).digit ≠ 0 ∧
      byte5 (sum5 raw carry) = BitVec.ofInt 8 (step 5 ⟨raw.val, carry.val⟩).digit ∧
      (step 5 ⟨raw.val, carry.val⟩).advance = 5 ∧
      (nextCarry5 (sum5 raw carry)).val = (step 5 ⟨raw.val, carry.val⟩).next.carry := by
  decide +kernel

theorem odd_step5_scalar (scalar : BitVec 256) (pos : Fin 256) (carry : Fin 2)
    (hodd : ¬(sum5 (mask5 (WordWindow.rawWindow (WordWindow.scalarBuffer scalar) pos.val 5)) carry).val % 2 = 0) :
    let window := sum5 (mask5 (WordWindow.rawWindow (WordWindow.scalarBuffer scalar) pos.val 5)) carry
    let transition := step 5 ⟨scalar.toNat / 2 ^ pos.val, carry.val⟩
    transition.digit ≠ 0 ∧ byte5 window = BitVec.ofInt 8 transition.digit ∧
      transition.advance = 5 ∧ (nextCarry5 window).val = transition.next.carry := by
  have hcert := odd_step5_finite
    (mask5 (WordWindow.rawWindow (WordWindow.scalarBuffer scalar) pos.val 5)) carry hodd
  obtain ⟨hd, ha, hc⟩ := step_mod_window 5 (scalar.toNat / 2 ^ pos.val) carry.val
  rw [mask5_scalar] at hcert
  norm_num only [Nat.reducePow] at hd ha hc
  simpa only [hd, ha, hc] using hcert

/-- Total execution from the original word-load block. The structural budget
cannot run out before the compiler exits because each source transition moves
the cursor by at least one. No successful-execution premise is used. -/
theorem kernel5_loop_run (fuel : Nat) (E : ⟪kernel5.Γ⟫) (scratch out : Pointer)
    (scalar : BitVec 256) (pos : Fin 256) (carry : Fin 2) (s : GlobalState)
    (hbudget : 256 ≤ pos.val + fuel)
    (hscratch : Buffer s.mem scratch 40)
    (hscalar : s.mem.readAt scratch 320 = WordWindow.scalarBuffer scalar)
    (houtbuf : Buffer s.mem out 256) (hout : E.read (%arg0) = .value out)
    (hseparate : out.id ≠ scratch.id) :
    kernel5.runFrom (loopEnv5 E scratch pos carry) 2 s =
      .value (.nil, {s with mem := Memory.storeLoop 5 out fuel pos.val ⟨scalar.toNat / 2 ^ pos.val, carry.val⟩ s.mem}) := by
  induction fuel generalizing E pos carry s with
  | zero => have := pos.isLt; omega
  | succ fuel ih =>
      by_cases heven :
          (sum5 (mask5 (WordWindow.rawWindow (WordWindow.scalarBuffer scalar) pos.val 5)) carry).val % 2 = 0
      · have hsource : ((scalar.toNat / 2 ^ pos.val) % 32 + carry.val) % 2 = 0 := by
          simpa only [sum5, mask5_scalar] using heven
        have hstep := even_step5 (scalar.toNat / 2 ^ pos.val) carry hsource
        have htail : scalar.toNat / 2 ^ pos.val / 2 = scalar.toNat / 2 ^ (pos.val + 1) := by
          rw [Nat.div_div_eq_div_mul, pow_succ]
        rw [kernel5_even_iteration E scratch pos carry (WordWindow.scalarBuffer scalar)
          s hscratch hscalar heven]
        rw [Memory.storeLoop, if_pos pos.isLt, hstep]
        change _ = PoisonOr.value (Vals.nil, {s with mem := Memory.storeLoop 5 out fuel (pos.val + 1) ⟨scalar.toNat / 2 ^ pos.val / 2, carry.val⟩ s.mem})
        rw [htail]
        by_cases hnext : pos.val + 1 < 256
        · rw [dif_pos hnext]
          exact ih (evenNextEnv5 E scratch pos carry (WordWindow.scalarBuffer scalar))
            ⟨pos.val + 1, hnext⟩ carry s (by change 256 ≤ pos.val + 1 + fuel; omega) hscratch hscalar houtbuf
            (by rw [evenNextEnv5_arg]; exact hout)
        · rw [dif_neg hnext, storeLoop_outside 5 out fuel (pos.val + 1) _ _ hnext]
      · obtain ⟨hdigit, hbyte, hadvance, hcarry⟩ := odd_step5_scalar scalar pos carry heven
        let window := sum5 (mask5 (WordWindow.rawWindow (WordWindow.scalarBuffer scalar) pos.val 5)) carry
        let s' := {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte5 window)}
        have hscratch' : Buffer s'.mem scratch 40 := hscratch.storeAt _ _
        have houtbuf' : Buffer s'.mem out 256 := houtbuf.storeAt _ _
        have hscalar' : s'.mem.readAt scratch 320 = WordWindow.scalarBuffer scalar := by
          change (s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte5 window)).readAt scratch 320 = _
          rw [MemoryState.readAt_storeAt_disjoint
            (p := out.add (BitVec.ofNat 64 pos.val)) (q := scratch)
            (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hseparate)) (byte5 window)]
          exact hscalar
        have hstate : (step 5 ⟨scalar.toNat / 2 ^ pos.val, carry.val⟩).next =
            ⟨scalar.toNat / 2 ^ (pos.val + 5), (nextCarry5 window).val⟩ := by
          apply state_eq_of_fields
          · have ht := next_tail_of_original 5 scalar.toNat pos.val carry.val
            simpa only [hadvance] using ht
          · exact hcarry.symm
        rw [kernel5_odd_iteration E scratch out pos carry (WordWindow.scalarBuffer scalar)
          s hscratch hscalar houtbuf hout heven]
        dsimp only
        rw [Memory.storeLoop, if_pos pos.isLt]
        dsimp only
        rw [if_neg hdigit, ← hbyte, hadvance, hstate]
        by_cases hnext : pos.val + 5 < 256
        · rw [dif_pos hnext]
          exact ih (oddNextEnv5 E scratch out pos carry (WordWindow.scalarBuffer scalar))
            ⟨pos.val + 5, hnext⟩ (nextCarry5 window) s' (by change 256 ≤ pos.val + 5 + fuel; omega) hscratch' hscalar' houtbuf'
            (by rw [oddNextEnv5_arg]; exact hout)
        · rw [dif_neg hnext, storeLoop_outside 5 out fuel (pos.val + 5) _ _ hnext]

/-- Every byte after the actual complete loop equals the source digit array;
all skipped positions follow from the initial memset and strict cursor growth. -/
theorem kernel5_loop_sourceDigits (E : ⟪kernel5.Γ⟫) (scratch out : Pointer)
    (scalar : BitVec 256) (s : GlobalState)
    (hscratch : Buffer s.mem scratch 40)
    (hscalar : s.mem.readAt scratch 320 = WordWindow.scalarBuffer scalar)
    (houtbuf : Buffer s.mem out 256) (hout : E.read (%arg0) = .value out)
    (hseparate : out.id ≠ scratch.id) (hzero : s.mem.readAt out 2048 = 0) :
    ∃ result, kernel5.runFrom (loopEnv5 E scratch 0 0) 2 s = .value (.nil, result) ∧
      ∀ i : Fin 256, result.mem.readAt (out.add (BitVec.ofNat 64 i.val)) 8 =
        BitVec.ofInt 8 (sourceDigits 5 scalar.toNat i) := by
  refine ⟨{s with mem := Memory.storeLoop 5 out 256 0 ⟨scalar.toNat, 0⟩ s.mem}, ?_, ?_⟩
  · simpa only [Fin.val_zero, pow_zero, Nat.div_one] using
      kernel5_loop_run 256 E scratch out scalar 0 0 s (by decide)
        hscratch hscalar houtbuf hout hseparate
  · exact Memory.storeLoop_sourceDigits 5 (Or.inl rfl) scalar.toNat out s.mem houtbuf hzero

theorem mask8_scalar (scalar : BitVec 256) (pos : Fin 256) :
    (mask8 (WordWindow.rawWindow (WordWindow.scalarBuffer scalar) pos.val 8)).val =
      (scalar.toNat / 2 ^ pos.val) % 256 := by
  exact WordWindow.scalar_window_eq_tail scalar pos.val 8 (Or.inr rfl)

theorem even_step8 (tail : Nat) (carry : Fin 2)
    (heven : (tail % 256 + carry.val) % 2 = 0) :
    step 8 ⟨tail, carry.val⟩ = ⟨0, 1, ⟨tail / 2, carry.val⟩⟩ := by
  have hzero : (carry.val + tail % 2 ^ 8) % 2 = 0 := by
    simpa only [Nat.add_comm, Nat.reducePow] using heven
  simp only [step, hzero, ite_true]

/-- Finite arithmetic only: the odd branch writes a nonzero signed digit,
advances by the source width, and sets exactly the source's next carry. -/
theorem odd_step8_finite : ∀ raw : Fin 256, ∀ carry : Fin 2,
    ¬(sum8 raw carry).val % 2 = 0 →
      (step 8 ⟨raw.val, carry.val⟩).digit ≠ 0 ∧
      byte8 (sum8 raw carry) = BitVec.ofInt 8 (step 8 ⟨raw.val, carry.val⟩).digit ∧
      (step 8 ⟨raw.val, carry.val⟩).advance = 8 ∧
      (nextCarry8 (sum8 raw carry)).val = (step 8 ⟨raw.val, carry.val⟩).next.carry := by
  decide +kernel

theorem odd_step8_scalar (scalar : BitVec 256) (pos : Fin 256) (carry : Fin 2)
    (hodd : ¬(sum8 (mask8 (WordWindow.rawWindow (WordWindow.scalarBuffer scalar) pos.val 8)) carry).val % 2 = 0) :
    let window := sum8 (mask8 (WordWindow.rawWindow (WordWindow.scalarBuffer scalar) pos.val 8)) carry
    let transition := step 8 ⟨scalar.toNat / 2 ^ pos.val, carry.val⟩
    transition.digit ≠ 0 ∧ byte8 window = BitVec.ofInt 8 transition.digit ∧
      transition.advance = 8 ∧ (nextCarry8 window).val = transition.next.carry := by
  have hcert := odd_step8_finite
    (mask8 (WordWindow.rawWindow (WordWindow.scalarBuffer scalar) pos.val 8)) carry hodd
  obtain ⟨hd, ha, hc⟩ := step_mod_window 8 (scalar.toNat / 2 ^ pos.val) carry.val
  rw [mask8_scalar] at hcert
  norm_num only [Nat.reducePow] at hd ha hc
  simpa only [hd, ha, hc] using hcert

/-- Total execution from the original word-load block. The structural budget
cannot run out before the compiler exits because each source transition moves
the cursor by at least one. No successful-execution premise is used. -/
theorem kernel8_loop_run (fuel : Nat) (E : ⟪kernel8.Γ⟫) (scratch out : Pointer)
    (scalar : BitVec 256) (pos : Fin 256) (carry : Fin 2) (s : GlobalState)
    (hbudget : 256 ≤ pos.val + fuel)
    (hscratch : Buffer s.mem scratch 40)
    (hscalar : s.mem.readAt scratch 320 = WordWindow.scalarBuffer scalar)
    (houtbuf : Buffer s.mem out 256) (hout : E.read (%arg0) = .value out)
    (hseparate : out.id ≠ scratch.id) :
    kernel8.runFrom (loopEnv8 E scratch pos carry) 2 s =
      .value (.nil, {s with mem := Memory.storeLoop 8 out fuel pos.val ⟨scalar.toNat / 2 ^ pos.val, carry.val⟩ s.mem}) := by
  induction fuel generalizing E pos carry s with
  | zero => have := pos.isLt; omega
  | succ fuel ih =>
      by_cases heven :
          (sum8 (mask8 (WordWindow.rawWindow (WordWindow.scalarBuffer scalar) pos.val 8)) carry).val % 2 = 0
      · have hsource : ((scalar.toNat / 2 ^ pos.val) % 256 + carry.val) % 2 = 0 := by
          simpa only [sum8, mask8_scalar] using heven
        have hstep := even_step8 (scalar.toNat / 2 ^ pos.val) carry hsource
        have htail : scalar.toNat / 2 ^ pos.val / 2 = scalar.toNat / 2 ^ (pos.val + 1) := by
          rw [Nat.div_div_eq_div_mul, pow_succ]
        rw [kernel8_even_iteration E scratch pos carry (WordWindow.scalarBuffer scalar)
          s hscratch hscalar heven]
        rw [Memory.storeLoop, if_pos pos.isLt, hstep]
        change _ = PoisonOr.value (Vals.nil, {s with mem := Memory.storeLoop 8 out fuel (pos.val + 1) ⟨scalar.toNat / 2 ^ pos.val / 2, carry.val⟩ s.mem})
        rw [htail]
        by_cases hnext : pos.val + 1 < 256
        · rw [dif_pos hnext]
          exact ih (evenNextEnv8 E scratch pos carry (WordWindow.scalarBuffer scalar))
            ⟨pos.val + 1, hnext⟩ carry s (by change 256 ≤ pos.val + 1 + fuel; omega) hscratch hscalar houtbuf
            (by rw [evenNextEnv8_arg]; exact hout)
        · rw [dif_neg hnext, storeLoop_outside 8 out fuel (pos.val + 1) _ _ hnext]
      · obtain ⟨hdigit, hbyte, hadvance, hcarry⟩ := odd_step8_scalar scalar pos carry heven
        let window := sum8 (mask8 (WordWindow.rawWindow (WordWindow.scalarBuffer scalar) pos.val 8)) carry
        let s' := {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)}
        have hscratch' : Buffer s'.mem scratch 40 := hscratch.storeAt _ _
        have houtbuf' : Buffer s'.mem out 256 := houtbuf.storeAt _ _
        have hscalar' : s'.mem.readAt scratch 320 = WordWindow.scalarBuffer scalar := by
          change (s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)).readAt scratch 320 = _
          rw [MemoryState.readAt_storeAt_disjoint
            (p := out.add (BitVec.ofNat 64 pos.val)) (q := scratch)
            (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hseparate)) (byte8 window)]
          exact hscalar
        have hstate : (step 8 ⟨scalar.toNat / 2 ^ pos.val, carry.val⟩).next =
            ⟨scalar.toNat / 2 ^ (pos.val + 8), (nextCarry8 window).val⟩ := by
          apply state_eq_of_fields
          · have ht := next_tail_of_original 8 scalar.toNat pos.val carry.val
            simpa only [hadvance] using ht
          · exact hcarry.symm
        rw [kernel8_odd_iteration E scratch out pos carry (WordWindow.scalarBuffer scalar)
          s hscratch hscalar houtbuf hout heven]
        dsimp only
        rw [Memory.storeLoop, if_pos pos.isLt]
        dsimp only
        rw [if_neg hdigit, ← hbyte, hadvance, hstate]
        by_cases hnext : pos.val + 8 < 256
        · rw [dif_pos hnext]
          exact ih (oddNextEnv8 E scratch out pos carry (WordWindow.scalarBuffer scalar))
            ⟨pos.val + 8, hnext⟩ (nextCarry8 window) s' (by change 256 ≤ pos.val + 8 + fuel; omega) hscratch' hscalar' houtbuf'
            (by rw [oddNextEnv8_arg]; exact hout)
        · rw [dif_neg hnext, storeLoop_outside 8 out fuel (pos.val + 8) _ _ hnext]

/-- Every byte after the actual complete loop equals the source digit array;
all skipped positions follow from the initial memset and strict cursor growth. -/
theorem kernel8_loop_sourceDigits (E : ⟪kernel8.Γ⟫) (scratch out : Pointer)
    (scalar : BitVec 256) (s : GlobalState)
    (hscratch : Buffer s.mem scratch 40)
    (hscalar : s.mem.readAt scratch 320 = WordWindow.scalarBuffer scalar)
    (houtbuf : Buffer s.mem out 256) (hout : E.read (%arg0) = .value out)
    (hseparate : out.id ≠ scratch.id) (hzero : s.mem.readAt out 2048 = 0) :
    ∃ result, kernel8.runFrom (loopEnv8 E scratch 0 0) 2 s = .value (.nil, result) ∧
      ∀ i : Fin 256, result.mem.readAt (out.add (BitVec.ofNat 64 i.val)) 8 =
        BitVec.ofInt 8 (sourceDigits 8 scalar.toNat i) := by
  refine ⟨{s with mem := Memory.storeLoop 8 out 256 0 ⟨scalar.toNat, 0⟩ s.mem}, ?_, ?_⟩
  · simpa only [Fin.val_zero, pow_zero, Nat.div_one] using
      kernel8_loop_run 256 E scratch out scalar 0 0 s (by decide)
        hscratch hscalar houtbuf hout hseparate
  · exact Memory.storeLoop_sourceDigits 8 (Or.inr rfl) scalar.toNat out s.mem houtbuf hzero

end Agave.Ed25519.NAF.RIR
