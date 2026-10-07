import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialNAFFrame
import SSA.Projects.Agave.Ed25519.Proof.NAF.TotalLoop

/-!
# Total execution of the two inlined serial NAF loops

The induction follows the actual imported backedges and proves the exact
output stores. Exits continue at original block 7 or 14. No hypothesis assumes
termination, digit validity, index safety, or equivalence of an entire loop.
-/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR NAF NAF.RIR
open NAF.Memory (Buffer)
set_option maxRecDepth 10000

private theorem nafState_eq {a b : NAF.State}
    (ht : a.tail = b.tail) (hc : a.carry = b.carry) : a = b := by
  cases a
  cases b
  simp_all

private theorem storeLoop_outside (width : Nat) (out : Pointer) (fuel pos : Nat)
    (state : NAF.State) (mem : MemoryState) (hpos : ¬pos < 256) :
    NAF.Memory.storeLoop width out fuel pos state mem = mem := by
  cases fuel <;> simp [NAF.Memory.storeLoop, hpos]

/-- Complete width-5 emitter, retaining its actual successor environment. -/
theorem serial_naf5_loop_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (fuel : Nat) (E : ⟪serialKernel.Γ⟫) (scratch out : Pointer)
    (scalar : BitVec 256) (pos : Fin 256) (carry : Fin 2) (s : GlobalState)
    (hbudget : 256 ≤ pos.val + fuel)
    (hscratch : Buffer s.mem scratch 40)
    (hscalar : s.mem.readAt scratch 320 = WordWindow.scalarBuffer scalar)
    (houtbuf : Buffer s.mem out 256) (hout : E.read (%41) = .value out)
    (hseparate : out.id ≠ scratch.id) :
    ∃ E' : ⟪serialKernel.Γ⟫,
      (serialKernel p g).runFrom (loopEnv5 E scratch pos carry) 2 s =
        (serialKernel p g).runFrom E' 7
          {s with mem := NAF.Memory.storeLoop 5 out fuel pos.val ⟨scalar.toNat / 2 ^ pos.val, carry.val⟩ s.mem} ∧
      E'.read (%41) = .value out ∧
      PrefixEq (loopEnv5 E scratch pos carry) E' 43 := by
  induction fuel generalizing E pos carry s with
  | zero => have := pos.isLt; omega
  | succ fuel ih =>
    by_cases heven :
        (sum5 (mask5 (WordWindow.rawWindow (WordWindow.scalarBuffer scalar) pos.val 5)) carry).val % 2 = 0
    · have hsource : ((scalar.toNat / 2 ^ pos.val) % 32 + carry.val) % 2 = 0 := by
        simpa only [sum5, NAF.RIR.mask5_scalar] using heven
      have hstep := NAF.RIR.even_step5 (scalar.toNat / 2 ^ pos.val) carry hsource
      have htail : scalar.toNat / 2 ^ pos.val / 2 = scalar.toNat / 2 ^ (pos.val + 1) := by
        rw [Nat.div_div_eq_div_mul, pow_succ]
      have hiter := serial5_even_iteration p g E scratch pos carry
        (WordWindow.scalarBuffer scalar) s hscratch hscalar heven
      rw [NAF.Memory.storeLoop, if_pos pos.isLt, hstep]
      change ∃ E', _ = (serialKernel p g).runFrom E' 7
        {s with mem := NAF.Memory.storeLoop 5 out fuel (pos.val + 1) ⟨scalar.toNat / 2 ^ pos.val / 2, carry.val⟩ s.mem} ∧ _
      rw [htail]
      by_cases hnext : pos.val + 1 < 256
      · rw [dif_pos hnext] at hiter
        obtain ⟨E', hrun, hread, hframe⟩ := ih
          (evenNextEnv5 E scratch pos carry (WordWindow.scalarBuffer scalar))
          ⟨pos.val + 1, hnext⟩ carry s (by change 256 ≤ (pos.val + 1) + fuel; omega) hscratch hscalar houtbuf
          (by rw [evenNextEnv5_output]; exact hout)
        rw [evenNextEnv5_normalized] at hframe
        exact ⟨E', hiter.trans hrun, hread,
          (evenNextEnv5_frame E scratch pos carry (WordWindow.scalarBuffer scalar)).trans hframe⟩
      · rw [dif_neg hnext] at hiter
        rw [storeLoop_outside 5 out fuel (pos.val + 1) _ _ hnext]
        refine ⟨evenResult5 (controlEnv5 E scratch pos carry
          (WordWindow.scalarBuffer scalar)) pos, hiter, ?_,
          evenExitEnv5_frame E scratch pos carry (WordWindow.scalarBuffer scalar)⟩
        simpa [evenResult5, evenInput5, mlir_env, controlEnv5_output] using hout
    · obtain ⟨hdigit, hbyte, hadvance, hcarry⟩ :=
        NAF.RIR.odd_step5_scalar scalar pos carry heven
      let window := sum5 (mask5 (WordWindow.rawWindow
        (WordWindow.scalarBuffer scalar) pos.val 5)) carry
      let s' := {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte5 window)}
      have hscratch' : Buffer s'.mem scratch 40 := hscratch.storeAt _ _
      have houtbuf' : Buffer s'.mem out 256 := houtbuf.storeAt _ _
      have hscalar' : s'.mem.readAt scratch 320 = WordWindow.scalarBuffer scalar := by
        change (s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte5 window)).readAt scratch 320 = _
        rw [MemoryState.readAt_storeAt_disjoint
          (p := out.add (BitVec.ofNat 64 pos.val)) (q := scratch)
          (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hseparate)) (byte5 window)]
        exact hscalar
      have hstate : (NAF.step 5 ⟨scalar.toNat / 2 ^ pos.val, carry.val⟩).next =
          ⟨scalar.toNat / 2 ^ (pos.val + 5), (nextCarry5 window).val⟩ := by
        apply nafState_eq
        · have ht := next_tail_of_original 5 scalar.toNat pos.val carry.val
          simpa only [hadvance] using ht
        · exact hcarry.symm
      have hiter := serial5_odd_iteration p g E scratch out pos carry
        (WordWindow.scalarBuffer scalar) s hscratch hscalar houtbuf hout heven
      dsimp only at hiter
      rw [NAF.Memory.storeLoop, if_pos pos.isLt]
      dsimp only
      rw [if_neg hdigit, ← hbyte, hadvance, hstate]
      by_cases hnext : pos.val + 5 < 256
      · rw [dif_pos hnext] at hiter
        obtain ⟨E', hrun, hread, hframe⟩ := ih
          (oddNextEnv5 E scratch out pos carry (WordWindow.scalarBuffer scalar))
          ⟨pos.val + 5, hnext⟩ (nextCarry5 window) s' (by change 256 ≤ (pos.val + 5) + fuel; omega)
          hscratch' hscalar' houtbuf' (by rw [oddNextEnv5_output]; exact hout)
        rw [oddNextEnv5_normalized] at hframe
        exact ⟨E', hiter.trans hrun, hread,
          (oddNextEnv5_frame E scratch out pos carry (WordWindow.scalarBuffer scalar)).trans hframe⟩
      · rw [dif_neg hnext] at hiter
        rw [storeLoop_outside 5 out fuel (pos.val + 5) _ _ hnext]
        refine ⟨storeResult5 (controlEnv5 E scratch pos carry
          (WordWindow.scalarBuffer scalar)) out pos window, hiter, ?_,
          oddExitEnv5_frame E scratch out pos carry (WordWindow.scalarBuffer scalar)⟩
        simpa [storeResult5, storeInput5, mlir_env, controlEnv5_output] using hout

/-- All 256 bytes match the source NAF, including zero bytes skipped by the
loop, before the original caller continuation executes. -/
theorem serial_naf5_loop_sourceDigits (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (scratch out : Pointer) (scalar : BitVec 256)
    (s : GlobalState) (hscratch : Buffer s.mem scratch 40)
    (hscalar : s.mem.readAt scratch 320 = WordWindow.scalarBuffer scalar)
    (houtbuf : Buffer s.mem out 256) (hout : E.read (%41) = .value out)
    (hseparate : out.id ≠ scratch.id) (hzero : s.mem.readAt out 2048 = 0) :
    ∃ (E' : ⟪serialKernel.Γ⟫) (s' : GlobalState),
      (serialKernel p g).runFrom (loopEnv5 E scratch 0 0) 2 s =
        (serialKernel p g).runFrom E' 7 s' ∧
      E'.read (%41) = .value out ∧
      PrefixEq (loopEnv5 E scratch 0 0) E' 43 ∧
      (∀ i : Fin 256, s'.mem.readAt (out.add (BitVec.ofNat 64 i.val)) 8 =
        BitVec.ofInt 8 (sourceDigits 5 scalar.toNat i)) := by
  obtain ⟨E', hrun, hread, hframe⟩ := serial_naf5_loop_run p g 256 E scratch out scalar 0 0 s
    (by decide) hscratch hscalar houtbuf hout hseparate
  refine ⟨E', {s with mem := NAF.Memory.storeLoop 5 out 256 0 ⟨scalar.toNat, 0⟩ s.mem}, ?_, hread, hframe, ?_⟩
  · simpa only [Fin.val_zero, pow_zero, Nat.div_one] using hrun
  · exact NAF.Memory.storeLoop_sourceDigits 5 (Or.inl rfl)
      scalar.toNat out s.mem houtbuf hzero

/-- Complete width-8 emitter, retaining its actual successor environment. -/
theorem serial_naf8_loop_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (fuel : Nat) (E : ⟪serialKernel.Γ⟫) (scratch out : Pointer)
    (scalar : BitVec 256) (pos : Fin 256) (carry : Fin 2) (s : GlobalState)
    (hbudget : 256 ≤ pos.val + fuel)
    (hscratch : Buffer s.mem scratch 40)
    (hscalar : s.mem.readAt scratch 320 = WordWindow.scalarBuffer scalar)
    (houtbuf : Buffer s.mem out 256) (hout : E.read (%40) = .value out)
    (hseparate : out.id ≠ scratch.id) :
    ∃ E' : ⟪serialKernel.Γ⟫,
      (serialKernel p g).runFrom (loopEnv8 E scratch pos carry) 9 s =
        (serialKernel p g).runFrom E' 14
          {s with mem := NAF.Memory.storeLoop 8 out fuel pos.val ⟨scalar.toNat / 2 ^ pos.val, carry.val⟩ s.mem} ∧
      E'.read (%40) = .value out ∧
      PrefixEq (loopEnv8 E scratch pos carry) E' 74 := by
  induction fuel generalizing E pos carry s with
  | zero => have := pos.isLt; omega
  | succ fuel ih =>
    by_cases heven :
        (sum8 (mask8 (WordWindow.rawWindow (WordWindow.scalarBuffer scalar) pos.val 8)) carry).val % 2 = 0
    · have hsource : ((scalar.toNat / 2 ^ pos.val) % 256 + carry.val) % 2 = 0 := by
        simpa only [sum8, NAF.RIR.mask8_scalar] using heven
      have hstep := NAF.RIR.even_step8 (scalar.toNat / 2 ^ pos.val) carry hsource
      have htail : scalar.toNat / 2 ^ pos.val / 2 = scalar.toNat / 2 ^ (pos.val + 1) := by
        rw [Nat.div_div_eq_div_mul, pow_succ]
      have hiter := serial8_even_iteration p g E scratch pos carry
        (WordWindow.scalarBuffer scalar) s hscratch hscalar heven
      rw [NAF.Memory.storeLoop, if_pos pos.isLt, hstep]
      change ∃ E', _ = (serialKernel p g).runFrom E' 14
        {s with mem := NAF.Memory.storeLoop 8 out fuel (pos.val + 1) ⟨scalar.toNat / 2 ^ pos.val / 2, carry.val⟩ s.mem} ∧ _
      rw [htail]
      by_cases hnext : pos.val + 1 < 256
      · rw [dif_pos hnext] at hiter
        obtain ⟨E', hrun, hread, hframe⟩ := ih
          (evenNextEnv8 E scratch pos carry (WordWindow.scalarBuffer scalar))
          ⟨pos.val + 1, hnext⟩ carry s (by change 256 ≤ (pos.val + 1) + fuel; omega) hscratch hscalar houtbuf
          (by rw [evenNextEnv8_output]; exact hout)
        rw [evenNextEnv8_normalized] at hframe
        exact ⟨E', hiter.trans hrun, hread,
          (evenNextEnv8_frame E scratch pos carry (WordWindow.scalarBuffer scalar)).trans hframe⟩
      · rw [dif_neg hnext] at hiter
        rw [storeLoop_outside 8 out fuel (pos.val + 1) _ _ hnext]
        refine ⟨evenResult8 (controlEnv8 E scratch pos carry
          (WordWindow.scalarBuffer scalar)) pos, hiter, ?_,
          evenExitEnv8_frame E scratch pos carry (WordWindow.scalarBuffer scalar)⟩
        simpa [evenResult8, evenInput8, mlir_env, controlEnv8_output] using hout
    · obtain ⟨hdigit, hbyte, hadvance, hcarry⟩ :=
        NAF.RIR.odd_step8_scalar scalar pos carry heven
      let window := sum8 (mask8 (WordWindow.rawWindow
        (WordWindow.scalarBuffer scalar) pos.val 8)) carry
      let s' := {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)}
      have hscratch' : Buffer s'.mem scratch 40 := hscratch.storeAt _ _
      have houtbuf' : Buffer s'.mem out 256 := houtbuf.storeAt _ _
      have hscalar' : s'.mem.readAt scratch 320 = WordWindow.scalarBuffer scalar := by
        change (s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)).readAt scratch 320 = _
        rw [MemoryState.readAt_storeAt_disjoint
          (p := out.add (BitVec.ofNat 64 pos.val)) (q := scratch)
          (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hseparate)) (byte8 window)]
        exact hscalar
      have hstate : (NAF.step 8 ⟨scalar.toNat / 2 ^ pos.val, carry.val⟩).next =
          ⟨scalar.toNat / 2 ^ (pos.val + 8), (nextCarry8 window).val⟩ := by
        apply nafState_eq
        · have ht := next_tail_of_original 8 scalar.toNat pos.val carry.val
          simpa only [hadvance] using ht
        · exact hcarry.symm
      have hiter := serial8_odd_iteration p g E scratch out pos carry
        (WordWindow.scalarBuffer scalar) s hscratch hscalar houtbuf hout heven
      dsimp only at hiter
      rw [NAF.Memory.storeLoop, if_pos pos.isLt]
      dsimp only
      rw [if_neg hdigit, ← hbyte, hadvance, hstate]
      by_cases hnext : pos.val + 8 < 256
      · rw [dif_pos hnext] at hiter
        obtain ⟨E', hrun, hread, hframe⟩ := ih
          (oddNextEnv8 E scratch out pos carry (WordWindow.scalarBuffer scalar))
          ⟨pos.val + 8, hnext⟩ (nextCarry8 window) s' (by change 256 ≤ (pos.val + 8) + fuel; omega)
          hscratch' hscalar' houtbuf' (by rw [oddNextEnv8_output]; exact hout)
        rw [oddNextEnv8_normalized] at hframe
        exact ⟨E', hiter.trans hrun, hread,
          (oddNextEnv8_frame E scratch out pos carry (WordWindow.scalarBuffer scalar)).trans hframe⟩
      · rw [dif_neg hnext] at hiter
        rw [storeLoop_outside 8 out fuel (pos.val + 8) _ _ hnext]
        refine ⟨storeResult8 (controlEnv8 E scratch pos carry
          (WordWindow.scalarBuffer scalar)) out pos window, hiter, ?_,
          oddExitEnv8_frame E scratch out pos carry (WordWindow.scalarBuffer scalar)⟩
        simpa [storeResult8, storeInput8, mlir_env, controlEnv8_output] using hout

/-- All 256 bytes match the source NAF, including zero bytes skipped by the
loop, before the original caller continuation executes. -/
theorem serial_naf8_loop_sourceDigits (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (scratch out : Pointer) (scalar : BitVec 256)
    (s : GlobalState) (hscratch : Buffer s.mem scratch 40)
    (hscalar : s.mem.readAt scratch 320 = WordWindow.scalarBuffer scalar)
    (houtbuf : Buffer s.mem out 256) (hout : E.read (%40) = .value out)
    (hseparate : out.id ≠ scratch.id) (hzero : s.mem.readAt out 2048 = 0) :
    ∃ (E' : ⟪serialKernel.Γ⟫) (s' : GlobalState),
      (serialKernel p g).runFrom (loopEnv8 E scratch 0 0) 9 s =
        (serialKernel p g).runFrom E' 14 s' ∧
      E'.read (%40) = .value out ∧
      PrefixEq (loopEnv8 E scratch 0 0) E' 74 ∧
      (∀ i : Fin 256, s'.mem.readAt (out.add (BitVec.ofNat 64 i.val)) 8 =
        BitVec.ofInt 8 (sourceDigits 8 scalar.toNat i)) := by
  obtain ⟨E', hrun, hread, hframe⟩ := serial_naf8_loop_run p g 256 E scratch out scalar 0 0 s
    (by decide) hscratch hscalar houtbuf hout hseparate
  refine ⟨E', {s with mem := NAF.Memory.storeLoop 8 out 256 0 ⟨scalar.toNat, 0⟩ s.mem}, ?_, hread, hframe, ?_⟩
  · simpa only [Fin.val_zero, pow_zero, Nat.div_one] using hrun
  · exact NAF.Memory.storeLoop_sourceDigits 8 (Or.inr rfl)
      scalar.toNat out s.mem houtbuf hzero

end Agave.Ed25519.DoubleBase.RIR
