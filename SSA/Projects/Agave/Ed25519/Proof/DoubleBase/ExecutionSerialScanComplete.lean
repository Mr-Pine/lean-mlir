import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialScan
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialBlocks

/-!
# Complete execution of the serial descending digit scan

The induction executes bb15 and bb17 of the imported function until bb16.
It derives the selected position from the bytes in the two live arrays and
preserves all arguments and registers below the scan temporaries. There is no
point-helper or successful-scan hypothesis.
-/
namespace Agave.Ed25519.DoubleBase.RIR

open LeanMLIR.RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000

/-- Saved registers remain available after an isolated compiler region. -/
def PrefixEq (before after : ⟪Γ⟫) (limit : Nat) : Prop :=
  after.args = before.args ∧ ∀ i : Fin Γ.n, i.val < limit → after.vals i = before.vals i

theorem PrefixEq.refl (E : ⟪Γ⟫) (limit : Nat) : PrefixEq E E limit :=
  ⟨rfl, fun _ _ => rfl⟩

theorem PrefixEq.trans {a b c : ⟪Γ⟫} (h₁ : PrefixEq a b limit)
    (h₂ : PrefixEq b c limit) : PrefixEq a c limit := by
  exact ⟨h₂.1.trans h₁.1, fun i hi => (h₂.2 i hi).trans (h₁.2 i hi)⟩

theorem PrefixEq.write {a b : ⟪Γ⟫} (h : PrefixEq a b limit)
    (dst : Dst Γ ty) (value : ⟦ty⟧) (hi : limit ≤ dst.i.val) :
    PrefixEq a (b.write dst value) limit := by
  refine ⟨h.1, ?_⟩
  intro i hlt
  have hne : i ≠ dst.i := by intro he; have := congrArg Fin.val he; omega
  change (if he : i = dst.i then he ▸ (dst.h.symm ▸ value) else b.vals i) = _
  rw [dif_neg hne]
  exact h.2 i hlt

theorem PrefixEq.read {a b : ⟪Γ⟫} (h : PrefixEq a b limit)
    (reg : Reg Γ ty) (hr : ∀ i ht, reg = .val i ht → i.val < limit) :
    b.read reg = a.read reg := by
  cases reg with
  | arg i ht => simp only [Env.read, h.1]
  | val i ht => simp only [Env.read, h.2 i (hr i ht rfl)]

def scanDigits (mem : MemoryState) (array : Pointer) : Digits :=
  fun i => (mem.readAt (array.add (BitVec.ofNat 64 i)) 8).toInt

theorem byte_eq_zero_iff : ∀ byte : BitVec 8, byte = 0#8 ↔ byte.toInt = 0 := by
  decide +kernel

def scanReady (E : ⟪serialKernel.Γ⟫) (a b : Pointer) (i : Fin 256) :
    ⟪serialKernel.Γ⟫ :=
  scanInput (E[%4 := .value 0#64, %40 := .value b]) a i

def scanAfterA (E : ⟪serialKernel.Γ⟫) (a b : Pointer) (i : Fin 256)
    (mem : MemoryState) : ⟪serialKernel.Γ⟫ :=
  scanResult (scanReady E a b i) a i (mem.readAt (a.add (BitVec.ofNat 64 i.val)) 8)

def scanAfterB (E : ⟪serialKernel.Γ⟫) (a b : Pointer) (i : Fin 256)
    (mem : MemoryState) : ⟪serialKernel.Γ⟫ :=
  scanBResult (scanAfterA E a b i mem) b i (mem.readAt (b.add (BitVec.ofNat 64 i.val)) 8)

def scanBack (E : ⟪serialKernel.Γ⟫) (a b : Pointer) (i : Fin 256)
    (mem : MemoryState) : ⟪serialKernel.Γ⟫ :=
  (scanAfterB E a b i mem)[%102 := .value (BitVec.ofNat 64 i.val)]

theorem scanInput_ready (E : ⟪serialKernel.Γ⟫) (a b : Pointer) (i : Fin 256) :
    scanInput (scanReady E a b i) a i = scanReady E a b i := by
  let base := scanReady E a b i
  have h1 : base.read (%1) = .value 0#8 := by simp [base, scanReady, scanInput, mlir_env]
  have h19 : base.read (%19) = .value (-1 : BitVec 64) := by simp [base, scanReady, scanInput, mlir_env]
  have h41 : base.read (%41) = .value a := by simp [base, scanReady, scanInput, mlir_env]
  have h102 : base.read (%102) = .value (BitVec.ofNat 64 (i.val + 1)) := by simp [base, scanReady, scanInput, mlir_env]
  change scanInput base a i = base
  unfold scanInput
  rw [Env.write_of_read base (%1) h1, Env.write_of_read base (%19) h19,
    Env.write_of_read base (%41) h41, Env.write_of_read base (%102) h102]

theorem scanBInput_afterA (E : ⟪serialKernel.Γ⟫) (a b : Pointer) (i : Fin 256)
    (mem : MemoryState) : scanBInput (scanAfterA E a b i mem) b i = scanAfterA E a b i mem := by
  let base := scanAfterA E a b i mem
  have h1 : base.read (%1) = .value 0#8 := by simp [base, scanAfterA, scanResult, scanReady, scanInput, mlir_env]
  have h4 : base.read (%4) = .value 0#64 := by simp [base, scanAfterA, scanResult, scanReady, scanInput, mlir_env]
  have h40 : base.read (%40) = .value b := by simp [base, scanAfterA, scanResult, scanReady, scanInput, mlir_env]
  have h103 : base.read (%103) = .value (BitVec.ofNat 64 i.val) := by simp [base, scanAfterA, scanResult, scanReady, scanInput, mlir_env]
  change scanBInput base b i = base
  unfold scanBInput
  rw [Env.write_of_read base (%1) h1, Env.write_of_read base (%4) h4,
    Env.write_of_read base (%40) h40, Env.write_of_read base (%103) h103]

theorem scanAfterA_prefix (E : ⟪serialKernel.Γ⟫) (a b : Pointer) (i : Fin 256)
    (mem : MemoryState) : PrefixEq (scanReady E a b i) (scanAfterA E a b i mem) 102 := by
  unfold scanAfterA scanResult
  rw [scanInput_ready]
  apply PrefixEq.write _ _ _ (by decide)
  apply PrefixEq.write _ _ _ (by decide)
  apply PrefixEq.write _ _ _ (by decide)
  apply PrefixEq.write _ _ _ (by decide)
  exact PrefixEq.refl _ _

theorem scanAfterB_prefix (E : ⟪serialKernel.Γ⟫) (a b : Pointer) (i : Fin 256)
    (mem : MemoryState) : PrefixEq (scanReady E a b i) (scanAfterB E a b i mem) 102 := by
  unfold scanAfterB scanBResult
  rw [scanBInput_afterA]
  apply PrefixEq.write _ _ _ (by decide)
  apply PrefixEq.write _ _ _ (by decide)
  apply PrefixEq.write _ _ _ (by decide)
  apply PrefixEq.write _ _ _ (by decide)
  apply PrefixEq.write _ _ _ (by decide)
  exact scanAfterA_prefix E a b i mem

theorem scanBack_prefix (E : ⟪serialKernel.Γ⟫) (a b : Pointer) (i : Fin 256)
    (mem : MemoryState) : PrefixEq (scanReady E a b i) (scanBack E a b i mem) 102 :=
  (scanAfterB_prefix E a b i mem).write _ _ (by decide)

theorem scanBack_ready (E : ⟪serialKernel.Γ⟫) (a b : Pointer) (n : Nat)
    (hn : n + 1 < 256) (mem : MemoryState) :
    scanReady (scanBack E a b ⟨n + 1, hn⟩ mem) a b ⟨n, by omega⟩ =
      scanBack E a b ⟨n + 1, hn⟩ mem := by
  let base := scanBack E a b ⟨n + 1, hn⟩ mem
  have h4 : base.read (%4) = .value 0#64 := by
    simp [base, scanBack, scanAfterB, scanBResult, scanBInput, scanAfterA, scanResult, scanReady, scanInput, mlir_env]
  have h40 : base.read (%40) = .value b := by
    simp [base, scanBack, scanAfterB, scanBResult, scanBInput, scanAfterA, scanResult, scanReady, scanInput, mlir_env]
  have h1 : base.read (%1) = .value 0#8 := by
    simp [base, scanBack, scanAfterB, scanBResult, scanBInput, scanAfterA, scanResult, scanReady, scanInput, mlir_env]
  have h19 : base.read (%19) = .value (-1 : BitVec 64) := by
    simp [base, scanBack, scanAfterB, scanBResult, scanBInput, scanAfterA, scanResult, scanReady, scanInput, mlir_env]
  have h41 : base.read (%41) = .value a := by
    simp [base, scanBack, scanAfterB, scanBResult, scanBInput, scanAfterA, scanResult, scanReady, scanInput, mlir_env]
  have h102 : base.read (%102) = .value (BitVec.ofNat 64 (n + 1)) := by
    simp [base, scanBack, mlir_env]
  change scanReady base a b ⟨n, by omega⟩ = base
  unfold scanReady scanInput
  rw [Env.write_of_read base (%4) h4, Env.write_of_read base (%40) h40,
    Env.write_of_read base (%1) h1, Env.write_of_read base (%19) h19,
    Env.write_of_read base (%41) h41, Env.write_of_read base (%102) h102]

theorem serial_scan_a_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (a b : Pointer) (i : Fin 256) (s : GlobalState)
    (ha : Buffer s.mem a 256) :
    (serialKernel p g).runFrom (scanReady E a b i) 15 s =
      (serialKernel p g).runFrom (scanAfterA E a b i s.mem)
        (if s.mem.readAt (a.add (BitVec.ofNat 64 i.val)) 8 = 0#8 then 17 else 16) s := by
  have h := serial_scan_a_block (scanReady E a b i) a i s ha
  rw [scanInput_ready] at h
  rw [Func.runFrom_eq, show (serialKernel p g).blocks 15 = serialKernel.bb15 from rfl, h]
  rfl

theorem serial_scan_b_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (a b : Pointer) (i : Fin 256) (s : GlobalState)
    (hb : Buffer s.mem b 256) :
    (serialKernel p g).runFrom (scanAfterA E a b i s.mem) 17 s =
      if s.mem.readAt (b.add (BitVec.ofNat 64 i.val)) 8 ≠ 0#8 ∨ i.val = 0 then
        (serialKernel p g).runFrom (scanAfterB E a b i s.mem) 16 s
      else (serialKernel p g).runFrom (scanBack E a b i s.mem) 15 s := by
  have h := serial_scan_b_block (scanAfterA E a b i s.mem) b i s hb
  rw [scanBInput_afterA] at h
  rw [Func.runFrom_eq, show (serialKernel p g).blocks 17 = serialKernel.bb17 from rfl, h]
  dsimp only
  split_ifs <;> rfl

/-- The complete imported scan reaches table construction at exactly the
source scan index. Memory is unchanged, including both NAF arrays. -/
theorem serial_scan_complete (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (a b : Pointer) (s : GlobalState) (ha : Buffer s.mem a 256) (hb : Buffer s.mem b 256)
    (n : Nat) (hn : n < 256) (E : ⟪serialKernel.Γ⟫) :
    ∃ final : ⟪serialKernel.Γ⟫,
      (serialKernel p g).runFrom (scanReady E a b ⟨n, hn⟩) 15 s =
        (serialKernel p g).runFrom final 16 s ∧
      final.read (%103) = .value (BitVec.ofNat 64
        (startIndex (scanDigits s.mem a) (scanDigits s.mem b) n)) ∧
      PrefixEq (scanReady E a b ⟨n, hn⟩) final 102 := by
  induction n generalizing E with
  | zero =>
      by_cases hA : s.mem.readAt (a.add (BitVec.ofNat 64 0)) 8 = 0#8
      · refine ⟨scanAfterB E a b ⟨0, hn⟩ s.mem, ?_, ?_, scanAfterB_prefix _ _ _ _ _⟩
        · rw [serial_scan_a_run p g E a b ⟨0, hn⟩ s ha, if_pos hA,
            serial_scan_b_run p g E a b ⟨0, hn⟩ s hb, if_pos (Or.inr rfl)]
        · simp [startIndex, scanAfterB, scanBResult, scanBInput, mlir_env]
      · refine ⟨scanAfterA E a b ⟨0, hn⟩ s.mem, ?_, ?_, scanAfterA_prefix _ _ _ _ _⟩
        · rw [serial_scan_a_run p g E a b ⟨0, hn⟩ s ha, if_neg hA]
        · simp [startIndex, scanAfterA, scanResult, mlir_env]
  | succ n ih =>
      by_cases hA : s.mem.readAt (a.add (BitVec.ofNat 64 (n + 1))) 8 = 0#8
      · by_cases hB : s.mem.readAt (b.add (BitVec.ofNat 64 (n + 1))) 8 = 0#8
        · obtain ⟨final, hrun, hindex, hframe⟩ := ih (by omega) (scanBack E a b ⟨n + 1, hn⟩ s.mem)
          rw [scanBack_ready E a b n hn s.mem] at hrun hframe
          refine ⟨final, ?_, ?_, (scanBack_prefix E a b ⟨n + 1, hn⟩ s.mem).trans hframe⟩
          · rw [serial_scan_a_run p g E a b ⟨n + 1, hn⟩ s ha, if_pos hA,
              serial_scan_b_run p g E a b ⟨n + 1, hn⟩ s hb,
              if_neg (by simp [hB])]
            exact hrun
          · simpa [startIndex, scanDigits, hA, hB] using hindex
        · have hnonzero : scanDigits s.mem b (n + 1) ≠ 0 := by
            exact fun h => hB ((byte_eq_zero_iff _).mpr h)
          refine ⟨scanAfterB E a b ⟨n + 1, hn⟩ s.mem, ?_, ?_, scanAfterB_prefix _ _ _ _ _⟩
          · rw [serial_scan_a_run p g E a b ⟨n + 1, hn⟩ s ha, if_pos hA,
              serial_scan_b_run p g E a b ⟨n + 1, hn⟩ s hb, if_pos (Or.inl hB)]
          · simp [startIndex, hnonzero, scanAfterB, scanBResult, scanBInput, mlir_env]
      · have hnonzero : scanDigits s.mem a (n + 1) ≠ 0 := by
          exact fun h => hA ((byte_eq_zero_iff _).mpr h)
        refine ⟨scanAfterA E a b ⟨n + 1, hn⟩ s.mem, ?_, ?_, scanAfterA_prefix _ _ _ _ _⟩
        · rw [serial_scan_a_run p g E a b ⟨n + 1, hn⟩ s ha, if_neg hA]
        · simp [startIndex, hnonzero, scanAfterA, scanResult, mlir_env]

/-- Source byte correctness is supplied by the preceding executed NAF loops;
this bridge does not assume the selected index or a successful scan. -/
theorem scanDigits_naf (mem : MemoryState) (array : Pointer) (width n : Nat)
    (hw : NAF.Supported width)
    (hbytes : ∀ i : Fin 256, mem.readAt (array.add (BitVec.ofNat 64 i.val)) 8 =
      BitVec.ofInt 8 (NAF.sourceDigits width n i)) (i : Fin 256) :
    scanDigits mem array i.val = nafDigits width n i.val := by
  unfold scanDigits
  rw [hbytes]
  have hbound := NAF.sourceDigits_bounds width hw n i
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · rcases hw with rfl | rfl <;> norm_num at hbound ⊢ <;> omega
  · rcases hw with rfl | rfl <;> norm_num at hbound ⊢ <;> omega

/-- Once the executed NAF loops have supplied their byte arrays, the imported
scan selects exactly the shared mathematical schedule's starting position. -/
theorem serial_scan_naf (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (a b : Pointer) (s : GlobalState) (scalarA scalarB : Nat)
    (ha : Buffer s.mem a 256) (hb : Buffer s.mem b 256)
    (hbytesA : ∀ i : Fin 256, s.mem.readAt (a.add (BitVec.ofNat 64 i.val)) 8 =
      BitVec.ofInt 8 (NAF.sourceDigits 5 scalarA i))
    (hbytesB : ∀ i : Fin 256, s.mem.readAt (b.add (BitVec.ofNat 64 i.val)) 8 =
      BitVec.ofInt 8 (NAF.sourceDigits 8 scalarB i)) :
    ∃ final : ⟪serialKernel.Γ⟫,
      (serialKernel p g).runFrom (scanReady E a b 255) 15 s =
        (serialKernel p g).runFrom final 16 s ∧
      final.read (%103) = .value (BitVec.ofNat 64
        (startIndex (nafDigits 5 scalarA) (nafDigits 8 scalarB) 255)) ∧
      PrefixEq (scanReady E a b 255) final 102 := by
  obtain ⟨final, hrun, hindex, hframe⟩ := serial_scan_complete p g a b s ha hb 255 (by decide) E
  have hstart := startIndex_congr (scanDigits s.mem a) (scanDigits s.mem b)
    (nafDigits 5 scalarA) (nafDigits 8 scalarB) 255
    (fun i hi => scanDigits_naf s.mem a 5 scalarA (Or.inl rfl) hbytesA ⟨i, by omega⟩)
    (fun i hi => scanDigits_naf s.mem b 8 scalarB (Or.inr rfl) hbytesB ⟨i, by omega⟩)
  exact ⟨final, hrun, hstart ▸ hindex, hframe⟩

end Agave.Ed25519.DoubleBase.RIR
