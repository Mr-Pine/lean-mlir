import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialPrefix

/-! Complete executable scalar preparation, ending immediately before the
constructor call. Both NAF arrays and the scan index are consequences of the
actual imported CFG. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
set_option maxRecDepth 10000

theorem scanReady_of_reads (E : ⟪serialKernel.Γ⟫) (a b : Pointer) (i : Fin 256)
    (h1 : E.read (%1) = .value 0#8)
    (h4 : E.read (%4) = .value 0#64)
    (h19 : E.read (%19) = .value (-1 : BitVec 64))
    (h40 : E.read (%40) = .value b) (h41 : E.read (%41) = .value a)
    (h102 : E.read (%102) = .value (BitVec.ofNat 64 (i.val + 1))) :
    scanReady E a b i = E := by
  unfold scanReady scanInput
  rw [Env.write_of_read E (%4) h4, Env.write_of_read E (%40) h40,
    Env.write_of_read E (%1) h1, Env.write_of_read E (%19) h19,
    Env.write_of_read E (%41) h41, Env.write_of_read E (%102) h102]

/-- The imported scan-entry edge supplies its exact initial counter. All
other scan input registers survived the two executed NAF loops. -/
theorem scanReady_of_prefix (E F : ⟪serialKernel.Γ⟫) (g : SerialCFG.Globals)
    (s : GlobalState) (hframe : PrefixEq (serialInitial5 E g s) F 43) :
    scanReady (F[%102 := F.read (%2)]) (serialStackPtr s 11) (serialStackPtr s 10) 255 =
      F[%102 := F.read (%2)] := by
  apply scanReady_of_reads
  all_goals try simp [mlir_env]
  all_goals
    rw [hframe.read _ (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]

/-- The complete scalar preparation prefix. Its only memory premises are the
two caller scalar ranges and reads. In particular, there is no successful NAF
execution, valid digit, valid selection index, or scan-result premise. -/
theorem serial_prepare_scalars (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (s : GlobalState) (inputA inputB : Pointer) (a b : BitVec 256)
    (hwf : s.WF) (hA : Buffer s.mem inputA 32) (hB : Buffer s.mem inputB 32)
    (ha : s.mem.readAt inputA 256 = a) (hb : s.mem.readAt inputB 256 = b)
    (hargA : E.args 1 = .value inputA) (hargB : E.args 3 = .value inputB) :
    ∃ final : ⟪serialKernel.Γ⟫,
      (serialKernel p g).runFrom E 0 s =
        (serialKernel p g).runFrom final 16 (serialNAFState8 s a b) ∧
      final.read (%103) = .value (BitVec.ofNat 64
        (startIndex (nafDigits 5 a.toNat) (nafDigits 8 b.toNat) 255)) ∧
      PrefixEq (serialInitial5 E g s) final 43 ∧
      (∀ i : Fin 256, (serialNAFState8 s a b).mem.readAt
        ((serialStackPtr s 11).add (BitVec.ofNat 64 i.val)) 8 =
          BitVec.ofInt 8 (NAF.sourceDigits 5 a.toNat i)) ∧
      (∀ i : Fin 256, (serialNAFState8 s a b).mem.readAt
        ((serialStackPtr s 10).add (BitVec.ofNat 64 i.val)) 8 =
          BitVec.ofInt 8 (NAF.sourceDigits 8 b.toNat i)) := by
  obtain ⟨F, hprefix, hframe⟩ := serial_naf_prefix p g E s inputA inputB a b hwf hA hB ha hb hargA hargB
  obtain ⟨hbytesA, hbytesB⟩ := serialNAFState8_sourceDigits s a b hwf
  have hbufA : Buffer (serialNAFState8 s a b).mem (serialStackPtr s 11) 256 :=
    serialNAFState8_buffer (serialStack_buffer hwf 11 12 (by decide) (by decide))
  have hbufB : Buffer (serialNAFState8 s a b).mem (serialStackPtr s 10) 256 :=
    serialNAFState8_buffer (serialStack_buffer hwf 10 12 (by decide) (by decide))
  obtain ⟨final, hscan, hindex, hscanframe⟩ := serial_scan_naf p g
    (F[%102 := F.read (%2)]) (serialStackPtr s 11) (serialStackPtr s 10)
    (serialNAFState8 s a b) a.toNat b.toNat hbufA hbufB hbytesA hbytesB
  rw [scanReady_of_prefix E F g s hframe] at hscan hscanframe
  refine ⟨final, hprefix.trans ?_, hindex, ?_, hbytesA, hbytesB⟩
  · rw [serial8_scan_entry p g]
    exact hscan
  · have hentry : PrefixEq F (F[%102 := F.read (%2)]) 43 :=
      (PrefixEq.refl F 43).write _ _ (by decide)
    exact hframe.trans (hentry.trans (hscanframe.mono (by decide)))

end Agave.Ed25519.DoubleBase.RIR
