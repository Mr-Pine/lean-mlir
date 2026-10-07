import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorFrame

namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR SerialPoint SerialPoint.Execution SerialFieldMul
open Reduce64.Execution (SmallRange)
open Verifier.Execution
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

private theorem pointBytes_ext (a b : BitVec 1280)
    (h : ∀ i : Fin 20, a.extractLsb' (64*i.val) 64 = b.extractLsb' (64*i.val) 64) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hlim : i / 64 < 20 := by omega
  have hb : i % 64 < 64 := Nat.mod_lt _ (by decide)
  have hoff : 64 * (i / 64) + i % 64 = i := by omega
  have hh := congrArg (fun v : BitVec 64 => v.getLsbD (i % 64)) (h ⟨i / 64, hlim⟩)
  simpa only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and, hoff] using hh

private theorem payload_flat_word (P : WordPoint) (i : Fin 20) :
    (wordKeyPoint P).bytes.extractLsb' (64*i.val) 64 = pointToWords P i := by
  let c : Fin 4 := ⟨i.val / 5, by omega⟩
  let j : Fin 5 := ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩
  have h := payload_word (wordKeyPoint P) c j
  have hoff : 320*c.val + 64*j.val = 64*i.val := by dsimp [c, j]; omega
  rw [hoff] at h
  refine h.trans ?_
  fin_cases i <;> rfl

/-- Whole-payload equality follows from the twenty exact limb observations;
it does not require canonical field representations. -/
theorem readWordPoint_bytes (s : GlobalState) (out : Pointer) (P : WordPoint)
    (hout : SmallRange s.mem out 160) (hr : readWordPoint s out = P) :
    s.mem.readAt out 1280 = (wordKeyPoint P).bytes := by
  have hinv (w : PointWords) : pointToWords (pointFromWords w) = w := by
    funext i
    fin_cases i <;> rfl
  rw [readWordPoint_eq] at hr
  have hwords := congrArg pointToWords hr
  rw [hinv] at hwords
  apply pointBytes_ext
  intro i
  have hsmall : 8*i.val < 2^64 := by omega
  have hbits : (BitVec.ofNat 64 (8*i.val)).toNat * 8 + 64 ≤ 1280 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall]
    omega
  have hm := MemoryState.readAt_add_of_readAt hout.fits
    (hout.no_wrap (k := 8*i.val) (by omega)) hbits (rfl : s.mem.readAt out 1280 = _)
  have hword := congrFun hwords i
  change s.mem.readAt (out.add (BitVec.ofNat 64 (8*i.val))) 64 = _ at hword
  have hoff : 8*i.val*8 = 64*i.val := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall, hoff] at hm
  exact hm.symm.trans (hword.trans (payload_flat_word P i).symm)

/-- The concrete cofactor state satisfies the verifier's complete frame:
wellformedness, preservation of live caller objects, and all disjoint reads. -/
theorem cofactorState_frame (s : GlobalState) (out input : Pointer)
    (hwf : s.WF) (hout : SmallRange s.mem out 160) (hin : SmallRange s.mem input 120) :
    Dalek.OutputFrame s (cofactorState s out input) out 160 := by
  rw [cofactorState_eq_pointPost s out input hwf hout hin]
  refine ⟨pointPost_wf s hwf out _ 19, ?_, ?_⟩
  · intro q n hq
    exact smallRange_storePointWords hq out _
  · intro q bits hd
    exact readAt_storePointWords_frame s.mem out q _ bits hout hd

/-- Exact ABI bytes of the valid times-eight result. The source's ordinary
valid-point bytes supply all input bounds and representation facts. -/
theorem cofactorState_payload (s : GlobalState) (out input : Pointer) (P : Verifier.Execution.ValidPoint)
    (hwf : s.WF) (hout : SmallRange s.mem out 160)
    (hin : Dalek.ReadBytes s input 160 P.bytes) :
    Dalek.ReadBytes (cofactorState s out input) out 160 (SmallOrder.ValidPoint.timesEight P).bytes := by
  have hi120 := smallRange_add hin.1 (k := 0) (count := 120) (by decide)
  simp only [Pointer.add_zero] at hi120
  have ho := (cofactorState_frame s out input hwf hout hi120).live out 160 hout
  refine ⟨ho, ?_⟩
  apply readWordPoint_bytes _ _ _ ho
  rw [cofactorState_read s out input hwf hout hi120, readWordPoint_layout s input P.words hin]

end Agave.Ed25519.SmallOrder.Execution
