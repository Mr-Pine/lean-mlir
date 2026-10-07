import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline956Composition

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline956
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
open Verifier.Execution.Dalek (ReadBytes disjoint_add_subrange)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000

/-- Whole-field readback for the actual scalar, vector, vector store order. -/
theorem storeRoot_read320 (m : MemoryState) (r : Pointer) (a : Words)
    (hr : SmallRange m r 40) : (storeRoot m r a).readAt r 320 = limbBytes a := by
  have h0 := MemoryState.readAt_add_storeAt (p := r) (off := 0#64)
    (v := 320) hr.fits (hr.no_wrap (k := 0) (by decide)) (by decide) (a 0)
  have h8 := MemoryState.readAt_add_storeAt (p := r) (off := 8#64)
    (v := 320) (m := m.storeAt r (a 0)) hr.fits.storeAt
    (hr.no_wrap (k := 8) (by decide)) (by decide) (a 2 ++ a 1)
  have h24 := MemoryState.readAt_add_storeAt (p := r) (off := 24#64)
    (v := 320) (m := (m.storeAt r (a 0)).storeAt (r.add 8#64) (a 2 ++ a 1))
    hr.fits.storeAt.storeAt (hr.no_wrap (k := 24) (by decide)) (by decide) (a 4 ++ a 3)
  simp only [Pointer.add_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.zero_mul, Nat.reduceMul] at h0 h8 h24
  simp only [storeRoot,h24,h8,h0]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Memory.getLsbD_spliceBits,limbBytes,BitVec.getLsbD_append]
  grind

theorem tailState_live (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (h : SmallRange s.mem q bytes) : SmallRange (tailState s r t b x y).mem q bytes :=
  ((h.storeAt _ _).storeAt _ _).storeAt _ _

theorem tailState_wf (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (h : s.WF) : (tailState s r t b x y).WF :=
  ((h.add_blocks (k := 1)).storeAt.storeAt).storeAt

theorem tailState_read (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (hr : SmallRange s.mem r 40) :
    (tailState s r t b x y).mem.readAt r 320 = limbBytes (rootWords r t b x y) :=
  storeRoot_read320 s.mem r _ hr

theorem tailState_readLimbs (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (hr : SmallRange s.mem r 40) :
    readLimbs (tailState s r t b x y) r = rootWords r t b x y :=
  readLimbs_of_limbBytes _ r _ (tailState_live s r t b x y hr) (tailState_read s r t b x y hr)

theorem tailState_frame (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (hr : SmallRange s.mem r 40) (q : Pointer) (bits : Nat)
    (hd : (Range.of q bits).Disjoint (Range.of r 320)) :
    (tailState s r t b x y).mem.readAt q bits = s.mem.readAt q bits := by
  have h0 := disjoint_add_subrange hr hd (k := 0) (count := 8) (by decide)
  have h8 := disjoint_add_subrange hr hd (k := 8) (count := 16) (by decide)
  have h24 := disjoint_add_subrange hr hd (k := 24) (count := 16) (by decide)
  simp only [Pointer.add_zero] at h0
  simp only [tailState,storeRoot,MemoryState.readAt_storeAt_disjoint h24.symm,
    MemoryState.readAt_storeAt_disjoint h8.symm,MemoryState.readAt_storeAt_disjoint h0.symm]

theorem output_ready (E : Env program.Γ) (s : GlobalState)
    (out r t : Pointer) (b first second : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ho : SmallRange s.mem out 48)
    (hd : (Range.of out 384).Disjoint (Range.of r 320))
    (hout : E.read (%arg0) = .value out)
    (hfirst : E.read (%430) = .value first) (hsecond : E.read (%236) = .value second)
    (hforty : E.read (%1) = .value 40#64) :
    ExecutionOutputReady (env1047 E r t b x y) (tailState s r t b x y) out ⟨r, first, second⟩ := by
  refine ⟨tailState_wf s r t b x y hwf, tailState_live s r t b x y ho,
    tailState_live s r t b x y hr, hd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, env1017, env1018, env1019, env1020, env1021, env1022, env1023, env1024, env1025, env1026, env1028, env1029, env1030, env1031, env1032, env1033, env1034, env1037, env1038, env1042, env1043, env1047, mlir_env] using hout
  · simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, env1017, env1018, env1019, env1020, env1021, env1022, env1023, env1024, env1025, env1026, env1028, env1029, env1030, env1031, env1032, env1033, env1034, env1037, env1038, env1042, env1043, env1047, mlir_env] using he.e79
  · simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, env1017, env1018, env1019, env1020, env1021, env1022, env1023, env1024, env1025, env1026, env1028, env1029, env1030, env1031, env1032, env1033, env1034, env1037, env1038, env1042, env1043, env1047, mlir_env] using hfirst
  · simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, env1017, env1018, env1019, env1020, env1021, env1022, env1023, env1024, env1025, env1026, env1028, env1029, env1030, env1031, env1032, env1033, env1034, env1037, env1038, env1042, env1043, env1047, mlir_env] using hsecond
  · simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, env1017, env1018, env1019, env1020, env1021, env1022, env1023, env1024, env1025, env1026, env1028, env1029, env1030, env1031, env1032, env1033, env1034, env1037, env1038, env1042, env1043, env1047, mlir_env] using he.e3
  · simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, env1017, env1018, env1019, env1020, env1021, env1022, env1023, env1024, env1025, env1026, env1028, env1029, env1030, env1031, env1032, env1033, env1034, env1037, env1038, env1042, env1043, env1047, mlir_env] using hforty

/-- The final tail plus checked output stores, rooted in concrete incoming words. -/
theorem output_run_from956 (g : Globals) (E : Env program.Γ) (s : GlobalState)
    (out r t : Pointer) (b first second : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40)
    (hx : readLimbs s r = x) (hy : readLimbs s t = y)
    (ho : SmallRange s.mem out 48)
    (hd : (Range.of out 384).Disjoint (Range.of r 320))
    (hout : E.read (%arg0) = .value out)
    (hfirst : E.read (%430) = .value first) (hsecond : E.read (%236) = .value second)
    (hforty : E.read (%1) = .value 40#64) :
    Cutpoint.resume (program sqrtRatioPrimitives g) 0 956 E s =
      .value (.nil, outputState (tailState s r t b x y) out (first ||| second)
        (limbBytes (rootWords r t b x y))) := by
  rw [cutpoint g E s r t b x y he hwf hr ht hx hy]
  have ready := output_ready E s out r t b first second x y he hwf hr ho hd
    hout hfirst hsecond hforty
  rw [output_run g _ _ out r first second ready.wf ready.outputLive ready.rootLive
    ready.disjoint ready.outputRegister ready.rootRegister ready.firstRegister
    ready.secondRegister ready.eightRegister ready.fortyRegister,
    tailState_read s r t b x y hr]

/-- The root actually read from memory has the specified field denotation. -/
theorem stored_root_field (s : GlobalState) (r t : Pointer)
    (u v : Pow22501.TightWords) (hr : SmallRange s.mem r 40) :
    wordValue (readLimbs (tailState s r t
      (byte (equalWords (wordCheck u v) (negativeWord u) ||
        equalWords (wordCheck u v) ((negativeWord u).mul sqrtM1Word)))
      (wordCandidate u v).limbs (sqrtM1Word.mul (wordCandidate u v)).limbs) r) =
        (Decompress.sqrtRatio (wordValue u.limbs) (wordValue v.limbs)).2 := by
  rw [tailState_readLimbs _ _ _ _ _ _ hr, rootWords_sqrt]
  exact congrArg Prod.snd (wordSqrt_value u v)

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline956
