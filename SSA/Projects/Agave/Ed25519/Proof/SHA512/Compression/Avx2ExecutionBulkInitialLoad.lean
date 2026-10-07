import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkInitialLoadStart
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkInitialLoadMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairControl

/-! Exact execution of all 108 instructions of the dual-block initializer. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

structure BulkInitialLoadReady (E : Env program.Γ) (data scratch cache : Pointer) (n : Nat) : Prop where
  pointers : BulkInitialPointers E scratch cache
  dataPtr : E.read (%arg1) = .value data
  index : E.read (%358) = .value (BitVec.ofNat 64 n)
  one : E.read (%1) = .value 1#64
  c16 : E.read (%4) = .value 16#64
  c32 : E.read (%6) = .value 32#64
  c48 : E.read (%8) = .value 48#64
  c64 : E.read (%15) = .value 64#64
  c80 : E.read (%17) = .value 80#64
  c96 : E.read (%19) = .value 96#64
  c112 : E.read (%21) = .value 112#64
  c128 : E.read (%47) = .value 128#64
  c144 : E.read (%52) = .value 144#64
  c160 : E.read (%54) = .value 160#64
  c176 : E.read (%56) = .value 176#64
  c192 : E.read (%58) = .value 192#64
  c208 : E.read (%60) = .value 208#64
  c224 : E.read (%62) = .value 224#64
  c240 : E.read (%64) = .value 240#64
  k0 : E.read (%51) = bulkVec (constants[0]!) (constants[1]!) (constants[0]!) (constants[1]!)
  k1 : E.read (%53) = bulkVec (constants[2]!) (constants[3]!) (constants[2]!) (constants[3]!)
  k2 : E.read (%55) = bulkVec (constants[4]!) (constants[5]!) (constants[4]!) (constants[5]!)
  k3 : E.read (%57) = bulkVec (constants[6]!) (constants[7]!) (constants[6]!) (constants[7]!)
  k4 : E.read (%59) = bulkVec (constants[8]!) (constants[9]!) (constants[8]!) (constants[9]!)
  k5 : E.read (%61) = bulkVec (constants[10]!) (constants[11]!) (constants[10]!) (constants[11]!)
  k6 : E.read (%63) = bulkVec (constants[12]!) (constants[13]!) (constants[12]!) (constants[13]!)
  k7 : E.read (%65) = bulkVec (constants[14]!) (constants[15]!) (constants[14]!) (constants[15]!)

def bulkInitialLoadEnv (E : Env program.Γ) (data : Pointer) (n : Nat)
    (first second : Bytes) : Env program.Γ :=
  let E := bulkInitialStartEnv E data n
  let p := data.add (BitVec.ofNat 64 (128*n))
  let E := bulkInitialSlice0Env E p first second (constants[0]!) (constants[1]!)
  let E := bulkInitialSlice1Env E p first second (constants[2]!) (constants[3]!)
  let E := bulkInitialSlice2Env E p first second (constants[4]!) (constants[5]!)
  let E := bulkInitialSlice3Env E p first second (constants[6]!) (constants[7]!)
  let E := bulkInitialSlice4Env E p first second (constants[8]!) (constants[9]!)
  let E := bulkInitialSlice5Env E p first second (constants[10]!) (constants[11]!)
  let E := bulkInitialSlice6Env E p first second (constants[12]!) (constants[13]!)
  let E := bulkInitialSlice7Env E p first second (constants[14]!) (constants[15]!)
  E

theorem bulkInitialLoadEnv_frame (E : Env program.Γ) (data : Pointer) (n : Nat)
    (first second : Bytes) : RegFrame 360 447 E (bulkInitialLoadEnv E data n first second) := by
  unfold bulkInitialLoadEnv bulkInitialStartEnv bulkInitialSlice0Env bulkInitialSlice1Env bulkInitialSlice2Env bulkInitialSlice3Env bulkInitialSlice4Env bulkInitialSlice5Env bulkInitialSlice6Env bulkInitialSlice7Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

theorem bulk_initial_load_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch cache : Pointer) (n : Nat)
    (h : BulkInitialLoadReady E data scratch cache n)
    (hd : SmallRange mem.mem data (128*n+256))
    (hs : SmallRange mem.mem scratch 128) (hc : SmallRange mem.mem cache 640)
    (hsd : scratch.id ≠ data.id) (hcd : cache.id ≠ data.id) :
    let p := data.add (BitVec.ofNat 64 (128*n))
    let first := readBytes mem.mem p 128
    let second := readBytes mem.mem (p.add 128#64) 128
    List.foldlM Instr.run E program.bb9.body mem =
      .value (bulkInitialLoadEnv E data n first second,
        bulkInitialStores mem scratch cache first second 8) := by
  let p := data.add (BitVec.ofNat 64 (128*n))
  let first := readBytes mem.mem p 128
  let second := readBytes mem.mem (p.add 128#64) 128
  let E0 := bulkInitialStartEnv E data n
  let E1 := bulkInitialSlice0Env E0 p first second (constants[0]!) (constants[1]!)
  let E2 := bulkInitialSlice1Env E1 p first second (constants[2]!) (constants[3]!)
  let E3 := bulkInitialSlice2Env E2 p first second (constants[4]!) (constants[5]!)
  let E4 := bulkInitialSlice3Env E3 p first second (constants[6]!) (constants[7]!)
  let E5 := bulkInitialSlice4Env E4 p first second (constants[8]!) (constants[9]!)
  let E6 := bulkInitialSlice5Env E5 p first second (constants[10]!) (constants[11]!)
  let E7 := bulkInitialSlice6Env E6 p first second (constants[12]!) (constants[13]!)
  let E8 := bulkInitialSlice7Env E7 p first second (constants[14]!) (constants[15]!)
  have hstart := bulk_initial_start_body E mem data n hd h.dataPtr h.index
  have hdlive := bulk_initial_data_live mem.mem data n hd
  have hclive : SmallRange mem.mem cache 128 := smallRange_mono hc (by decide)
  have he0 : RegFrame 360 447 E E0 := (bulkInitialStartEnv_frame E data n).enlarge (by decide) (by decide)
  have he1 : RegFrame 360 447 E E1 := he0.trans ((bulkInitialSlice0Env_frame E0 p first second _ _).enlarge (by decide) (by decide))
  have he2 : RegFrame 360 447 E E2 := he1.trans ((bulkInitialSlice1Env_frame E1 p first second _ _).enlarge (by decide) (by decide))
  have he3 : RegFrame 360 447 E E3 := he2.trans ((bulkInitialSlice2Env_frame E2 p first second _ _).enlarge (by decide) (by decide))
  have he4 : RegFrame 360 447 E E4 := he3.trans ((bulkInitialSlice3Env_frame E3 p first second _ _).enlarge (by decide) (by decide))
  have he5 : RegFrame 360 447 E E5 := he4.trans ((bulkInitialSlice4Env_frame E4 p first second _ _).enlarge (by decide) (by decide))
  have he6 : RegFrame 360 447 E E6 := he5.trans ((bulkInitialSlice5Env_frame E5 p first second _ _).enlarge (by decide) (by decide))
  have he7 : RegFrame 360 447 E E7 := he6.trans ((bulkInitialSlice6Env_frame E6 p first second _ _).enlarge (by decide) (by decide))
  have hf0 := bulkInitialStores_frame mem scratch cache first second 0
  have hr0 := bulkInitialStores_load_first mem p scratch cache first second 0 0
    (by decide) hdlive (by simpa [p] using hsd) (by simpa [p] using hcd)
  have hu0 := bulkInitialStores_load_second mem p scratch cache first second 0 0
    (by decide) hdlive (by simpa [p] using hsd) (by simpa [p] using hcd)
  have hex0 := bulk_initial_slice0_body E0 (bulkInitialStores mem scratch cache first second 0)
    p scratch cache first second (constants[0]!) (constants[1]!)
    (hf0.live hdlive) (hf0.live hs) (hf0.live hclive)
    (by simp [E0, bulkInitialStartEnv, p, mlir_env])
    (by rw [he0.read (%83)]; simpa only [Pointer.add_zero] using h.pointers.scratchPtr)
    (by rw [he0.read (%82)]; simpa only [Pointer.add_zero] using h.pointers.cachePtr)
    (by rw [he0.read (%47)]; exact h.c128)
    (by rw [he0.read (%51)]; exact h.k0)
    (by simpa [first] using hr0) (by simpa [second] using hu0)
  have hf1 := bulkInitialStores_frame mem scratch cache first second 1
  have hr1 := bulkInitialStores_load_first mem p scratch cache first second 1 1
    (by decide) hdlive (by simpa [p] using hsd) (by simpa [p] using hcd)
  have hu1 := bulkInitialStores_load_second mem p scratch cache first second 1 1
    (by decide) hdlive (by simpa [p] using hsd) (by simpa [p] using hcd)
  have hex1 := bulk_initial_slice1_body E1 (bulkInitialStores mem scratch cache first second 1)
    p scratch cache first second (constants[2]!) (constants[3]!)
    (hf1.live hdlive) (hf1.live hs) (hf1.live hclive)
    (by simp [E0, E1, bulkInitialStartEnv, bulkInitialSlice0Env, p, mlir_env])
    (by rw [he1.read (%321)]; simpa only [Pointer.add_zero] using h.pointers.scratch1)
    (by rw [he1.read (%322)]; simpa only [Pointer.add_zero] using h.pointers.cache1)
    (by rw [he1.read (%52)]; exact h.c144)
    (by rw [he1.read (%4)]; exact h.c16)
    (by rw [he1.read (%53)]; exact h.k1)
    (by simpa [first] using hr1) (by simpa [second] using hu1)
  have hf2 := bulkInitialStores_frame mem scratch cache first second 2
  have hr2 := bulkInitialStores_load_first mem p scratch cache first second 2 2
    (by decide) hdlive (by simpa [p] using hsd) (by simpa [p] using hcd)
  have hu2 := bulkInitialStores_load_second mem p scratch cache first second 2 2
    (by decide) hdlive (by simpa [p] using hsd) (by simpa [p] using hcd)
  have hex2 := bulk_initial_slice2_body E2 (bulkInitialStores mem scratch cache first second 2)
    p scratch cache first second (constants[4]!) (constants[5]!)
    (hf2.live hdlive) (hf2.live hs) (hf2.live hclive)
    (by simp [E0, E1, E2, bulkInitialStartEnv, bulkInitialSlice0Env, bulkInitialSlice1Env, p, mlir_env])
    (by rw [he2.read (%323)]; simpa only [Pointer.add_zero] using h.pointers.scratch2)
    (by rw [he2.read (%324)]; simpa only [Pointer.add_zero] using h.pointers.cache2)
    (by rw [he2.read (%54)]; exact h.c160)
    (by rw [he2.read (%6)]; exact h.c32)
    (by rw [he2.read (%55)]; exact h.k2)
    (by simpa [first] using hr2) (by simpa [second] using hu2)
  have hf3 := bulkInitialStores_frame mem scratch cache first second 3
  have hr3 := bulkInitialStores_load_first mem p scratch cache first second 3 3
    (by decide) hdlive (by simpa [p] using hsd) (by simpa [p] using hcd)
  have hu3 := bulkInitialStores_load_second mem p scratch cache first second 3 3
    (by decide) hdlive (by simpa [p] using hsd) (by simpa [p] using hcd)
  have hex3 := bulk_initial_slice3_body E3 (bulkInitialStores mem scratch cache first second 3)
    p scratch cache first second (constants[6]!) (constants[7]!)
    (hf3.live hdlive) (hf3.live hs) (hf3.live hclive)
    (by simp [E0, E1, E2, E3, bulkInitialStartEnv, bulkInitialSlice0Env, bulkInitialSlice1Env, bulkInitialSlice2Env, p, mlir_env])
    (by rw [he3.read (%325)]; simpa only [Pointer.add_zero] using h.pointers.scratch3)
    (by rw [he3.read (%326)]; simpa only [Pointer.add_zero] using h.pointers.cache3)
    (by rw [he3.read (%56)]; exact h.c176)
    (by rw [he3.read (%8)]; exact h.c48)
    (by rw [he3.read (%57)]; exact h.k3)
    (by simpa [first] using hr3) (by simpa [second] using hu3)
  have hf4 := bulkInitialStores_frame mem scratch cache first second 4
  have hr4 := bulkInitialStores_load_first mem p scratch cache first second 4 4
    (by decide) hdlive (by simpa [p] using hsd) (by simpa [p] using hcd)
  have hu4 := bulkInitialStores_load_second mem p scratch cache first second 4 4
    (by decide) hdlive (by simpa [p] using hsd) (by simpa [p] using hcd)
  have hex4 := bulk_initial_slice4_body E4 (bulkInitialStores mem scratch cache first second 4)
    p scratch cache first second (constants[8]!) (constants[9]!)
    (hf4.live hdlive) (hf4.live hs) (hf4.live hclive)
    (by simp [E0, E1, E2, E3, E4, bulkInitialStartEnv, bulkInitialSlice0Env, bulkInitialSlice1Env, bulkInitialSlice2Env, bulkInitialSlice3Env, p, mlir_env])
    (by rw [he4.read (%327)]; simpa only [Pointer.add_zero] using h.pointers.scratch4)
    (by rw [he4.read (%328)]; simpa only [Pointer.add_zero] using h.pointers.cache4)
    (by rw [he4.read (%58)]; exact h.c192)
    (by rw [he4.read (%15)]; exact h.c64)
    (by rw [he4.read (%59)]; exact h.k4)
    (by simpa [first] using hr4) (by simpa [second] using hu4)
  have hf5 := bulkInitialStores_frame mem scratch cache first second 5
  have hr5 := bulkInitialStores_load_first mem p scratch cache first second 5 5
    (by decide) hdlive (by simpa [p] using hsd) (by simpa [p] using hcd)
  have hu5 := bulkInitialStores_load_second mem p scratch cache first second 5 5
    (by decide) hdlive (by simpa [p] using hsd) (by simpa [p] using hcd)
  have hex5 := bulk_initial_slice5_body E5 (bulkInitialStores mem scratch cache first second 5)
    p scratch cache first second (constants[10]!) (constants[11]!)
    (hf5.live hdlive) (hf5.live hs) (hf5.live hclive)
    (by simp [E0, E1, E2, E3, E4, E5, bulkInitialStartEnv, bulkInitialSlice0Env, bulkInitialSlice1Env, bulkInitialSlice2Env, bulkInitialSlice3Env, bulkInitialSlice4Env, p, mlir_env])
    (by rw [he5.read (%329)]; simpa only [Pointer.add_zero] using h.pointers.scratch5)
    (by rw [he5.read (%330)]; simpa only [Pointer.add_zero] using h.pointers.cache5)
    (by rw [he5.read (%60)]; exact h.c208)
    (by rw [he5.read (%17)]; exact h.c80)
    (by rw [he5.read (%61)]; exact h.k5)
    (by simpa [first] using hr5) (by simpa [second] using hu5)
  have hf6 := bulkInitialStores_frame mem scratch cache first second 6
  have hr6 := bulkInitialStores_load_first mem p scratch cache first second 6 6
    (by decide) hdlive (by simpa [p] using hsd) (by simpa [p] using hcd)
  have hu6 := bulkInitialStores_load_second mem p scratch cache first second 6 6
    (by decide) hdlive (by simpa [p] using hsd) (by simpa [p] using hcd)
  have hex6 := bulk_initial_slice6_body E6 (bulkInitialStores mem scratch cache first second 6)
    p scratch cache first second (constants[12]!) (constants[13]!)
    (hf6.live hdlive) (hf6.live hs) (hf6.live hclive)
    (by simp [E0, E1, E2, E3, E4, E5, E6, bulkInitialStartEnv, bulkInitialSlice0Env, bulkInitialSlice1Env, bulkInitialSlice2Env, bulkInitialSlice3Env, bulkInitialSlice4Env, bulkInitialSlice5Env, p, mlir_env])
    (by rw [he6.read (%331)]; simpa only [Pointer.add_zero] using h.pointers.scratch6)
    (by rw [he6.read (%332)]; simpa only [Pointer.add_zero] using h.pointers.cache6)
    (by rw [he6.read (%62)]; exact h.c224)
    (by rw [he6.read (%19)]; exact h.c96)
    (by rw [he6.read (%63)]; exact h.k6)
    (by simpa [first] using hr6) (by simpa [second] using hu6)
  have hf7 := bulkInitialStores_frame mem scratch cache first second 7
  have hr7 := bulkInitialStores_load_first mem p scratch cache first second 7 7
    (by decide) hdlive (by simpa [p] using hsd) (by simpa [p] using hcd)
  have hu7 := bulkInitialStores_load_second mem p scratch cache first second 7 7
    (by decide) hdlive (by simpa [p] using hsd) (by simpa [p] using hcd)
  have hex7 := bulk_initial_slice7_body E7 (bulkInitialStores mem scratch cache first second 7)
    p scratch cache first second (constants[14]!) (constants[15]!)
    (hf7.live hdlive) (hf7.live hs) (hf7.live hclive)
    (by simp [E0, E1, E2, E3, E4, E5, E6, E7, bulkInitialStartEnv, bulkInitialSlice0Env, bulkInitialSlice1Env, bulkInitialSlice2Env, bulkInitialSlice3Env, bulkInitialSlice4Env, bulkInitialSlice5Env, bulkInitialSlice6Env, p, mlir_env])
    (by rw [he7.read (%333)]; simpa only [Pointer.add_zero] using h.pointers.scratch7)
    (by rw [he7.read (%334)]; simpa only [Pointer.add_zero] using h.pointers.cache7)
    (by rw [he7.read (%64)]; exact h.c240)
    (by rw [he7.read (%21)]; exact h.c112)
    (by rw [he7.read (%65)]; exact h.k7)
    (by simpa [first] using hr7) (by simpa [second] using hu7)
  have hcut : program.bb9.body = program.bb9.body.take 3 ++
    (program.bb9.body.drop 3).take 12 ++
    (program.bb9.body.drop 15).take 13 ++
    (program.bb9.body.drop 28).take 13 ++
    (program.bb9.body.drop 41).take 13 ++
    (program.bb9.body.drop 54).take 13 ++
    (program.bb9.body.drop 67).take 13 ++
    (program.bb9.body.drop 80).take 13 ++
    (program.bb9.body.drop 93).take 13 ++
    program.bb9.body.drop 106 := by rfl
  change List.foldlM Instr.run E0 ((program.bb9.body.drop 3).take 12)
    mem =
      .value (E1, bulkInitialStores mem scratch cache first second 1) at hex0
  change List.foldlM Instr.run E1 ((program.bb9.body.drop 15).take 13)
    (bulkInitialStores mem scratch cache first second 1) =
      .value (E2, bulkInitialStores mem scratch cache first second 2) at hex1
  change List.foldlM Instr.run E2 ((program.bb9.body.drop 28).take 13)
    (bulkInitialStores mem scratch cache first second 2) =
      .value (E3, bulkInitialStores mem scratch cache first second 3) at hex2
  change List.foldlM Instr.run E3 ((program.bb9.body.drop 41).take 13)
    (bulkInitialStores mem scratch cache first second 3) =
      .value (E4, bulkInitialStores mem scratch cache first second 4) at hex3
  change List.foldlM Instr.run E4 ((program.bb9.body.drop 54).take 13)
    (bulkInitialStores mem scratch cache first second 4) =
      .value (E5, bulkInitialStores mem scratch cache first second 5) at hex4
  change List.foldlM Instr.run E5 ((program.bb9.body.drop 67).take 13)
    (bulkInitialStores mem scratch cache first second 5) =
      .value (E6, bulkInitialStores mem scratch cache first second 6) at hex5
  change List.foldlM Instr.run E6 ((program.bb9.body.drop 80).take 13)
    (bulkInitialStores mem scratch cache first second 6) =
      .value (E7, bulkInitialStores mem scratch cache first second 7) at hex6
  change List.foldlM Instr.run E7 ((program.bb9.body.drop 93).take 13)
    (bulkInitialStores mem scratch cache first second 7) =
      .value (E8, bulkInitialStores mem scratch cache first second 8) at hex7
  dsimp only [E0, E1, E2, E3, E4, E5, E6, E7, E8] at hex0 hex1 hex2 hex3 hex4 hex5 hex6 hex7
  rw [hcut]
  simp only [List.foldlM_append, EffectM.bind_eq, hstart, LeanMLIR.RIR.PoisonOr.value_bind,
    hex0, hex1, hex2, hex3, hex4, hex5, hex6, hex7]
  simp [program.bb9, List.foldlM_cons, List.foldlM_nil, Instr.run, EffectM.pure_eq,
    mlir_effect, bulkInitialLoadEnv, E0, E1, E2, E3, E4, E5, E6, E7, E8, p, first, second]

def bulkInitialGroupEnv (E : Env program.Γ) : Env program.Γ :=
  E[%450 := E.read (%4), %451 := E.read (%1),
    %452 := E.read (%378), %453 := E.read (%367),
    %454 := E.read (%422), %455 := E.read (%411),
    %456 := E.read (%444), %457 := E.read (%389),
    %458 := E.read (%400), %459 := E.read (%433),
    %460 := E.read (%350), %461 := E.read (%353),
    %462 := E.read (%351), %463 := E.read (%352),
    %464 := E.read (%357), %465 := E.read (%356),
    %466 := E.read (%355), %467 := E.read (%354)]

theorem bulk_initial_group_exit (E : Env program.Γ) (mem : GlobalState) :
    program.bb9.exit.run program.blockParams E mem =
      .value ((bulkInitialGroupEnv E, .inr 11), mem) := by
  simp [program.bb9, Exit.run, Jump.run, bulkInitialGroupEnv,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

theorem bulk_initial_load_run (E : Env program.Γ) (mem : GlobalState)
    (data scratch cache : Pointer) (n : Nat)
    (h : BulkInitialLoadReady E data scratch cache n)
    (hd : SmallRange mem.mem data (128*n+256))
    (hs : SmallRange mem.mem scratch 128) (hc : SmallRange mem.mem cache 640)
    (hsd : scratch.id ≠ data.id) (hcd : cache.id ≠ data.id) :
    let p := data.add (BitVec.ofNat 64 (128*n))
    let first := readBytes mem.mem p 128
    let second := readBytes mem.mem (p.add 128#64) 128
    program.bb9.run program.blockParams E mem =
      .value ((bulkInitialGroupEnv (bulkInitialLoadEnv E data n first second), .inr 11),
        bulkInitialStores mem scratch cache first second 8) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    bulk_initial_load_body E mem data scratch cache n h hd hs hc hsd hcd,
    LeanMLIR.RIR.PoisonOr.value_bind]
  exact bulk_initial_group_exit _ _

end Agave.Ed25519.SHA512.Execution.Avx2
