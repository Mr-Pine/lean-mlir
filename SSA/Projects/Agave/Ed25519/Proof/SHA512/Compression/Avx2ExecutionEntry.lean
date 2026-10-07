import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionCompression

/-! Exact imported bb0 entry for a single input block. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def entryConstants0 (g : Globals) (E : Env program.Γ) : Env program.Γ :=
  E[%0 := .value 1#32,
    %1 := .value 1#64,
    %2 := .value 0#64,
    %3 := .value 8#64,
    %4 := .value 16#64,
    %5 := .value 24#64,
    %6 := .value 32#64,
    %7 := .value 40#64,
    %8 := .value 48#64,
    %9 := .value 56#64,
    %10 := Ty.poisoned (.vec 16 8),
    %11 := Ty.wrap #v[4794697086780616226#64, 8158064640168781261#64],
    %12 := Ty.wrap #v[13096744586834688815#64, 16840607885511220156#64],
    %13 := Ty.wrap #v[4131703408338449720#64, 6480981068601479193#64],
    %14 := Ty.wrap #v[10538285296894168987#64, 12329834152419229976#64],
    %15 := .value 64#64,
    %16 := Ty.wrap #v[15566598209576043074#64, 1334009975649890238#64],
    %17 := .value 80#64,
    %18 := Ty.wrap #v[2608012711638119052#64, 6128411473006802146#64],
    %19 := .value 96#64,
    %20 := Ty.wrap #v[8268148722764581231#64, 9286055187155687089#64],
    %21 := .value 112#64,
    %22 := Ty.wrap #v[11230858885718282805#64, 13951009754708518548#64],
    %23 := .value 0#32,
    %24 := .value g.address0]

def entryConstants1 (_g : Globals) (E : Env program.Γ) : Env program.Γ :=
  E[%25 := Ty.wrap #v[1#64, 1#64],
    %26 := Ty.wrap #v[7#64, 7#64],
    %27 := Ty.wrap #v[56#64, 56#64],
    %28 := Ty.wrap #v[8#64, 8#64],
    %29 := Ty.wrap #v[63#64, 63#64],
    %30 := Ty.wrap #v[6#64, 6#64],
    %31 := Ty.wrap #v[3#64, 3#64],
    %32 := Ty.wrap #v[19#64, 19#64],
    %33 := Ty.wrap #v[45#64, 45#64],
    %34 := Ty.wrap #v[61#64, 61#64],
    %35 := .value 4#64,
    %36 := .value 50#64,
    %37 := .value 46#64,
    %38 := .value 23#64,
    %39 := .value 36#64,
    %40 := .value 30#64,
    %41 := .value 25#64,
    %42 := .value 2#64,
    %43 := .value 4#32,
    %44 := .value 15#64,
    %45 := Ty.poisoned (.vec 4 64),
    %46 := .value 3#64,
    %47 := .value 128#64,
    %48 := .value 0#8,
    %49 := .value 512#64,
    %50 := Ty.poisoned (.vec 32 8)]

def entryConstants2 (_g : Globals) (E : Env program.Γ) : Env program.Γ :=
  E[%51 := Ty.wrap #v[4794697086780616226#64, 8158064640168781261#64, 4794697086780616226#64, 8158064640168781261#64],
    %52 := .value 144#64,
    %53 := Ty.wrap #v[13096744586834688815#64, 16840607885511220156#64, 13096744586834688815#64, 16840607885511220156#64],
    %54 := .value 160#64,
    %55 := Ty.wrap #v[4131703408338449720#64, 6480981068601479193#64, 4131703408338449720#64, 6480981068601479193#64],
    %56 := .value 176#64,
    %57 := Ty.wrap #v[10538285296894168987#64, 12329834152419229976#64, 10538285296894168987#64, 12329834152419229976#64],
    %58 := .value 192#64,
    %59 := Ty.wrap #v[15566598209576043074#64, 1334009975649890238#64, 15566598209576043074#64, 1334009975649890238#64],
    %60 := .value 208#64,
    %61 := Ty.wrap #v[2608012711638119052#64, 6128411473006802146#64, 2608012711638119052#64, 6128411473006802146#64],
    %62 := .value 224#64,
    %63 := Ty.wrap #v[8268148722764581231#64, 9286055187155687089#64, 8268148722764581231#64, 9286055187155687089#64],
    %64 := .value 240#64,
    %65 := Ty.wrap #v[11230858885718282805#64, 13951009754708518548#64, 11230858885718282805#64, 13951009754708518548#64],
    %66 := .value 7#64,
    %67 := Ty.poisoned (.vec 2 64),
    %68 := Ty.wrap #v[1#64, 1#64, 1#64, 1#64],
    %69 := Ty.wrap #v[7#64, 7#64, 7#64, 7#64],
    %70 := Ty.wrap #v[56#64, 56#64, 56#64, 56#64],
    %71 := Ty.wrap #v[8#64, 8#64, 8#64, 8#64],
    %72 := Ty.wrap #v[63#64, 63#64, 63#64, 63#64],
    %73 := Ty.wrap #v[6#64, 6#64, 6#64, 6#64],
    %74 := Ty.wrap #v[3#64, 3#64, 3#64, 3#64],
    %75 := Ty.wrap #v[19#64, 19#64, 19#64, 19#64],
    %76 := Ty.wrap #v[45#64, 45#64, 45#64, 45#64],
    %77 := Ty.wrap #v[61#64, 61#64, 61#64, 61#64],
    %78 := .value 5#64,
    %79 := .value 640#64,
    %80 := .value 18446744073709551615#64]

def entryConstantsEnv (g : Globals) (E : Env program.Γ) : Env program.Γ :=
  entryConstants2 g (entryConstants1 g (entryConstants0 g E))

def entryState (mem : GlobalState) : GlobalState :=
  ((mem.alloca 128).alloca 640).alloca 128

def entryEnv (g : Globals) (E : Env program.Γ) (mem : GlobalState) : Env program.Γ :=
  (entryConstantsEnv g E)[%81 := .value mem.allocaPtr,
    %82 := .value (mem.alloca 128).allocaPtr,
    %83 := .value ((mem.alloca 128).alloca 640).allocaPtr,
    %84 := .value 1#64, %85 := .value 0#1]

structure EntryReady (g : Globals) (E : Env program.Γ) (mem : GlobalState) : Prop where
  v0 : E.read (%0) = .value 1#32
  v1 : E.read (%1) = .value 1#64
  v2 : E.read (%2) = .value 0#64
  v3 : E.read (%3) = .value 8#64
  v4 : E.read (%4) = .value 16#64
  v5 : E.read (%5) = .value 24#64
  v6 : E.read (%6) = .value 32#64
  v7 : E.read (%7) = .value 40#64
  v8 : E.read (%8) = .value 48#64
  v9 : E.read (%9) = .value 56#64
  v10 : E.read (%10) = Ty.poisoned (.vec 16 8)
  v11 : E.read (%11) = Ty.wrap #v[4794697086780616226#64, 8158064640168781261#64]
  v12 : E.read (%12) = Ty.wrap #v[13096744586834688815#64, 16840607885511220156#64]
  v13 : E.read (%13) = Ty.wrap #v[4131703408338449720#64, 6480981068601479193#64]
  v14 : E.read (%14) = Ty.wrap #v[10538285296894168987#64, 12329834152419229976#64]
  v15 : E.read (%15) = .value 64#64
  v16 : E.read (%16) = Ty.wrap #v[15566598209576043074#64, 1334009975649890238#64]
  v17 : E.read (%17) = .value 80#64
  v18 : E.read (%18) = Ty.wrap #v[2608012711638119052#64, 6128411473006802146#64]
  v19 : E.read (%19) = .value 96#64
  v20 : E.read (%20) = Ty.wrap #v[8268148722764581231#64, 9286055187155687089#64]
  v21 : E.read (%21) = .value 112#64
  v22 : E.read (%22) = Ty.wrap #v[11230858885718282805#64, 13951009754708518548#64]
  v23 : E.read (%23) = .value 0#32
  v24 : E.read (%24) = .value g.address0
  v25 : E.read (%25) = Ty.wrap #v[1#64, 1#64]
  v26 : E.read (%26) = Ty.wrap #v[7#64, 7#64]
  v27 : E.read (%27) = Ty.wrap #v[56#64, 56#64]
  v28 : E.read (%28) = Ty.wrap #v[8#64, 8#64]
  v29 : E.read (%29) = Ty.wrap #v[63#64, 63#64]
  v30 : E.read (%30) = Ty.wrap #v[6#64, 6#64]
  v31 : E.read (%31) = Ty.wrap #v[3#64, 3#64]
  v32 : E.read (%32) = Ty.wrap #v[19#64, 19#64]
  v33 : E.read (%33) = Ty.wrap #v[45#64, 45#64]
  v34 : E.read (%34) = Ty.wrap #v[61#64, 61#64]
  v35 : E.read (%35) = .value 4#64
  v36 : E.read (%36) = .value 50#64
  v37 : E.read (%37) = .value 46#64
  v38 : E.read (%38) = .value 23#64
  v39 : E.read (%39) = .value 36#64
  v40 : E.read (%40) = .value 30#64
  v41 : E.read (%41) = .value 25#64
  v42 : E.read (%42) = .value 2#64
  v43 : E.read (%43) = .value 4#32
  v44 : E.read (%44) = .value 15#64
  v45 : E.read (%45) = Ty.poisoned (.vec 4 64)
  v46 : E.read (%46) = .value 3#64
  v47 : E.read (%47) = .value 128#64
  v48 : E.read (%48) = .value 0#8
  v49 : E.read (%49) = .value 512#64
  v50 : E.read (%50) = Ty.poisoned (.vec 32 8)
  v51 : E.read (%51) = Ty.wrap #v[4794697086780616226#64, 8158064640168781261#64, 4794697086780616226#64, 8158064640168781261#64]
  v52 : E.read (%52) = .value 144#64
  v53 : E.read (%53) = Ty.wrap #v[13096744586834688815#64, 16840607885511220156#64, 13096744586834688815#64, 16840607885511220156#64]
  v54 : E.read (%54) = .value 160#64
  v55 : E.read (%55) = Ty.wrap #v[4131703408338449720#64, 6480981068601479193#64, 4131703408338449720#64, 6480981068601479193#64]
  v56 : E.read (%56) = .value 176#64
  v57 : E.read (%57) = Ty.wrap #v[10538285296894168987#64, 12329834152419229976#64, 10538285296894168987#64, 12329834152419229976#64]
  v58 : E.read (%58) = .value 192#64
  v59 : E.read (%59) = Ty.wrap #v[15566598209576043074#64, 1334009975649890238#64, 15566598209576043074#64, 1334009975649890238#64]
  v60 : E.read (%60) = .value 208#64
  v61 : E.read (%61) = Ty.wrap #v[2608012711638119052#64, 6128411473006802146#64, 2608012711638119052#64, 6128411473006802146#64]
  v62 : E.read (%62) = .value 224#64
  v63 : E.read (%63) = Ty.wrap #v[8268148722764581231#64, 9286055187155687089#64, 8268148722764581231#64, 9286055187155687089#64]
  v64 : E.read (%64) = .value 240#64
  v65 : E.read (%65) = Ty.wrap #v[11230858885718282805#64, 13951009754708518548#64, 11230858885718282805#64, 13951009754708518548#64]
  v66 : E.read (%66) = .value 7#64
  v67 : E.read (%67) = Ty.poisoned (.vec 2 64)
  v68 : E.read (%68) = Ty.wrap #v[1#64, 1#64, 1#64, 1#64]
  v69 : E.read (%69) = Ty.wrap #v[7#64, 7#64, 7#64, 7#64]
  v70 : E.read (%70) = Ty.wrap #v[56#64, 56#64, 56#64, 56#64]
  v71 : E.read (%71) = Ty.wrap #v[8#64, 8#64, 8#64, 8#64]
  v72 : E.read (%72) = Ty.wrap #v[63#64, 63#64, 63#64, 63#64]
  v73 : E.read (%73) = Ty.wrap #v[6#64, 6#64, 6#64, 6#64]
  v74 : E.read (%74) = Ty.wrap #v[3#64, 3#64, 3#64, 3#64]
  v75 : E.read (%75) = Ty.wrap #v[19#64, 19#64, 19#64, 19#64]
  v76 : E.read (%76) = Ty.wrap #v[45#64, 45#64, 45#64, 45#64]
  v77 : E.read (%77) = Ty.wrap #v[61#64, 61#64, 61#64, 61#64]
  v78 : E.read (%78) = .value 5#64
  v79 : E.read (%79) = .value 640#64
  v80 : E.read (%80) = .value 18446744073709551615#64
  scratch : E.read (%81) = .value mem.allocaPtr
  cache : E.read (%82) = .value (mem.alloca 128).allocaPtr
  buffer : E.read (%83) = .value ((mem.alloca 128).alloca 640).allocaPtr
  parity : E.read (%84) = .value 1#64
  branch : E.read (%85) = .value 0#1

private theorem entry_splat2 (x : BitVec 64) :
    Vector.replicate 2 (PoisonOr.value x) = Ty.wrap (t := .vec 2 64) #v[x,x] := by
  ext i hi
  interval_cases i <;> simp [Ty.wrap_vec]

private theorem entry_splat4 (x : BitVec 64) :
    Vector.replicate 4 (PoisonOr.value x) = Ty.wrap (t := .vec 4 64) #v[x,x,x,x] := by
  ext i hi
  interval_cases i <;> simp [Ty.wrap_vec]

theorem entry_constants0 (g : Globals) (E : Env program.Γ) (mem : GlobalState) :
    List.foldlM Instr.run E ((program.bb0 g).body.take 25) mem =
      .value (entryConstants0 g E, mem) := by
  simp [program.bb0, entryConstants0, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Ty.wrap,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

theorem entry_constants1 (g : Globals) (E : Env program.Γ) (mem : GlobalState) :
    List.foldlM Instr.run E (((program.bb0 g).body.drop 25).take 26) mem =
      .value (entryConstants1 g E, mem) := by
  simp [program.bb0, entryConstants1, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Ty.wrap, entry_splat2,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

theorem entry_constants2 (g : Globals) (E : Env program.Γ) (mem : GlobalState) :
    List.foldlM Instr.run E (((program.bb0 g).body.drop 51).take 30) mem =
      .value (entryConstants2 g E, mem) := by
  simp [program.bb0, entryConstants2, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Ty.wrap, entry_splat4,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

theorem entry_constants (g : Globals) (E : Env program.Γ) (mem : GlobalState) :
    List.foldlM Instr.run E ((program.bb0 g).body.take 81) mem =
      .value (entryConstantsEnv g E, mem) := by
  have hcut : (program.bb0 g).body.take 81 =
      (program.bb0 g).body.take 25 ++ ((program.bb0 g).body.drop 25).take 26 ++
        ((program.bb0 g).body.drop 51).take 30 := by rfl
  rw [hcut, List.foldlM_append, List.foldlM_append]
  simp only [EffectM.bind_eq, entry_constants0, PoisonOr.value_bind,
    entry_constants1, entry_constants2, entryConstantsEnv]

private theorem modifyGet_apply (f : GlobalState → α × GlobalState) (s : GlobalState) :
    (modifyGet f : EffectM α) s = .value (f s) := rfl

private theorem entry_allocations_raw (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (hcount : E.read (%arg2) = .value 1#64)
    (h1 : E.read (%1) = .value 1#64) (h2 : E.read (%2) = .value 0#64) :
    List.foldlM Instr.run E ((program.bb0 g).body.drop 81) mem =
      .value (E[%81 := .value mem.allocaPtr,
        %82 := .value (mem.alloca 128).allocaPtr,
        %83 := .value ((mem.alloca 128).alloca 640).allocaPtr,
        %84 := .value 1#64, %85 := .value 0#1], entryState mem) := by
  change E.args 2 = .value 1#64 at hcount
  simp [program.bb0, entryState, List.foldlM_cons, List.foldlM_nil,
    Instr.run, modifyGet_apply, Operation.and, Operation.icmp,
    BinOp.compute, EffectM.bind_eq, hcount, h1, h2, mlir_env, mlir_effect]

private theorem entry_allocations (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (hcount : E.read (%arg2) = .value 1#64) :
    List.foldlM Instr.run (entryConstantsEnv g E) ((program.bb0 g).body.drop 81) mem =
      .value (entryEnv g E mem, entryState mem) := by
  apply entry_allocations_raw
  · simpa [entryConstantsEnv, entryConstants0, entryConstants1, entryConstants2, mlir_env] using hcount
  · simp [entryConstantsEnv, entryConstants0, entryConstants1, entryConstants2, mlir_env]
  · simp [entryConstantsEnv, entryConstants0, entryConstants1, entryConstants2, mlir_env]

theorem entry_body (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (hcount : E.read (%arg2) = .value 1#64) :
    List.foldlM Instr.run E (program.bb0 g).body mem =
      .value (entryEnv g E mem, entryState mem) := by
  have hcut : (program.bb0 g).body =
      (program.bb0 g).body.take 81 ++ (program.bb0 g).body.drop 81 := by rfl
  rw [hcut, List.foldlM_append]
  simp only [EffectM.bind_eq, entry_constants, PoisonOr.value_bind]
  exact entry_allocations g E mem hcount

@[simp] theorem entry_params2 : program.blockParams 2 = .nil := rfl

theorem entry_block (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (hcount : E.read (%arg2) = .value 1#64) :
    (program.bb0 g).run program.blockParams E mem =
      .value ((entryEnv g E mem, .inr 2), entryState mem) := by
  simp only [BasicBlock.run, EffectM.bind_eq, entry_body g E mem hcount,
    PoisonOr.value_bind]
  simp [program.bb0, entryEnv, Exit.run, Jump.run, Regs.read_nil,
    Env.writeMany_nil, EffectM.pure_eq, mlir_env, mlir_effect]

theorem entry_ready (g : Globals) (E : Env program.Γ) (mem : GlobalState) :
    EntryReady g (entryEnv g E mem) mem := by
  constructor <;> simp [entryEnv, entryConstantsEnv, entryConstants0,
    entryConstants1, entryConstants2, mlir_env]

theorem entry_frame (g : Globals) (E : Env program.Γ) (mem : GlobalState) :
    RegFrame 0 85 E (entryEnv g E mem) := by
  unfold entryEnv entryConstantsEnv entryConstants2 entryConstants1 entryConstants0
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

end Agave.Ed25519.SHA512.Execution.Avx2
