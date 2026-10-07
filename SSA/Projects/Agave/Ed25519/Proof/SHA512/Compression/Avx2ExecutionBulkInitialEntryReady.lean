import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkEntry

/-! Parity-independent constants consumed by the dual-block initializer. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
set_option maxRecDepth 100000
set_option maxHeartbeats 3500000

/-- Only the constants read by bb9/bb11 and the resulting bb12 invariant.
The allocation pointers have their own invariant; parity registers 84/85 are unused. -/
structure BulkInitialEntryReady (g : Globals) (E : Env program.Γ) : Prop where
  v1 : E.read (%1) = .value 1#64
  v2 : E.read (%2) = .value 0#64
  v3 : E.read (%3) = .value 8#64
  v4 : E.read (%4) = .value 16#64
  v6 : E.read (%6) = .value 32#64
  v8 : E.read (%8) = .value 48#64
  v15 : E.read (%15) = .value 64#64
  v17 : E.read (%17) = .value 80#64
  v19 : E.read (%19) = .value 96#64
  v21 : E.read (%21) = .value 112#64
  v24 : E.read (%24) = .value g.address0
  v35 : E.read (%35) = .value 4#64
  v36 : E.read (%36) = .value 50#64
  v37 : E.read (%37) = .value 46#64
  v38 : E.read (%38) = .value 23#64
  v39 : E.read (%39) = .value 36#64
  v40 : E.read (%40) = .value 30#64
  v41 : E.read (%41) = .value 25#64
  v42 : E.read (%42) = .value 2#64
  v44 : E.read (%44) = .value 15#64
  v47 : E.read (%47) = .value 128#64
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

/-- The single-block entry invariant supplies the same bulk constants. -/
theorem EntryReady.bulk_initial {g : Globals} {E : Env program.Γ} {origin : GlobalState}
    (h : EntryReady g E origin) : BulkInitialEntryReady g E :=
  ⟨h.v1, h.v2, h.v3, h.v4, h.v6, h.v8, h.v15, h.v17,
    h.v19, h.v21, h.v24, h.v35, h.v36, h.v37, h.v38, h.v39,
    h.v40, h.v41, h.v42, h.v44, h.v47, h.v51, h.v52, h.v53,
    h.v54, h.v55, h.v56, h.v57, h.v58, h.v59, h.v60, h.v61,
    h.v62, h.v63, h.v64, h.v65, h.v66, h.v68, h.v69, h.v70,
    h.v71, h.v72, h.v73, h.v74, h.v75, h.v76, h.v77, h.v78⟩

/-- Every input count establishes these constants, independently of its low bit. -/
theorem bulkEntryEnv_bulkInitialReady (g : Globals) (E : Env program.Γ)
    (mem : GlobalState) (count : BitVec 64) :
    BulkInitialEntryReady g (bulkEntryEnv g E mem count) := by
  constructor <;> simp [bulkEntryEnv, entryConstantsEnv, entryConstants0,
    entryConstants1, entryConstants2, mlir_env]

/-- Any frame beginning after the consumed constants preserves bulk readiness. -/
theorem BulkInitialEntryReady.of_frame {g : Globals} {E E' : Env program.Γ}
    {lo hi : Nat} (h : BulkInitialEntryReady g E) (hf : RegFrame lo hi E E')
    (hlo : 79 ≤ lo := by decide) : BulkInitialEntryReady g E' := by
  constructor
  · exact (hf.read (%1) (by left; change 1 < lo; omega)).trans h.v1
  · exact (hf.read (%2) (by left; change 2 < lo; omega)).trans h.v2
  · exact (hf.read (%3) (by left; change 3 < lo; omega)).trans h.v3
  · exact (hf.read (%4) (by left; change 4 < lo; omega)).trans h.v4
  · exact (hf.read (%6) (by left; change 6 < lo; omega)).trans h.v6
  · exact (hf.read (%8) (by left; change 8 < lo; omega)).trans h.v8
  · exact (hf.read (%15) (by left; change 15 < lo; omega)).trans h.v15
  · exact (hf.read (%17) (by left; change 17 < lo; omega)).trans h.v17
  · exact (hf.read (%19) (by left; change 19 < lo; omega)).trans h.v19
  · exact (hf.read (%21) (by left; change 21 < lo; omega)).trans h.v21
  · exact (hf.read (%24) (by left; change 24 < lo; omega)).trans h.v24
  · exact (hf.read (%35) (by left; change 35 < lo; omega)).trans h.v35
  · exact (hf.read (%36) (by left; change 36 < lo; omega)).trans h.v36
  · exact (hf.read (%37) (by left; change 37 < lo; omega)).trans h.v37
  · exact (hf.read (%38) (by left; change 38 < lo; omega)).trans h.v38
  · exact (hf.read (%39) (by left; change 39 < lo; omega)).trans h.v39
  · exact (hf.read (%40) (by left; change 40 < lo; omega)).trans h.v40
  · exact (hf.read (%41) (by left; change 41 < lo; omega)).trans h.v41
  · exact (hf.read (%42) (by left; change 42 < lo; omega)).trans h.v42
  · exact (hf.read (%44) (by left; change 44 < lo; omega)).trans h.v44
  · exact (hf.read (%47) (by left; change 47 < lo; omega)).trans h.v47
  · exact (hf.read (%51) (by left; change 51 < lo; omega)).trans h.v51
  · exact (hf.read (%52) (by left; change 52 < lo; omega)).trans h.v52
  · exact (hf.read (%53) (by left; change 53 < lo; omega)).trans h.v53
  · exact (hf.read (%54) (by left; change 54 < lo; omega)).trans h.v54
  · exact (hf.read (%55) (by left; change 55 < lo; omega)).trans h.v55
  · exact (hf.read (%56) (by left; change 56 < lo; omega)).trans h.v56
  · exact (hf.read (%57) (by left; change 57 < lo; omega)).trans h.v57
  · exact (hf.read (%58) (by left; change 58 < lo; omega)).trans h.v58
  · exact (hf.read (%59) (by left; change 59 < lo; omega)).trans h.v59
  · exact (hf.read (%60) (by left; change 60 < lo; omega)).trans h.v60
  · exact (hf.read (%61) (by left; change 61 < lo; omega)).trans h.v61
  · exact (hf.read (%62) (by left; change 62 < lo; omega)).trans h.v62
  · exact (hf.read (%63) (by left; change 63 < lo; omega)).trans h.v63
  · exact (hf.read (%64) (by left; change 64 < lo; omega)).trans h.v64
  · exact (hf.read (%65) (by left; change 65 < lo; omega)).trans h.v65
  · exact (hf.read (%66) (by left; change 66 < lo; omega)).trans h.v66
  · exact (hf.read (%68) (by left; change 68 < lo; omega)).trans h.v68
  · exact (hf.read (%69) (by left; change 69 < lo; omega)).trans h.v69
  · exact (hf.read (%70) (by left; change 70 < lo; omega)).trans h.v70
  · exact (hf.read (%71) (by left; change 71 < lo; omega)).trans h.v71
  · exact (hf.read (%72) (by left; change 72 < lo; omega)).trans h.v72
  · exact (hf.read (%73) (by left; change 73 < lo; omega)).trans h.v73
  · exact (hf.read (%74) (by left; change 74 < lo; omega)).trans h.v74
  · exact (hf.read (%75) (by left; change 75 < lo; omega)).trans h.v75
  · exact (hf.read (%76) (by left; change 76 < lo; omega)).trans h.v76
  · exact (hf.read (%77) (by left; change 77 < lo; omega)).trans h.v77
  · exact (hf.read (%78) (by left; change 78 < lo; omega)).trans h.v78

end Agave.Ed25519.SHA512.Execution.Avx2
