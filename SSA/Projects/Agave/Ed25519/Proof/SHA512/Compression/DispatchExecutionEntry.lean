import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.DispatchProgram
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Globals

/-! Exact execution of the original sha2 dispatcher entry.  Even the warm
AVX2 branch evaluates the emitted K64 address computations before the cache
load. The range premises account for every flagged GEP and the cache load;
no compression result or CPU-feature accuracy is assumed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Agave.Ed25519.SHA512.Execution.Dispatch
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.SHA512Finalization

def dispatchChunk0 (E : Env program.Γ) (g : Globals) (cache : BitVec 8) : Env program.Γ :=
  E[%0 := .value g.address0,
    %1 := .value 7#64,
    %2 := .value 0#64,
    %3 := .value 8#64,
    %4 := .value 16#64,
    %5 := .value 24#64,
    %6 := .value 32#64,
    %7 := .value 40#64,
    %8 := .value 48#64,
    %9 := .value 56#64,
    %10 := .value 128#64,
    %11 := .value 64#64,
    %12 := .value 72#64,
    %13 := .value 80#64,
    %14 := .value 88#64,
    %15 := .value 96#64,
    %16 := .value 104#64,
    %17 := .value 112#64,
    %18 := .value 120#64,
    %19 := .value 50#64,
    %20 := .value 46#64,
    %21 := .value 23#64,
    %22 := .value (-1 : BitVec 64),
    %23 := .value g.address1,
    %24 := .value 36#64,
    %25 := .value 30#64,
    %26 := .value 25#64,
    %27 := .value (g.address1.add 8#64),
    %28 := .value (g.address1.add 16#64),
    %29 := .value (g.address1.add 24#64),
    %30 := .value (g.address1.add 32#64),
    %31 := .value (g.address1.add 40#64),
    %32 := .value (g.address1.add 48#64),
    %33 := .value (g.address1.add 56#64),
    %34 := .value (g.address1.add 64#64),
    %35 := .value (g.address1.add 72#64),
    %36 := .value (g.address1.add 80#64),
    %37 := .value (g.address1.add 88#64),
    %38 := .value (g.address1.add 96#64),
    %39 := .value (g.address1.add 104#64),
    %40 := .value (g.address1.add 112#64),
    %41 := .value (g.address1.add 120#64),
    %42 := .value 63#64,
    %43 := .value 45#64,
    %44 := .value 3#64,
    %45 := .value 6#64,
    %46 := .value (g.address1.add 128#64)]

def dispatchChunk1 (E : Env program.Γ) (g : Globals) (cache : BitVec 8) : Env program.Γ :=
  E[%47 := .value 136#64,
    %48 := .value (g.address1.add 136#64),
    %49 := .value 144#64,
    %50 := .value (g.address1.add 144#64),
    %51 := .value 152#64,
    %52 := .value (g.address1.add 152#64),
    %53 := .value 160#64,
    %54 := .value (g.address1.add 160#64),
    %55 := .value 168#64,
    %56 := .value (g.address1.add 168#64),
    %57 := .value 176#64,
    %58 := .value (g.address1.add 176#64),
    %59 := .value 184#64,
    %60 := .value (g.address1.add 184#64),
    %61 := .value 192#64,
    %62 := .value (g.address1.add 192#64),
    %63 := .value 200#64,
    %64 := .value (g.address1.add 200#64),
    %65 := .value 208#64,
    %66 := .value (g.address1.add 208#64),
    %67 := .value 216#64,
    %68 := .value (g.address1.add 216#64),
    %69 := .value 224#64,
    %70 := .value (g.address1.add 224#64),
    %71 := .value 232#64,
    %72 := .value (g.address1.add 232#64),
    %73 := .value 240#64,
    %74 := .value (g.address1.add 240#64),
    %75 := .value 248#64,
    %76 := .value (g.address1.add 248#64),
    %77 := .value 256#64,
    %78 := .value (g.address1.add 256#64)]

def dispatchChunk2 (E : Env program.Γ) (g : Globals) (cache : BitVec 8) : Env program.Γ :=
  E[%79 := .value 264#64,
    %80 := .value (g.address1.add 264#64),
    %81 := .value 272#64,
    %82 := .value (g.address1.add 272#64),
    %83 := .value 280#64,
    %84 := .value (g.address1.add 280#64),
    %85 := .value 288#64,
    %86 := .value (g.address1.add 288#64),
    %87 := .value 296#64,
    %88 := .value (g.address1.add 296#64),
    %89 := .value 304#64,
    %90 := .value (g.address1.add 304#64),
    %91 := .value 312#64,
    %92 := .value (g.address1.add 312#64),
    %93 := .value 320#64,
    %94 := .value (g.address1.add 320#64),
    %95 := .value 328#64,
    %96 := .value (g.address1.add 328#64),
    %97 := .value 336#64,
    %98 := .value (g.address1.add 336#64),
    %99 := .value 344#64,
    %100 := .value (g.address1.add 344#64),
    %101 := .value 352#64,
    %102 := .value (g.address1.add 352#64),
    %103 := .value 360#64,
    %104 := .value (g.address1.add 360#64),
    %105 := .value 368#64,
    %106 := .value (g.address1.add 368#64),
    %107 := .value 376#64,
    %108 := .value (g.address1.add 376#64),
    %109 := .value 384#64,
    %110 := .value (g.address1.add 384#64)]

def dispatchChunk3 (E : Env program.Γ) (g : Globals) (cache : BitVec 8) : Env program.Γ :=
  E[%111 := .value 392#64,
    %112 := .value (g.address1.add 392#64),
    %113 := .value 400#64,
    %114 := .value (g.address1.add 400#64),
    %115 := .value 408#64,
    %116 := .value (g.address1.add 408#64),
    %117 := .value 416#64,
    %118 := .value (g.address1.add 416#64),
    %119 := .value 424#64,
    %120 := .value (g.address1.add 424#64),
    %121 := .value 432#64,
    %122 := .value (g.address1.add 432#64),
    %123 := .value 440#64,
    %124 := .value (g.address1.add 440#64),
    %125 := .value 448#64,
    %126 := .value (g.address1.add 448#64),
    %127 := .value 456#64,
    %128 := .value (g.address1.add 456#64),
    %129 := .value 464#64,
    %130 := .value (g.address1.add 464#64),
    %131 := .value 472#64,
    %132 := .value (g.address1.add 472#64),
    %133 := .value 480#64,
    %134 := .value (g.address1.add 480#64),
    %135 := .value 488#64,
    %136 := .value (g.address1.add 488#64),
    %137 := .value 496#64,
    %138 := .value (g.address1.add 496#64),
    %139 := .value 504#64,
    %140 := .value (g.address1.add 504#64),
    %141 := .value 512#64,
    %142 := .value (g.address1.add 512#64)]

def dispatchChunk4 (E : Env program.Γ) (g : Globals) (cache : BitVec 8) : Env program.Γ :=
  E[%143 := .value 520#64,
    %144 := .value (g.address1.add 520#64),
    %145 := .value 528#64,
    %146 := .value (g.address1.add 528#64),
    %147 := .value 536#64,
    %148 := .value (g.address1.add 536#64),
    %149 := .value 544#64,
    %150 := .value (g.address1.add 544#64),
    %151 := .value 552#64,
    %152 := .value (g.address1.add 552#64),
    %153 := .value 560#64,
    %154 := .value (g.address1.add 560#64),
    %155 := .value 568#64,
    %156 := .value (g.address1.add 568#64),
    %157 := .value 576#64,
    %158 := .value (g.address1.add 576#64),
    %159 := .value 584#64,
    %160 := .value (g.address1.add 584#64),
    %161 := .value 592#64,
    %162 := .value (g.address1.add 592#64),
    %163 := .value 600#64,
    %164 := .value (g.address1.add 600#64),
    %165 := .value 608#64,
    %166 := .value (g.address1.add 608#64),
    %167 := .value 616#64,
    %168 := .value (g.address1.add 616#64),
    %169 := .value 624#64,
    %170 := .value (g.address1.add 624#64),
    %171 := .value 632#64,
    %172 := .value (g.address1.add 632#64)]

def dispatchChunk5 (E : Env program.Γ) (g : Globals) (cache : BitVec 8) : Env program.Γ :=
  E[%173 := .value cache]

/-- Complete register effects of the imported bb0, in source order.
Named chunks keep kernel checking bounded while preserving every instruction. -/
def dispatchEntryEnv (E : Env program.Γ) (g : Globals) (cache : BitVec 8) : Env program.Γ :=
  (dispatchChunk5 (dispatchChunk4 (dispatchChunk3 (dispatchChunk2 (dispatchChunk1 (dispatchChunk0 E g cache) g cache) g cache) g cache) g cache) g cache)

/-- The emitted switch: cold sentinel, warm AVX2, or scalar default. -/
def dispatchTarget (cache : BitVec 8) : Fin 8 :=
  if cache = 255 then 1 else if cache = 1 then 6 else 2

private theorem dispatch_chunk0 (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (cache : BitVec 8)
    (hk : SmallRange state.mem g.address1 640)
    (hc : SmallRange state.mem g.address0 1)
    (hr : state.mem.readAt g.address0 8 = cache)
    : List.foldlM Instr.run E (((program.bb0 g).body.drop 0).take 47) state =
      .value (dispatchChunk0 E g cache, state) := by
  have hg8 := hk.gep (k := 8) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (8 : Int)] = .value (g.address1.add 8#64) at hg8
  have hg16 := hk.gep (k := 16) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (16 : Int)] = .value (g.address1.add 16#64) at hg16
  have hg24 := hk.gep (k := 24) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (24 : Int)] = .value (g.address1.add 24#64) at hg24
  have hg32 := hk.gep (k := 32) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (32 : Int)] = .value (g.address1.add 32#64) at hg32
  have hg40 := hk.gep (k := 40) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (40 : Int)] = .value (g.address1.add 40#64) at hg40
  have hg48 := hk.gep (k := 48) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (48 : Int)] = .value (g.address1.add 48#64) at hg48
  have hg56 := hk.gep (k := 56) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (56 : Int)] = .value (g.address1.add 56#64) at hg56
  have hg64 := hk.gep (k := 64) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (64 : Int)] = .value (g.address1.add 64#64) at hg64
  have hg72 := hk.gep (k := 72) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (72 : Int)] = .value (g.address1.add 72#64) at hg72
  have hg80 := hk.gep (k := 80) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (80 : Int)] = .value (g.address1.add 80#64) at hg80
  have hg88 := hk.gep (k := 88) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (88 : Int)] = .value (g.address1.add 88#64) at hg88
  have hg96 := hk.gep (k := 96) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (96 : Int)] = .value (g.address1.add 96#64) at hg96
  have hg104 := hk.gep (k := 104) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (104 : Int)] = .value (g.address1.add 104#64) at hg104
  have hg112 := hk.gep (k := 112) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (112 : Int)] = .value (g.address1.add 112#64) at hg112
  have hg120 := hk.gep (k := 120) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (120 : Int)] = .value (g.address1.add 120#64) at hg120
  have hg128 := hk.gep (k := 128) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (128 : Int)] = .value (g.address1.add 128#64) at hg128
  simp (config := { maxSteps := 300000 }) [program.bb0, List.foldlM_cons,
    List.foldlM_nil, Instr.run, dispatchChunk0, GepIndex.inboundsOffset, Ty.wrap,
    Operation.load, hg8, hg16, hg24, hg32, hg40, hg48, hg56, hg64, hg72, hg80, hg88, hg96, hg104, hg112, hg120, hg128,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

private theorem dispatch_chunk1 (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (cache : BitVec 8)
    (hk : SmallRange state.mem g.address1 640)
    (hc : SmallRange state.mem g.address0 1)
    (hr : state.mem.readAt g.address0 8 = cache)
    (h23 : E.read (%23) = .value g.address1)
    : List.foldlM Instr.run E (((program.bb0 g).body.drop 47).take 32) state =
      .value (dispatchChunk1 E g cache, state) := by
  have hg136 := hk.gep (k := 136) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (136 : Int)] = .value (g.address1.add 136#64) at hg136
  have hg144 := hk.gep (k := 144) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (144 : Int)] = .value (g.address1.add 144#64) at hg144
  have hg152 := hk.gep (k := 152) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (152 : Int)] = .value (g.address1.add 152#64) at hg152
  have hg160 := hk.gep (k := 160) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (160 : Int)] = .value (g.address1.add 160#64) at hg160
  have hg168 := hk.gep (k := 168) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (168 : Int)] = .value (g.address1.add 168#64) at hg168
  have hg176 := hk.gep (k := 176) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (176 : Int)] = .value (g.address1.add 176#64) at hg176
  have hg184 := hk.gep (k := 184) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (184 : Int)] = .value (g.address1.add 184#64) at hg184
  have hg192 := hk.gep (k := 192) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (192 : Int)] = .value (g.address1.add 192#64) at hg192
  have hg200 := hk.gep (k := 200) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (200 : Int)] = .value (g.address1.add 200#64) at hg200
  have hg208 := hk.gep (k := 208) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (208 : Int)] = .value (g.address1.add 208#64) at hg208
  have hg216 := hk.gep (k := 216) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (216 : Int)] = .value (g.address1.add 216#64) at hg216
  have hg224 := hk.gep (k := 224) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (224 : Int)] = .value (g.address1.add 224#64) at hg224
  have hg232 := hk.gep (k := 232) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (232 : Int)] = .value (g.address1.add 232#64) at hg232
  have hg240 := hk.gep (k := 240) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (240 : Int)] = .value (g.address1.add 240#64) at hg240
  have hg248 := hk.gep (k := 248) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (248 : Int)] = .value (g.address1.add 248#64) at hg248
  have hg256 := hk.gep (k := 256) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (256 : Int)] = .value (g.address1.add 256#64) at hg256
  simp (config := { maxSteps := 300000 }) [program.bb0, List.foldlM_cons,
    List.foldlM_nil, Instr.run, dispatchChunk1, GepIndex.inboundsOffset, Ty.wrap,
    Operation.load, hg136, hg144, hg152, hg160, hg168, hg176, hg184, hg192, hg200, hg208, hg216, hg224, hg232, hg240, hg248, hg256, h23,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

private theorem dispatch_chunk2 (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (cache : BitVec 8)
    (hk : SmallRange state.mem g.address1 640)
    (hc : SmallRange state.mem g.address0 1)
    (hr : state.mem.readAt g.address0 8 = cache)
    (h23 : E.read (%23) = .value g.address1)
    : List.foldlM Instr.run E (((program.bb0 g).body.drop 79).take 32) state =
      .value (dispatchChunk2 E g cache, state) := by
  have hg264 := hk.gep (k := 264) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (264 : Int)] = .value (g.address1.add 264#64) at hg264
  have hg272 := hk.gep (k := 272) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (272 : Int)] = .value (g.address1.add 272#64) at hg272
  have hg280 := hk.gep (k := 280) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (280 : Int)] = .value (g.address1.add 280#64) at hg280
  have hg288 := hk.gep (k := 288) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (288 : Int)] = .value (g.address1.add 288#64) at hg288
  have hg296 := hk.gep (k := 296) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (296 : Int)] = .value (g.address1.add 296#64) at hg296
  have hg304 := hk.gep (k := 304) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (304 : Int)] = .value (g.address1.add 304#64) at hg304
  have hg312 := hk.gep (k := 312) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (312 : Int)] = .value (g.address1.add 312#64) at hg312
  have hg320 := hk.gep (k := 320) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (320 : Int)] = .value (g.address1.add 320#64) at hg320
  have hg328 := hk.gep (k := 328) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (328 : Int)] = .value (g.address1.add 328#64) at hg328
  have hg336 := hk.gep (k := 336) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (336 : Int)] = .value (g.address1.add 336#64) at hg336
  have hg344 := hk.gep (k := 344) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (344 : Int)] = .value (g.address1.add 344#64) at hg344
  have hg352 := hk.gep (k := 352) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (352 : Int)] = .value (g.address1.add 352#64) at hg352
  have hg360 := hk.gep (k := 360) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (360 : Int)] = .value (g.address1.add 360#64) at hg360
  have hg368 := hk.gep (k := 368) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (368 : Int)] = .value (g.address1.add 368#64) at hg368
  have hg376 := hk.gep (k := 376) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (376 : Int)] = .value (g.address1.add 376#64) at hg376
  have hg384 := hk.gep (k := 384) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (384 : Int)] = .value (g.address1.add 384#64) at hg384
  simp (config := { maxSteps := 300000 }) [program.bb0, List.foldlM_cons,
    List.foldlM_nil, Instr.run, dispatchChunk2, GepIndex.inboundsOffset, Ty.wrap,
    Operation.load, hg264, hg272, hg280, hg288, hg296, hg304, hg312, hg320, hg328, hg336, hg344, hg352, hg360, hg368, hg376, hg384, h23,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

private theorem dispatch_chunk3 (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (cache : BitVec 8)
    (hk : SmallRange state.mem g.address1 640)
    (hc : SmallRange state.mem g.address0 1)
    (hr : state.mem.readAt g.address0 8 = cache)
    (h23 : E.read (%23) = .value g.address1)
    : List.foldlM Instr.run E (((program.bb0 g).body.drop 111).take 32) state =
      .value (dispatchChunk3 E g cache, state) := by
  have hg392 := hk.gep (k := 392) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (392 : Int)] = .value (g.address1.add 392#64) at hg392
  have hg400 := hk.gep (k := 400) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (400 : Int)] = .value (g.address1.add 400#64) at hg400
  have hg408 := hk.gep (k := 408) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (408 : Int)] = .value (g.address1.add 408#64) at hg408
  have hg416 := hk.gep (k := 416) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (416 : Int)] = .value (g.address1.add 416#64) at hg416
  have hg424 := hk.gep (k := 424) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (424 : Int)] = .value (g.address1.add 424#64) at hg424
  have hg432 := hk.gep (k := 432) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (432 : Int)] = .value (g.address1.add 432#64) at hg432
  have hg440 := hk.gep (k := 440) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (440 : Int)] = .value (g.address1.add 440#64) at hg440
  have hg448 := hk.gep (k := 448) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (448 : Int)] = .value (g.address1.add 448#64) at hg448
  have hg456 := hk.gep (k := 456) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (456 : Int)] = .value (g.address1.add 456#64) at hg456
  have hg464 := hk.gep (k := 464) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (464 : Int)] = .value (g.address1.add 464#64) at hg464
  have hg472 := hk.gep (k := 472) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (472 : Int)] = .value (g.address1.add 472#64) at hg472
  have hg480 := hk.gep (k := 480) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (480 : Int)] = .value (g.address1.add 480#64) at hg480
  have hg488 := hk.gep (k := 488) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (488 : Int)] = .value (g.address1.add 488#64) at hg488
  have hg496 := hk.gep (k := 496) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (496 : Int)] = .value (g.address1.add 496#64) at hg496
  have hg504 := hk.gep (k := 504) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (504 : Int)] = .value (g.address1.add 504#64) at hg504
  have hg512 := hk.gep (k := 512) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (512 : Int)] = .value (g.address1.add 512#64) at hg512
  simp (config := { maxSteps := 300000 }) [program.bb0, List.foldlM_cons,
    List.foldlM_nil, Instr.run, dispatchChunk3, GepIndex.inboundsOffset, Ty.wrap,
    Operation.load, hg392, hg400, hg408, hg416, hg424, hg432, hg440, hg448, hg456, hg464, hg472, hg480, hg488, hg496, hg504, hg512, h23,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

private theorem dispatch_chunk4 (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (cache : BitVec 8)
    (hk : SmallRange state.mem g.address1 640)
    (hc : SmallRange state.mem g.address0 1)
    (hr : state.mem.readAt g.address0 8 = cache)
    (h23 : E.read (%23) = .value g.address1)
    : List.foldlM Instr.run E (((program.bb0 g).body.drop 143).take 30) state =
      .value (dispatchChunk4 E g cache, state) := by
  have hg520 := hk.gep (k := 520) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (520 : Int)] = .value (g.address1.add 520#64) at hg520
  have hg528 := hk.gep (k := 528) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (528 : Int)] = .value (g.address1.add 528#64) at hg528
  have hg536 := hk.gep (k := 536) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (536 : Int)] = .value (g.address1.add 536#64) at hg536
  have hg544 := hk.gep (k := 544) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (544 : Int)] = .value (g.address1.add 544#64) at hg544
  have hg552 := hk.gep (k := 552) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (552 : Int)] = .value (g.address1.add 552#64) at hg552
  have hg560 := hk.gep (k := 560) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (560 : Int)] = .value (g.address1.add 560#64) at hg560
  have hg568 := hk.gep (k := 568) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (568 : Int)] = .value (g.address1.add 568#64) at hg568
  have hg576 := hk.gep (k := 576) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (576 : Int)] = .value (g.address1.add 576#64) at hg576
  have hg584 := hk.gep (k := 584) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (584 : Int)] = .value (g.address1.add 584#64) at hg584
  have hg592 := hk.gep (k := 592) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (592 : Int)] = .value (g.address1.add 592#64) at hg592
  have hg600 := hk.gep (k := 600) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (600 : Int)] = .value (g.address1.add 600#64) at hg600
  have hg608 := hk.gep (k := 608) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (608 : Int)] = .value (g.address1.add 608#64) at hg608
  have hg616 := hk.gep (k := 616) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (616 : Int)] = .value (g.address1.add 616#64) at hg616
  have hg624 := hk.gep (k := 624) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (624 : Int)] = .value (g.address1.add 624#64) at hg624
  have hg632 := hk.gep (k := 632) (by decide)
  change Operation.gepInboundsLive state.mem (.value g.address1) [.value (632 : Int)] = .value (g.address1.add 632#64) at hg632
  simp (config := { maxSteps := 300000 }) [program.bb0, List.foldlM_cons,
    List.foldlM_nil, Instr.run, dispatchChunk4, GepIndex.inboundsOffset, Ty.wrap,
    Operation.load, hg520, hg528, hg536, hg544, hg552, hg560, hg568, hg576, hg584, hg592, hg600, hg608, hg616, hg624, hg632, h23,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

private theorem dispatch_chunk5 (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (cache : BitVec 8)
    (hk : SmallRange state.mem g.address1 640)
    (hc : SmallRange state.mem g.address0 1)
    (hr : state.mem.readAt g.address0 8 = cache)
    (h0 : E.read (%0) = .value g.address0)
    : List.foldlM Instr.run E (((program.bb0 g).body.drop 173).take 3) state =
      .value (dispatchChunk5 E g cache, state) := by
  have hf := hc.fits
  simp (config := { maxSteps := 300000 }) [program.bb0, List.foldlM_cons,
    List.foldlM_nil, Instr.run, dispatchChunk5, GepIndex.inboundsOffset, Ty.wrap,
    Operation.load, hf, hr, h0,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

/-- Exact read-only body execution. K64 contents are irrelevant for this
slice, but its live extent is necessary for all emitted inbounds GEPs. -/
theorem dispatch_entry_body (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (cache : BitVec 8)
    (hk : SmallRange state.mem g.address1 640)
    (hc : SmallRange state.mem g.address0 1)
    (hr : state.mem.readAt g.address0 8 = cache) :
    List.foldlM Instr.run E (program.bb0 g).body state =
      .value (dispatchEntryEnv E g cache, state) := by
  have hsplit : (program.bb0 g).body =
    ((program.bb0 g).body.drop 0).take 47 ++
    ((program.bb0 g).body.drop 47).take 32 ++
    ((program.bb0 g).body.drop 79).take 32 ++
    ((program.bb0 g).body.drop 111).take 32 ++
    ((program.bb0 g).body.drop 143).take 30 ++
    ((program.bb0 g).body.drop 173).take 3 := by rfl
  rw [hsplit]
  simp only [List.foldlM_append, EffectM.bind_eq]
  rw [dispatch_chunk0 g E state cache hk hc hr]
  try dsimp
  rw [dispatch_chunk1 g (dispatchChunk0 E g cache) state cache hk hc hr (by simp [dispatchChunk0, mlir_env])]
  try dsimp
  rw [dispatch_chunk2 g (dispatchChunk1 (dispatchChunk0 E g cache) g cache) state cache hk hc hr (by simp [dispatchChunk0, dispatchChunk1, mlir_env])]
  try dsimp
  rw [dispatch_chunk3 g (dispatchChunk2 (dispatchChunk1 (dispatchChunk0 E g cache) g cache) g cache) state cache hk hc hr (by simp [dispatchChunk0, dispatchChunk1, dispatchChunk2, mlir_env])]
  try dsimp
  rw [dispatch_chunk4 g (dispatchChunk3 (dispatchChunk2 (dispatchChunk1 (dispatchChunk0 E g cache) g cache) g cache) g cache) state cache hk hc hr (by simp [dispatchChunk0, dispatchChunk1, dispatchChunk2, dispatchChunk3, mlir_env])]
  try dsimp
  rw [dispatch_chunk5 g (dispatchChunk4 (dispatchChunk3 (dispatchChunk2 (dispatchChunk1 (dispatchChunk0 E g cache) g cache) g cache) g cache) g cache) state cache hk hc hr (by simp [dispatchChunk0, dispatchChunk1, dispatchChunk2, dispatchChunk3, dispatchChunk4, mlir_env])]
  try dsimp
  rfl

@[simp] theorem dispatch_params1 : program.blockParams 1 = .nil := rfl
@[simp] theorem dispatch_params2 : program.blockParams 2 = .nil := rfl
@[simp] theorem dispatch_params3 : program.blockParams 3 = .nil := rfl
@[simp] theorem dispatch_params6 : program.blockParams 6 = .nil := rfl
@[simp] theorem dispatch_params7 : program.blockParams 7 = .nil := rfl

/-- One actual CFG step, including the original three-way switch. -/
theorem dispatch_entry_step (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (cache : BitVec 8)
    (hk : SmallRange state.mem g.address1 640)
    (hc : SmallRange state.mem g.address0 1)
    (hr : state.mem.readAt g.address0 8 = cache) :
    (program.bb0 g).run program.blockParams E state =
      .value ((dispatchEntryEnv E g cache, .inr (dispatchTarget cache)), state) := by
  rw [BasicBlock.run_eq]
  have hb := dispatch_entry_body g E state cache hk hc hr
  change (List.foldlM Instr.run E (program.bb0 g).body state >>= _) = _
  rw [hb]
  by_cases h255 : cache = 255#8 <;> by_cases h1 : cache = 1#8 <;>
    simp [program.bb0, Exit.run, switchTarget, Jump.run_ite, Jump.run, dispatchTarget,
      dispatchEntryEnv, dispatchChunk5, mlir_env, Regs.read_nil, Env.writeMany_nil,
      EffectM.bind_eq, EffectM.pure_eq, h255, h1, Ty.unwrap]
  all_goals
    rw [ite_eq_right h255, ite_eq_right h1]
    rfl

/-- Continuation equation derived from the concrete successful CFG step. -/
theorem dispatch_entry_runFrom (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (cache : BitVec 8)
    (hk : SmallRange state.mem g.address1 640)
    (hc : SmallRange state.mem g.address0 1)
    (hr : state.mem.readAt g.address0 8 = cache) :
    (program p g).runFrom E 0 state =
      (program p g).runFrom (dispatchEntryEnv E g cache) (dispatchTarget cache) state := by
  rw [Func.runFrom_eq]
  change ((program.bb0 g).run program.blockParams E state >>= _) = _
  rw [dispatch_entry_step g E state cache hk hc hr]
  rfl

/-- The full global invariant supplies the entry's concrete memory premises.
This theorem exposes which legal cache byte determines the next block. -/
theorem dispatch_entry_ready (p : Primitives) (cg : CompressionGlobals)
    (E : Env program.Γ) (state : GlobalState) (h : CompressionReady cg state) :
    ∃ cache, CacheByteLegal cache ∧
      (program p ⟨cg.cachePtr, cg.constantsPtr⟩).runFrom E 0 state =
        (program p ⟨cg.cachePtr, cg.constantsPtr⟩).runFrom
          (dispatchEntryEnv E ⟨cg.cachePtr, cg.constantsPtr⟩ cache)
          (dispatchTarget cache) state := by
  obtain ⟨cache, legal, present⟩ := h.cache
  exact ⟨cache, legal, dispatch_entry_runFrom p _ E state cache
    h.constants_range h.cache_range present.readAt⟩

end Agave.Ed25519.SHA512.Execution.Dispatch
