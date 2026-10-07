import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullInputMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRound79

/-! Exact imported bb4 message-loading and byte-decoding prefix. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Spec

def inputEnv (E : Env program.Γ) (mem : MemoryState) (data : Pointer) : Env program.Γ :=
  E[%202 := .value (data.add 128#64),
    %203 := .value (mem.readAt (data.add 0#64) 64),
    %204 := .value (readWordBE (readBytes mem data 128) 0),
    %205 := .value (data.add 8#64),
    %206 := .value (mem.readAt (data.add 8#64) 64),
    %207 := .value (readWordBE (readBytes mem data 128) 1),
    %208 := .value (data.add 16#64),
    %209 := .value (mem.readAt (data.add 16#64) 64),
    %210 := .value (readWordBE (readBytes mem data 128) 2),
    %211 := .value (data.add 24#64),
    %212 := .value (mem.readAt (data.add 24#64) 64),
    %213 := .value (readWordBE (readBytes mem data 128) 3),
    %214 := .value (data.add 32#64),
    %215 := .value (mem.readAt (data.add 32#64) 64),
    %216 := .value (readWordBE (readBytes mem data 128) 4),
    %217 := .value (data.add 40#64),
    %218 := .value (mem.readAt (data.add 40#64) 64),
    %219 := .value (readWordBE (readBytes mem data 128) 5),
    %220 := .value (data.add 48#64),
    %221 := .value (mem.readAt (data.add 48#64) 64),
    %222 := .value (readWordBE (readBytes mem data 128) 6),
    %223 := .value (data.add 56#64),
    %224 := .value (mem.readAt (data.add 56#64) 64),
    %225 := .value (readWordBE (readBytes mem data 128) 7),
    %226 := .value (data.add 64#64),
    %227 := .value (mem.readAt (data.add 64#64) 64),
    %228 := .value (readWordBE (readBytes mem data 128) 8),
    %229 := .value (data.add 72#64),
    %230 := .value (mem.readAt (data.add 72#64) 64),
    %231 := .value (readWordBE (readBytes mem data 128) 9),
    %232 := .value (data.add 80#64),
    %233 := .value (mem.readAt (data.add 80#64) 64),
    %234 := .value (readWordBE (readBytes mem data 128) 10),
    %235 := .value (data.add 88#64),
    %236 := .value (mem.readAt (data.add 88#64) 64),
    %237 := .value (readWordBE (readBytes mem data 128) 11),
    %238 := .value (data.add 96#64),
    %239 := .value (mem.readAt (data.add 96#64) 64),
    %240 := .value (readWordBE (readBytes mem data 128) 12),
    %241 := .value (data.add 104#64),
    %242 := .value (mem.readAt (data.add 104#64) 64),
    %243 := .value (readWordBE (readBytes mem data 128) 13),
    %244 := .value (data.add 112#64),
    %245 := .value (mem.readAt (data.add 112#64) 64),
    %246 := .value (readWordBE (readBytes mem data 128) 14),
    %247 := .value (data.add 120#64),
    %248 := .value (mem.readAt (data.add 120#64) 64),
    %249 := .value (readWordBE (readBytes mem data 128) 15)]

theorem input_before (E : Env program.Γ) (mem : MemoryState) (data : Pointer) :
    Before 202 E (inputEnv E mem data) := by
  unfold inputEnv
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem input_body (E : Env program.Γ) (state : GlobalState) (data : Pointer)
    (hd : SmallRange state.mem data 128) (hdata : E.read (%200) = .value data) :
    List.foldlM Instr.run E (program.bb4.body.take 50) state =
      .value (inputEnv E state.mem data, state) := by
  have hf0 : Fits state.mem (data.add 0#64) 64 := hd.fits_add (k := 0) (count := 8) (by decide)
  have hb0 := load_bswap_readWordBE state.mem data hd 0 (by decide)
  change Operation.bswap (.value (state.mem.readAt (data.add 0#64) 64)) = .value (readWordBE (readBytes state.mem data 128) 0) at hb0
  have hf1 : Fits state.mem (data.add 8#64) 64 := hd.fits_add (k := 8) (count := 8) (by decide)
  have hb1 := load_bswap_readWordBE state.mem data hd 1 (by decide)
  change Operation.bswap (.value (state.mem.readAt (data.add 8#64) 64)) = .value (readWordBE (readBytes state.mem data 128) 1) at hb1
  have hf2 : Fits state.mem (data.add 16#64) 64 := hd.fits_add (k := 16) (count := 8) (by decide)
  have hb2 := load_bswap_readWordBE state.mem data hd 2 (by decide)
  change Operation.bswap (.value (state.mem.readAt (data.add 16#64) 64)) = .value (readWordBE (readBytes state.mem data 128) 2) at hb2
  have hf3 : Fits state.mem (data.add 24#64) 64 := hd.fits_add (k := 24) (count := 8) (by decide)
  have hb3 := load_bswap_readWordBE state.mem data hd 3 (by decide)
  change Operation.bswap (.value (state.mem.readAt (data.add 24#64) 64)) = .value (readWordBE (readBytes state.mem data 128) 3) at hb3
  have hf4 : Fits state.mem (data.add 32#64) 64 := hd.fits_add (k := 32) (count := 8) (by decide)
  have hb4 := load_bswap_readWordBE state.mem data hd 4 (by decide)
  change Operation.bswap (.value (state.mem.readAt (data.add 32#64) 64)) = .value (readWordBE (readBytes state.mem data 128) 4) at hb4
  have hf5 : Fits state.mem (data.add 40#64) 64 := hd.fits_add (k := 40) (count := 8) (by decide)
  have hb5 := load_bswap_readWordBE state.mem data hd 5 (by decide)
  change Operation.bswap (.value (state.mem.readAt (data.add 40#64) 64)) = .value (readWordBE (readBytes state.mem data 128) 5) at hb5
  have hf6 : Fits state.mem (data.add 48#64) 64 := hd.fits_add (k := 48) (count := 8) (by decide)
  have hb6 := load_bswap_readWordBE state.mem data hd 6 (by decide)
  change Operation.bswap (.value (state.mem.readAt (data.add 48#64) 64)) = .value (readWordBE (readBytes state.mem data 128) 6) at hb6
  have hf7 : Fits state.mem (data.add 56#64) 64 := hd.fits_add (k := 56) (count := 8) (by decide)
  have hb7 := load_bswap_readWordBE state.mem data hd 7 (by decide)
  change Operation.bswap (.value (state.mem.readAt (data.add 56#64) 64)) = .value (readWordBE (readBytes state.mem data 128) 7) at hb7
  have hf8 : Fits state.mem (data.add 64#64) 64 := hd.fits_add (k := 64) (count := 8) (by decide)
  have hb8 := load_bswap_readWordBE state.mem data hd 8 (by decide)
  change Operation.bswap (.value (state.mem.readAt (data.add 64#64) 64)) = .value (readWordBE (readBytes state.mem data 128) 8) at hb8
  have hf9 : Fits state.mem (data.add 72#64) 64 := hd.fits_add (k := 72) (count := 8) (by decide)
  have hb9 := load_bswap_readWordBE state.mem data hd 9 (by decide)
  change Operation.bswap (.value (state.mem.readAt (data.add 72#64) 64)) = .value (readWordBE (readBytes state.mem data 128) 9) at hb9
  have hf10 : Fits state.mem (data.add 80#64) 64 := hd.fits_add (k := 80) (count := 8) (by decide)
  have hb10 := load_bswap_readWordBE state.mem data hd 10 (by decide)
  change Operation.bswap (.value (state.mem.readAt (data.add 80#64) 64)) = .value (readWordBE (readBytes state.mem data 128) 10) at hb10
  have hf11 : Fits state.mem (data.add 88#64) 64 := hd.fits_add (k := 88) (count := 8) (by decide)
  have hb11 := load_bswap_readWordBE state.mem data hd 11 (by decide)
  change Operation.bswap (.value (state.mem.readAt (data.add 88#64) 64)) = .value (readWordBE (readBytes state.mem data 128) 11) at hb11
  have hf12 : Fits state.mem (data.add 96#64) 64 := hd.fits_add (k := 96) (count := 8) (by decide)
  have hb12 := load_bswap_readWordBE state.mem data hd 12 (by decide)
  change Operation.bswap (.value (state.mem.readAt (data.add 96#64) 64)) = .value (readWordBE (readBytes state.mem data 128) 12) at hb12
  have hf13 : Fits state.mem (data.add 104#64) 64 := hd.fits_add (k := 104) (count := 8) (by decide)
  have hb13 := load_bswap_readWordBE state.mem data hd 13 (by decide)
  change Operation.bswap (.value (state.mem.readAt (data.add 104#64) 64)) = .value (readWordBE (readBytes state.mem data 128) 13) at hb13
  have hf14 : Fits state.mem (data.add 112#64) 64 := hd.fits_add (k := 112) (count := 8) (by decide)
  have hb14 := load_bswap_readWordBE state.mem data hd 14 (by decide)
  change Operation.bswap (.value (state.mem.readAt (data.add 112#64) 64)) = .value (readWordBE (readBytes state.mem data 128) 14) at hb14
  have hf15 : Fits state.mem (data.add 120#64) 64 := hd.fits_add (k := 120) (count := 8) (by decide)
  have hb15 := load_bswap_readWordBE state.mem data hd 15 (by decide)
  change Operation.bswap (.value (state.mem.readAt (data.add 120#64) 64)) = .value (readWordBE (readBytes state.mem data 128) 15) at hb15
  have hg1 := hd.gep (k := 8) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (8 : Int)] = .value (data.add 8#64) at hg1
  have hg2 := hd.gep (k := 16) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (16 : Int)] = .value (data.add 16#64) at hg2
  have hg3 := hd.gep (k := 24) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (24 : Int)] = .value (data.add 24#64) at hg3
  have hg4 := hd.gep (k := 32) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (32 : Int)] = .value (data.add 32#64) at hg4
  have hg5 := hd.gep (k := 40) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (40 : Int)] = .value (data.add 40#64) at hg5
  have hg6 := hd.gep (k := 48) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (48 : Int)] = .value (data.add 48#64) at hg6
  have hg7 := hd.gep (k := 56) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (56 : Int)] = .value (data.add 56#64) at hg7
  have hg8 := hd.gep (k := 64) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (64 : Int)] = .value (data.add 64#64) at hg8
  have hg9 := hd.gep (k := 72) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (72 : Int)] = .value (data.add 72#64) at hg9
  have hg10 := hd.gep (k := 80) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (80 : Int)] = .value (data.add 80#64) at hg10
  have hg11 := hd.gep (k := 88) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (88 : Int)] = .value (data.add 88#64) at hg11
  have hg12 := hd.gep (k := 96) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (96 : Int)] = .value (data.add 96#64) at hg12
  have hg13 := hd.gep (k := 104) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (104 : Int)] = .value (data.add 104#64) at hg13
  have hg14 := hd.gep (k := 112) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (112 : Int)] = .value (data.add 112#64) at hg14
  have hg15 := hd.gep (k := 120) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (120 : Int)] = .value (data.add 120#64) at hg15
  have hg16 := hd.gep (k := 128) (by decide)
  change Operation.gepInboundsLive state.mem (.value data) [.value (128 : Int)] = .value (data.add 128#64) at hg16
  simp only [Pointer.add_zero] at hf0 hb0
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run, inputEnv, hdata,
    hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15,
    hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16,
    GepIndex.inboundsOffset, Operation.load, UnOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem input_initial (E : Env program.Γ) (mem : MemoryState) (data : Pointer)
    (initial : Spec.State) (hi : InitialReady E initial) :
    InitialReady (inputEnv E mem data) initial := by
  have hb := input_before E mem data
  constructor
  · rw [hb.read_val 201 (by decide) (by rfl)]; exact hi.a
  · rw [hb.read_val 199 (by decide) (by rfl)]; exact hi.b
  · rw [hb.read_val 198 (by decide) (by rfl)]; exact hi.c
  · rw [hb.read_val 197 (by decide) (by rfl)]; exact hi.d
  · rw [hb.read_val 196 (by decide) (by rfl)]; exact hi.e
  · rw [hb.read_val 195 (by decide) (by rfl)]; exact hi.f
  · rw [hb.read_val 194 (by decide) (by rfl)]; exact hi.g
  · rw [hb.read_val 193 (by decide) (by rfl)]; exact hi.h

theorem input_ready (E : Env program.Γ) (mem : MemoryState) (data : Pointer)
    (initial : Spec.State) (hi : InitialReady E initial) :
    Ready00 (inputEnv E mem data) initial (fun r => (schedule (readBytes mem data 128)).getD r 0) := by
  have hb := input_before E mem data
  constructor
  · rw [hb.read_val 201 (by decide) (by rfl)]; exact hi.a
  · rw [hb.read_val 199 (by decide) (by rfl)]; exact hi.b
  · rw [hb.read_val 198 (by decide) (by rfl)]; exact hi.c
  · rw [hb.read_val 197 (by decide) (by rfl)]; exact hi.d
  · rw [hb.read_val 196 (by decide) (by rfl)]; exact hi.e
  · rw [hb.read_val 195 (by decide) (by rfl)]; exact hi.f
  · rw [hb.read_val 194 (by decide) (by rfl)]; exact hi.g
  · rw [hb.read_val 193 (by decide) (by rfl)]; exact hi.h
  · rw [schedule_initial _ 0 (by decide)]
    simp [inputEnv, mlir_env]
  · rw [schedule_initial _ 1 (by decide)]
    simp [inputEnv, mlir_env]
  · rw [schedule_initial _ 2 (by decide)]
    simp [inputEnv, mlir_env]
  · rw [schedule_initial _ 3 (by decide)]
    simp [inputEnv, mlir_env]
  · rw [schedule_initial _ 4 (by decide)]
    simp [inputEnv, mlir_env]
  · rw [schedule_initial _ 5 (by decide)]
    simp [inputEnv, mlir_env]
  · rw [schedule_initial _ 6 (by decide)]
    simp [inputEnv, mlir_env]
  · rw [schedule_initial _ 7 (by decide)]
    simp [inputEnv, mlir_env]
  · rw [schedule_initial _ 8 (by decide)]
    simp [inputEnv, mlir_env]
  · rw [schedule_initial _ 9 (by decide)]
    simp [inputEnv, mlir_env]
  · rw [schedule_initial _ 10 (by decide)]
    simp [inputEnv, mlir_env]
  · rw [schedule_initial _ 11 (by decide)]
    simp [inputEnv, mlir_env]
  · rw [schedule_initial _ 12 (by decide)]
    simp [inputEnv, mlir_env]
  · rw [schedule_initial _ 13 (by decide)]
    simp [inputEnv, mlir_env]
  · rw [schedule_initial _ 14 (by decide)]
    simp [inputEnv, mlir_env]
  · rw [schedule_initial _ 15 (by decide)]
    simp [inputEnv, mlir_env]

theorem input_constants (E : Env program.Γ) (mem : MemoryState) (data kp : Pointer)
    (hc : Constants E kp) : Constants (inputEnv E mem data) kp := by
  have hb := input_before E mem data
  constructor
  · rw [hb.read_val 1 (by decide) (by rfl)]; exact hc.v1
  · rw [hb.read_val 9 (by decide) (by rfl)]; exact hc.v9
  · rw [hb.read_val 19 (by decide) (by rfl)]; exact hc.v19
  · rw [hb.read_val 20 (by decide) (by rfl)]; exact hc.v20
  · rw [hb.read_val 21 (by decide) (by rfl)]; exact hc.v21
  · rw [hb.read_val 22 (by decide) (by rfl)]; exact hc.v22
  · rw [hb.read_val 24 (by decide) (by rfl)]; exact hc.v24
  · rw [hb.read_val 25 (by decide) (by rfl)]; exact hc.v25
  · rw [hb.read_val 26 (by decide) (by rfl)]; exact hc.v26
  · rw [hb.read_val 42 (by decide) (by rfl)]; exact hc.v42
  · rw [hb.read_val 43 (by decide) (by rfl)]; exact hc.v43
  · rw [hb.read_val 44 (by decide) (by rfl)]; exact hc.v44
  · rw [hb.read_val 45 (by decide) (by rfl)]; exact hc.v45
  · rw [hb.read_val 23 (by decide) (by rfl)]; exact hc.k00
  · rw [hb.read_val 27 (by decide) (by rfl)]; exact hc.k01
  · rw [hb.read_val 28 (by decide) (by rfl)]; exact hc.k02
  · rw [hb.read_val 29 (by decide) (by rfl)]; exact hc.k03
  · rw [hb.read_val 30 (by decide) (by rfl)]; exact hc.k04
  · rw [hb.read_val 31 (by decide) (by rfl)]; exact hc.k05
  · rw [hb.read_val 32 (by decide) (by rfl)]; exact hc.k06
  · rw [hb.read_val 33 (by decide) (by rfl)]; exact hc.k07
  · rw [hb.read_val 34 (by decide) (by rfl)]; exact hc.k08
  · rw [hb.read_val 35 (by decide) (by rfl)]; exact hc.k09
  · rw [hb.read_val 36 (by decide) (by rfl)]; exact hc.k10
  · rw [hb.read_val 37 (by decide) (by rfl)]; exact hc.k11
  · rw [hb.read_val 38 (by decide) (by rfl)]; exact hc.k12
  · rw [hb.read_val 39 (by decide) (by rfl)]; exact hc.k13
  · rw [hb.read_val 40 (by decide) (by rfl)]; exact hc.k14
  · rw [hb.read_val 41 (by decide) (by rfl)]; exact hc.k15
  · rw [hb.read_val 46 (by decide) (by rfl)]; exact hc.k16
  · rw [hb.read_val 48 (by decide) (by rfl)]; exact hc.k17
  · rw [hb.read_val 50 (by decide) (by rfl)]; exact hc.k18
  · rw [hb.read_val 52 (by decide) (by rfl)]; exact hc.k19
  · rw [hb.read_val 54 (by decide) (by rfl)]; exact hc.k20
  · rw [hb.read_val 56 (by decide) (by rfl)]; exact hc.k21
  · rw [hb.read_val 58 (by decide) (by rfl)]; exact hc.k22
  · rw [hb.read_val 60 (by decide) (by rfl)]; exact hc.k23
  · rw [hb.read_val 62 (by decide) (by rfl)]; exact hc.k24
  · rw [hb.read_val 64 (by decide) (by rfl)]; exact hc.k25
  · rw [hb.read_val 66 (by decide) (by rfl)]; exact hc.k26
  · rw [hb.read_val 68 (by decide) (by rfl)]; exact hc.k27
  · rw [hb.read_val 70 (by decide) (by rfl)]; exact hc.k28
  · rw [hb.read_val 72 (by decide) (by rfl)]; exact hc.k29
  · rw [hb.read_val 74 (by decide) (by rfl)]; exact hc.k30
  · rw [hb.read_val 76 (by decide) (by rfl)]; exact hc.k31
  · rw [hb.read_val 78 (by decide) (by rfl)]; exact hc.k32
  · rw [hb.read_val 80 (by decide) (by rfl)]; exact hc.k33
  · rw [hb.read_val 82 (by decide) (by rfl)]; exact hc.k34
  · rw [hb.read_val 84 (by decide) (by rfl)]; exact hc.k35
  · rw [hb.read_val 86 (by decide) (by rfl)]; exact hc.k36
  · rw [hb.read_val 88 (by decide) (by rfl)]; exact hc.k37
  · rw [hb.read_val 90 (by decide) (by rfl)]; exact hc.k38
  · rw [hb.read_val 92 (by decide) (by rfl)]; exact hc.k39
  · rw [hb.read_val 94 (by decide) (by rfl)]; exact hc.k40
  · rw [hb.read_val 96 (by decide) (by rfl)]; exact hc.k41
  · rw [hb.read_val 98 (by decide) (by rfl)]; exact hc.k42
  · rw [hb.read_val 100 (by decide) (by rfl)]; exact hc.k43
  · rw [hb.read_val 102 (by decide) (by rfl)]; exact hc.k44
  · rw [hb.read_val 104 (by decide) (by rfl)]; exact hc.k45
  · rw [hb.read_val 106 (by decide) (by rfl)]; exact hc.k46
  · rw [hb.read_val 108 (by decide) (by rfl)]; exact hc.k47
  · rw [hb.read_val 110 (by decide) (by rfl)]; exact hc.k48
  · rw [hb.read_val 112 (by decide) (by rfl)]; exact hc.k49
  · rw [hb.read_val 114 (by decide) (by rfl)]; exact hc.k50
  · rw [hb.read_val 116 (by decide) (by rfl)]; exact hc.k51
  · rw [hb.read_val 118 (by decide) (by rfl)]; exact hc.k52
  · rw [hb.read_val 120 (by decide) (by rfl)]; exact hc.k53
  · rw [hb.read_val 122 (by decide) (by rfl)]; exact hc.k54
  · rw [hb.read_val 124 (by decide) (by rfl)]; exact hc.k55
  · rw [hb.read_val 126 (by decide) (by rfl)]; exact hc.k56
  · rw [hb.read_val 128 (by decide) (by rfl)]; exact hc.k57
  · rw [hb.read_val 130 (by decide) (by rfl)]; exact hc.k58
  · rw [hb.read_val 132 (by decide) (by rfl)]; exact hc.k59
  · rw [hb.read_val 134 (by decide) (by rfl)]; exact hc.k60
  · rw [hb.read_val 136 (by decide) (by rfl)]; exact hc.k61
  · rw [hb.read_val 138 (by decide) (by rfl)]; exact hc.k62
  · rw [hb.read_val 140 (by decide) (by rfl)]; exact hc.k63
  · rw [hb.read_val 142 (by decide) (by rfl)]; exact hc.k64
  · rw [hb.read_val 144 (by decide) (by rfl)]; exact hc.k65
  · rw [hb.read_val 146 (by decide) (by rfl)]; exact hc.k66
  · rw [hb.read_val 148 (by decide) (by rfl)]; exact hc.k67
  · rw [hb.read_val 150 (by decide) (by rfl)]; exact hc.k68
  · rw [hb.read_val 152 (by decide) (by rfl)]; exact hc.k69
  · rw [hb.read_val 154 (by decide) (by rfl)]; exact hc.k70
  · rw [hb.read_val 156 (by decide) (by rfl)]; exact hc.k71
  · rw [hb.read_val 158 (by decide) (by rfl)]; exact hc.k72
  · rw [hb.read_val 160 (by decide) (by rfl)]; exact hc.k73
  · rw [hb.read_val 162 (by decide) (by rfl)]; exact hc.k74
  · rw [hb.read_val 164 (by decide) (by rfl)]; exact hc.k75
  · rw [hb.read_val 166 (by decide) (by rfl)]; exact hc.k76
  · rw [hb.read_val 168 (by decide) (by rfl)]; exact hc.k77
  · rw [hb.read_val 170 (by decide) (by rfl)]; exact hc.k78
  · rw [hb.read_val 172 (by decide) (by rfl)]; exact hc.k79

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
