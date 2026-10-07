import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionInitialBlockChain
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionInitialVectors

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def initialSlice0Env (E : Env program.Γ) (data scratch : Pointer) (block : Bytes)
    (k0 k1 : Word) : Env program.Γ :=
  E[%107 := Ty.unflatten (.vec 16 8) (readWordNative block 1 ++ readWordNative block 0), %108 := initialShuffle (readWordNative block 1 ++ readWordNative block 0), %109 := pairVec (readWordBE block 0) (readWordBE block 1), %110 := pairVec (readWordBE block 0+k0) (readWordBE block 1+k1)]

theorem initial_slice0_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch : Pointer) (block : Bytes) (k0 k1 : Word)
    (hd : SmallRange mem.mem data 128) (hs : SmallRange mem.mem scratch 128)
    (hp : E.read (%arg1) = .value data) (hq : E.read (%81) = .value scratch)
    (hk : E.read (%11) = pairVec k0 k1)
    (hr : mem.mem.readAt data 128 =
      readWordNative block 1 ++ readWordNative block 0) :
    List.foldlM Instr.run E ((program.bb2.body.drop 18).take 5) mem =
      .value (initialSlice0Env E data scratch block k0 k1,
        pairStoreState mem scratch 0 (readWordBE block 0+k0) (readWordBE block 1+k1)) := by
  have hp' : E.args 1 = .value data := hp
  have hgd := hd.gep (k := 0) (by decide)
  have hgs := hs.gep (k := 0) (by decide)
  norm_num only at hgd hgs
  have hfd := hd.fits_add (k := 0) (count := 16) (by decide)
  have hfs := hs.fits_add (k := 0) (count := 16) (by decide)
  try simp only [Pointer.add_zero] at hfd hfs
  have hshuffle := initialShuffle_any
    (readWordNative block 1 ++ readWordNative block 0) (E.read (%10))
  simp only [initialMask, Ty.unflatten_vec] at hshuffle
  have hcast := initialPair_native block 0 1
  unfold initialPair at hcast
  simp [program.bb2, List.foldlM_cons, List.foldlM_nil, Instr.run,
    initialSlice0Env, pairStoreState, pairScratchStore,
    hp', hq, hk, hgd, hgs, hfd, hfs, hr,
    hshuffle, hcast, pairVec_add,
    pairVec_flatten, UnOp.compute, GepIndex.inboundsOffset, Operation.load, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

def initialSlice1Env (E : Env program.Γ) (data scratch : Pointer) (block : Bytes)
    (k0 k1 : Word) : Env program.Γ :=
  E[%111 := .value (data.add 16#64), %112 := Ty.unflatten (.vec 16 8) (readWordNative block 3 ++ readWordNative block 2), %113 := initialShuffle (readWordNative block 3 ++ readWordNative block 2), %114 := pairVec (readWordBE block 2) (readWordBE block 3), %115 := pairVec (readWordBE block 2+k0) (readWordBE block 3+k1), %116 := .value (scratch.add 16#64)]

theorem initial_slice1_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch : Pointer) (block : Bytes) (k0 k1 : Word)
    (hd : SmallRange mem.mem data 128) (hs : SmallRange mem.mem scratch 128)
    (hp : E.read (%arg1) = .value data) (hq : E.read (%81) = .value scratch)
    (hk : E.read (%12) = pairVec k0 k1)
    (hr : mem.mem.readAt (data.add 16#64) 128 =
      readWordNative block 3 ++ readWordNative block 2) :
    List.foldlM Instr.run E ((program.bb2.body.drop 23).take 7) mem =
      .value (initialSlice1Env E data scratch block k0 k1,
        pairStoreState mem scratch 1 (readWordBE block 2+k0) (readWordBE block 3+k1)) := by
  have hp' : E.args 1 = .value data := hp
  have hgd := hd.gep (k := 16) (by decide)
  have hgs := hs.gep (k := 16) (by decide)
  norm_num only at hgd hgs
  have hfd := hd.fits_add (k := 16) (count := 16) (by decide)
  have hfs := hs.fits_add (k := 16) (count := 16) (by decide)
  try simp only [Pointer.add_zero] at hfd hfs
  have hshuffle := initialShuffle_any
    (readWordNative block 3 ++ readWordNative block 2) (E.read (%10))
  simp only [initialMask, Ty.unflatten_vec] at hshuffle
  have hcast := initialPair_native block 2 3
  unfold initialPair at hcast
  simp [program.bb2, List.foldlM_cons, List.foldlM_nil, Instr.run,
    initialSlice1Env, pairStoreState, pairScratchStore,
    hp', hq, hk, hgd, hgs, hfd, hfs, hr,
    hshuffle, hcast, pairVec_add,
    pairVec_flatten, UnOp.compute, GepIndex.inboundsOffset, Operation.load, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

def initialSlice2Env (E : Env program.Γ) (data scratch : Pointer) (block : Bytes)
    (k0 k1 : Word) : Env program.Γ :=
  E[%117 := .value (data.add 32#64), %118 := Ty.unflatten (.vec 16 8) (readWordNative block 5 ++ readWordNative block 4), %119 := initialShuffle (readWordNative block 5 ++ readWordNative block 4), %120 := pairVec (readWordBE block 4) (readWordBE block 5), %121 := pairVec (readWordBE block 4+k0) (readWordBE block 5+k1), %122 := .value (scratch.add 32#64)]

theorem initial_slice2_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch : Pointer) (block : Bytes) (k0 k1 : Word)
    (hd : SmallRange mem.mem data 128) (hs : SmallRange mem.mem scratch 128)
    (hp : E.read (%arg1) = .value data) (hq : E.read (%81) = .value scratch)
    (hk : E.read (%13) = pairVec k0 k1)
    (hr : mem.mem.readAt (data.add 32#64) 128 =
      readWordNative block 5 ++ readWordNative block 4) :
    List.foldlM Instr.run E ((program.bb2.body.drop 30).take 7) mem =
      .value (initialSlice2Env E data scratch block k0 k1,
        pairStoreState mem scratch 2 (readWordBE block 4+k0) (readWordBE block 5+k1)) := by
  have hp' : E.args 1 = .value data := hp
  have hgd := hd.gep (k := 32) (by decide)
  have hgs := hs.gep (k := 32) (by decide)
  norm_num only at hgd hgs
  have hfd := hd.fits_add (k := 32) (count := 16) (by decide)
  have hfs := hs.fits_add (k := 32) (count := 16) (by decide)
  try simp only [Pointer.add_zero] at hfd hfs
  have hshuffle := initialShuffle_any
    (readWordNative block 5 ++ readWordNative block 4) (E.read (%10))
  simp only [initialMask, Ty.unflatten_vec] at hshuffle
  have hcast := initialPair_native block 4 5
  unfold initialPair at hcast
  simp [program.bb2, List.foldlM_cons, List.foldlM_nil, Instr.run,
    initialSlice2Env, pairStoreState, pairScratchStore,
    hp', hq, hk, hgd, hgs, hfd, hfs, hr,
    hshuffle, hcast, pairVec_add,
    pairVec_flatten, UnOp.compute, GepIndex.inboundsOffset, Operation.load, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

def initialSlice3Env (E : Env program.Γ) (data scratch : Pointer) (block : Bytes)
    (k0 k1 : Word) : Env program.Γ :=
  E[%123 := .value (data.add 48#64), %124 := Ty.unflatten (.vec 16 8) (readWordNative block 7 ++ readWordNative block 6), %125 := initialShuffle (readWordNative block 7 ++ readWordNative block 6), %126 := pairVec (readWordBE block 6) (readWordBE block 7), %127 := pairVec (readWordBE block 6+k0) (readWordBE block 7+k1), %128 := .value (scratch.add 48#64)]

theorem initial_slice3_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch : Pointer) (block : Bytes) (k0 k1 : Word)
    (hd : SmallRange mem.mem data 128) (hs : SmallRange mem.mem scratch 128)
    (hp : E.read (%arg1) = .value data) (hq : E.read (%81) = .value scratch)
    (hk : E.read (%14) = pairVec k0 k1)
    (hr : mem.mem.readAt (data.add 48#64) 128 =
      readWordNative block 7 ++ readWordNative block 6) :
    List.foldlM Instr.run E ((program.bb2.body.drop 37).take 7) mem =
      .value (initialSlice3Env E data scratch block k0 k1,
        pairStoreState mem scratch 3 (readWordBE block 6+k0) (readWordBE block 7+k1)) := by
  have hp' : E.args 1 = .value data := hp
  have hgd := hd.gep (k := 48) (by decide)
  have hgs := hs.gep (k := 48) (by decide)
  norm_num only at hgd hgs
  have hfd := hd.fits_add (k := 48) (count := 16) (by decide)
  have hfs := hs.fits_add (k := 48) (count := 16) (by decide)
  try simp only [Pointer.add_zero] at hfd hfs
  have hshuffle := initialShuffle_any
    (readWordNative block 7 ++ readWordNative block 6) (E.read (%10))
  simp only [initialMask, Ty.unflatten_vec] at hshuffle
  have hcast := initialPair_native block 6 7
  unfold initialPair at hcast
  simp [program.bb2, List.foldlM_cons, List.foldlM_nil, Instr.run,
    initialSlice3Env, pairStoreState, pairScratchStore,
    hp', hq, hk, hgd, hgs, hfd, hfs, hr,
    hshuffle, hcast, pairVec_add,
    pairVec_flatten, UnOp.compute, GepIndex.inboundsOffset, Operation.load, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

def initialSlice4Env (E : Env program.Γ) (data scratch : Pointer) (block : Bytes)
    (k0 k1 : Word) : Env program.Γ :=
  E[%129 := .value (data.add 64#64), %130 := Ty.unflatten (.vec 16 8) (readWordNative block 9 ++ readWordNative block 8), %131 := initialShuffle (readWordNative block 9 ++ readWordNative block 8), %132 := pairVec (readWordBE block 8) (readWordBE block 9), %133 := pairVec (readWordBE block 8+k0) (readWordBE block 9+k1), %134 := .value (scratch.add 64#64)]

theorem initial_slice4_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch : Pointer) (block : Bytes) (k0 k1 : Word)
    (hd : SmallRange mem.mem data 128) (hs : SmallRange mem.mem scratch 128)
    (hp : E.read (%arg1) = .value data) (hq : E.read (%81) = .value scratch)
    (hk : E.read (%16) = pairVec k0 k1)
    (hr : mem.mem.readAt (data.add 64#64) 128 =
      readWordNative block 9 ++ readWordNative block 8) :
    List.foldlM Instr.run E ((program.bb2.body.drop 44).take 7) mem =
      .value (initialSlice4Env E data scratch block k0 k1,
        pairStoreState mem scratch 4 (readWordBE block 8+k0) (readWordBE block 9+k1)) := by
  have hp' : E.args 1 = .value data := hp
  have hgd := hd.gep (k := 64) (by decide)
  have hgs := hs.gep (k := 64) (by decide)
  norm_num only at hgd hgs
  have hfd := hd.fits_add (k := 64) (count := 16) (by decide)
  have hfs := hs.fits_add (k := 64) (count := 16) (by decide)
  try simp only [Pointer.add_zero] at hfd hfs
  have hshuffle := initialShuffle_any
    (readWordNative block 9 ++ readWordNative block 8) (E.read (%10))
  simp only [initialMask, Ty.unflatten_vec] at hshuffle
  have hcast := initialPair_native block 8 9
  unfold initialPair at hcast
  simp [program.bb2, List.foldlM_cons, List.foldlM_nil, Instr.run,
    initialSlice4Env, pairStoreState, pairScratchStore,
    hp', hq, hk, hgd, hgs, hfd, hfs, hr,
    hshuffle, hcast, pairVec_add,
    pairVec_flatten, UnOp.compute, GepIndex.inboundsOffset, Operation.load, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

def initialSlice5Env (E : Env program.Γ) (data scratch : Pointer) (block : Bytes)
    (k0 k1 : Word) : Env program.Γ :=
  E[%135 := .value (data.add 80#64), %136 := Ty.unflatten (.vec 16 8) (readWordNative block 11 ++ readWordNative block 10), %137 := initialShuffle (readWordNative block 11 ++ readWordNative block 10), %138 := pairVec (readWordBE block 10) (readWordBE block 11), %139 := pairVec (readWordBE block 10+k0) (readWordBE block 11+k1), %140 := .value (scratch.add 80#64)]

theorem initial_slice5_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch : Pointer) (block : Bytes) (k0 k1 : Word)
    (hd : SmallRange mem.mem data 128) (hs : SmallRange mem.mem scratch 128)
    (hp : E.read (%arg1) = .value data) (hq : E.read (%81) = .value scratch)
    (hk : E.read (%18) = pairVec k0 k1)
    (hr : mem.mem.readAt (data.add 80#64) 128 =
      readWordNative block 11 ++ readWordNative block 10) :
    List.foldlM Instr.run E ((program.bb2.body.drop 51).take 7) mem =
      .value (initialSlice5Env E data scratch block k0 k1,
        pairStoreState mem scratch 5 (readWordBE block 10+k0) (readWordBE block 11+k1)) := by
  have hp' : E.args 1 = .value data := hp
  have hgd := hd.gep (k := 80) (by decide)
  have hgs := hs.gep (k := 80) (by decide)
  norm_num only at hgd hgs
  have hfd := hd.fits_add (k := 80) (count := 16) (by decide)
  have hfs := hs.fits_add (k := 80) (count := 16) (by decide)
  try simp only [Pointer.add_zero] at hfd hfs
  have hshuffle := initialShuffle_any
    (readWordNative block 11 ++ readWordNative block 10) (E.read (%10))
  simp only [initialMask, Ty.unflatten_vec] at hshuffle
  have hcast := initialPair_native block 10 11
  unfold initialPair at hcast
  simp [program.bb2, List.foldlM_cons, List.foldlM_nil, Instr.run,
    initialSlice5Env, pairStoreState, pairScratchStore,
    hp', hq, hk, hgd, hgs, hfd, hfs, hr,
    hshuffle, hcast, pairVec_add,
    pairVec_flatten, UnOp.compute, GepIndex.inboundsOffset, Operation.load, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

def initialSlice6Env (E : Env program.Γ) (data scratch : Pointer) (block : Bytes)
    (k0 k1 : Word) : Env program.Γ :=
  E[%141 := .value (data.add 96#64), %142 := Ty.unflatten (.vec 16 8) (readWordNative block 13 ++ readWordNative block 12), %143 := initialShuffle (readWordNative block 13 ++ readWordNative block 12), %144 := pairVec (readWordBE block 12) (readWordBE block 13), %145 := pairVec (readWordBE block 12+k0) (readWordBE block 13+k1), %146 := .value (scratch.add 96#64)]

theorem initial_slice6_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch : Pointer) (block : Bytes) (k0 k1 : Word)
    (hd : SmallRange mem.mem data 128) (hs : SmallRange mem.mem scratch 128)
    (hp : E.read (%arg1) = .value data) (hq : E.read (%81) = .value scratch)
    (hk : E.read (%20) = pairVec k0 k1)
    (hr : mem.mem.readAt (data.add 96#64) 128 =
      readWordNative block 13 ++ readWordNative block 12) :
    List.foldlM Instr.run E ((program.bb2.body.drop 58).take 7) mem =
      .value (initialSlice6Env E data scratch block k0 k1,
        pairStoreState mem scratch 6 (readWordBE block 12+k0) (readWordBE block 13+k1)) := by
  have hp' : E.args 1 = .value data := hp
  have hgd := hd.gep (k := 96) (by decide)
  have hgs := hs.gep (k := 96) (by decide)
  norm_num only at hgd hgs
  have hfd := hd.fits_add (k := 96) (count := 16) (by decide)
  have hfs := hs.fits_add (k := 96) (count := 16) (by decide)
  try simp only [Pointer.add_zero] at hfd hfs
  have hshuffle := initialShuffle_any
    (readWordNative block 13 ++ readWordNative block 12) (E.read (%10))
  simp only [initialMask, Ty.unflatten_vec] at hshuffle
  have hcast := initialPair_native block 12 13
  unfold initialPair at hcast
  simp [program.bb2, List.foldlM_cons, List.foldlM_nil, Instr.run,
    initialSlice6Env, pairStoreState, pairScratchStore,
    hp', hq, hk, hgd, hgs, hfd, hfs, hr,
    hshuffle, hcast, pairVec_add,
    pairVec_flatten, UnOp.compute, GepIndex.inboundsOffset, Operation.load, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

def initialSlice7Env (E : Env program.Γ) (data scratch : Pointer) (block : Bytes)
    (k0 k1 : Word) : Env program.Γ :=
  E[%147 := .value (data.add 112#64), %148 := Ty.unflatten (.vec 16 8) (readWordNative block 15 ++ readWordNative block 14), %149 := initialShuffle (readWordNative block 15 ++ readWordNative block 14), %150 := pairVec (readWordBE block 14) (readWordBE block 15), %151 := pairVec (readWordBE block 14+k0) (readWordBE block 15+k1), %152 := .value (scratch.add 112#64)]

theorem initial_slice7_body (E : Env program.Γ) (mem : GlobalState)
    (data scratch : Pointer) (block : Bytes) (k0 k1 : Word)
    (hd : SmallRange mem.mem data 128) (hs : SmallRange mem.mem scratch 128)
    (hp : E.read (%arg1) = .value data) (hq : E.read (%81) = .value scratch)
    (hk : E.read (%22) = pairVec k0 k1)
    (hr : mem.mem.readAt (data.add 112#64) 128 =
      readWordNative block 15 ++ readWordNative block 14) :
    List.foldlM Instr.run E ((program.bb2.body.drop 65).take 7) mem =
      .value (initialSlice7Env E data scratch block k0 k1,
        pairStoreState mem scratch 7 (readWordBE block 14+k0) (readWordBE block 15+k1)) := by
  have hp' : E.args 1 = .value data := hp
  have hgd := hd.gep (k := 112) (by decide)
  have hgs := hs.gep (k := 112) (by decide)
  norm_num only at hgd hgs
  have hfd := hd.fits_add (k := 112) (count := 16) (by decide)
  have hfs := hs.fits_add (k := 112) (count := 16) (by decide)
  try simp only [Pointer.add_zero] at hfd hfs
  have hshuffle := initialShuffle_any
    (readWordNative block 15 ++ readWordNative block 14) (E.read (%10))
  simp only [initialMask, Ty.unflatten_vec] at hshuffle
  have hcast := initialPair_native block 14 15
  unfold initialPair at hcast
  simp [program.bb2, List.foldlM_cons, List.foldlM_nil, Instr.run,
    initialSlice7Env, pairStoreState, pairScratchStore,
    hp', hq, hk, hgd, hgs, hfd, hfs, hr,
    hshuffle, hcast, pairVec_add,
    pairVec_flatten, UnOp.compute, GepIndex.inboundsOffset, Operation.load, Operation.store,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

end Agave.Ed25519.SHA512.Execution.Avx2
