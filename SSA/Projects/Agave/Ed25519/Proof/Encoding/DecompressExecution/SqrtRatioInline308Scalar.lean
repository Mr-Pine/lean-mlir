import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline308Packing

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem frame_trans (E F G : Env program.Γ) (h : Frame E F lo) (k : Frame F G lo) :
    Frame E G lo := ⟨k.1.trans h.1, fun i hi => (k.2 i hi).trans (h.2 i hi)⟩

theorem frame_mono (E F : Env program.Γ) (h : Frame E F lo) (hn : n ≤ lo) :
    Frame E F n := ⟨h.1, fun i hi => h.2 i (Nat.lt_of_lt_of_le hi hn)⟩

theorem frame_arg (E F : Env program.Γ) (h : Frame E F lo)
    (i : Fin program.Γ.args.length) (ht : program.Γ.args[i] = t) :
    F.read (.arg i ht) = E.read (.arg i ht) := by
  cases ht
  exact congrFun h.1 i

def pointerRegister : Fin 32 → Reg program.Γ .ptr :=
  ![(%64), (%269), (%270), (%271), (%272), (%273), (%274), (%275), (%276), (%277), (%278), (%279), (%280), (%281), (%282), (%283), (%284), (%285), (%286), (%287), (%288), (%289), (%290), (%291), (%292), (%293), (%294), (%295), (%296), (%297), (%298), (%299)]

def Pointers (E : Env program.Γ) (right : Pointer) : Prop :=
  ∀ i, E.read (pointerRegister i) = .value (right.add (BitVec.ofNat 64 i.val))

def scalarEnv (E : Env program.Γ) (x : Words) : Env program.Γ :=
  packingEnv15 (packingEnv14 (packingEnv13 (packingEnv12 (packingEnv11 (packingEnv10 (packingEnv9 (packingEnv8 (packingEnv7 (packingEnv6 (packingEnv5 (packingEnv4 (packingEnv3 (packingEnv2 (packingEnv1 (packingEnv0 (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x

def scalarState (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  packingState15 (packingState14 (packingState13 (packingState12 (packingState11 (packingState10 (packingState9 (packingState8 (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x

theorem scalar_state (s : GlobalState) (right : Pointer) (x : Words) :
    scalarState s right x = {s with mem := ToBytes.storeBytes s.mem right (ToBytes.machine x)} := by
  rw [← outputBytes_machine]
  simp only [scalarState, packingState0, packingState1, packingState2, packingState3, packingState4, packingState5, packingState6, packingState7, packingState8, packingState9, packingState10, packingState11, packingState12, packingState13, packingState14, packingState15, ToBytes.storeBytes,
    outputBytes, Pointer.add_zero]
  rfl

theorem scalar_frame (E : Env program.Γ) (x : Words) : Frame E (scalarEnv E x) 314 := by
  unfold scalarEnv
  apply frame_trans _ _ _ ?_ (frame_mono (n := 314) _ _ (packing_frame15 _ x) (by decide))
  apply frame_trans _ _ _ ?_ (frame_mono (n := 314) _ _ (packing_frame14 _ x) (by decide))
  apply frame_trans _ _ _ ?_ (frame_mono (n := 314) _ _ (packing_frame13 _ x) (by decide))
  apply frame_trans _ _ _ ?_ (frame_mono (n := 314) _ _ (packing_frame12 _ x) (by decide))
  apply frame_trans _ _ _ ?_ (frame_mono (n := 314) _ _ (packing_frame11 _ x) (by decide))
  apply frame_trans _ _ _ ?_ (frame_mono (n := 314) _ _ (packing_frame10 _ x) (by decide))
  apply frame_trans _ _ _ ?_ (frame_mono (n := 314) _ _ (packing_frame9 _ x) (by decide))
  apply frame_trans _ _ _ ?_ (frame_mono (n := 314) _ _ (packing_frame8 _ x) (by decide))
  apply frame_trans _ _ _ ?_ (frame_mono (n := 314) _ _ (packing_frame7 _ x) (by decide))
  apply frame_trans _ _ _ ?_ (frame_mono (n := 314) _ _ (packing_frame6 _ x) (by decide))
  apply frame_trans _ _ _ ?_ (frame_mono (n := 314) _ _ (packing_frame5 _ x) (by decide))
  apply frame_trans _ _ _ ?_ (frame_mono (n := 314) _ _ (packing_frame4 _ x) (by decide))
  apply frame_trans _ _ _ ?_ (frame_mono (n := 314) _ _ (packing_frame3 _ x) (by decide))
  apply frame_trans _ _ _ ?_ (frame_mono (n := 314) _ _ (packing_frame2 _ x) (by decide))
  apply frame_trans _ _ _ ?_ (frame_mono (n := 314) _ _ (packing_frame1 _ x) (by decide))
  apply frame_trans _ _ _ ?_ (frame_mono (n := 314) _ _ (packing_frame0 _ x) (by decide))
  apply frame_trans _ _ _ ?_ (arithmetic_frame8 _ x)
  apply frame_trans _ _ _ ?_ (arithmetic_frame7 _ x)
  apply frame_trans _ _ _ ?_ (arithmetic_frame6 _ x)
  apply frame_trans _ _ _ ?_ (arithmetic_frame5 _ x)
  apply frame_trans _ _ _ ?_ (arithmetic_frame4 _ x)
  apply frame_trans _ _ _ ?_ (arithmetic_frame3 _ x)
  apply frame_trans _ _ _ ?_ (arithmetic_frame2 _ x)
  apply frame_trans _ _ _ ?_ (arithmetic_frame1 _ x)
  apply frame_trans _ _ _ ?_ (arithmetic_frame0 _ x)
  exact frame_refl E _

theorem scalar_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32) (hc : Constants E) (hp : Pointers E right)
    (e312 : E.read (%312) = .value (x 0))
    (e313 : E.read (%313) = Ty.wrap #v[x 1, x 2, x 3, x 4]) :
    Cutpoint.segment (program p g) 0 421 148 E s =
      .value (scalarEnv E x, scalarState s right x) := by
  have e1 := hc.c1
  have e3 := hc.c3
  have e4 := hc.c4
  have e5 := hc.c5
  have e6 := hc.c6
  have e7 := hc.c7
  have e8 := hc.c8
  have e9 := hc.c9
  have e10 := hc.c10
  have e11 := hc.c11
  have e12 := hc.c12
  have e13 := hc.c13
  have e14 := hc.c14
  have e15 := hc.c15
  have e16 := hc.c16
  have e17 := hc.c17
  have e18 := hc.c18
  have e19 := hc.c19
  have e20 := hc.c20
  have e21 := hc.c21
  have e22 := hc.c22
  have e23 := hc.c23
  have e24 := hc.c24
  have e25 := hc.c25
  have e26 := hc.c26
  have e27 := hc.c27
  have e28 := hc.c28
  have e29 := hc.c29
  have e30 := hc.c30
  have e31 := hc.c31
  have e32 := hc.c32
  have e33 := hc.c33
  have e34 := hc.c34
  have e35 := hc.c35
  have e36 := hc.c36
  have e37 := hc.c37
  have e38 := hc.c38
  have e39 := hc.c39
  have e40 := hc.c40
  have e41 := hc.c41
  have e42 := hc.c42
  have e43 := hc.c43
  have e44 := hc.c44
  have e45 := hc.c45
  have e46 := hc.c46
  have e50 := hc.c50
  have e54 := hc.c54
  have e59 := hc.c59
  have e47 := hc.c47
  have e48 := hc.c48
  have e49 := hc.c49
  have e51 := hc.c51
  have e64 : E.read (%64) = .value right := by
    have h : E.read (%64) = .value (right.add 0#64) := hp 0
    simpa only [Pointer.add_zero] using h
  have e269 : E.read (%269) = .value (right.add 1#64) := hp 1
  have e270 : E.read (%270) = .value (right.add 2#64) := hp 2
  have e271 : E.read (%271) = .value (right.add 3#64) := hp 3
  have e272 : E.read (%272) = .value (right.add 4#64) := hp 4
  have e273 : E.read (%273) = .value (right.add 5#64) := hp 5
  have e274 : E.read (%274) = .value (right.add 6#64) := hp 6
  have e275 : E.read (%275) = .value (right.add 7#64) := hp 7
  have e276 : E.read (%276) = .value (right.add 8#64) := hp 8
  have e277 : E.read (%277) = .value (right.add 9#64) := hp 9
  have e278 : E.read (%278) = .value (right.add 10#64) := hp 10
  have e279 : E.read (%279) = .value (right.add 11#64) := hp 11
  have e280 : E.read (%280) = .value (right.add 12#64) := hp 12
  have e281 : E.read (%281) = .value (right.add 13#64) := hp 13
  have e282 : E.read (%282) = .value (right.add 14#64) := hp 14
  have e283 : E.read (%283) = .value (right.add 15#64) := hp 15
  have e284 : E.read (%284) = .value (right.add 16#64) := hp 16
  have e285 : E.read (%285) = .value (right.add 17#64) := hp 17
  have e286 : E.read (%286) = .value (right.add 18#64) := hp 18
  have e287 : E.read (%287) = .value (right.add 19#64) := hp 19
  have e288 : E.read (%288) = .value (right.add 20#64) := hp 20
  have e289 : E.read (%289) = .value (right.add 21#64) := hp 21
  have e290 : E.read (%290) = .value (right.add 22#64) := hp 22
  have e291 : E.read (%291) = .value (right.add 23#64) := hp 23
  have e292 : E.read (%292) = .value (right.add 24#64) := hp 24
  have e293 : E.read (%293) = .value (right.add 25#64) := hp 25
  have e294 : E.read (%294) = .value (right.add 26#64) := hp 26
  have e295 : E.read (%295) = .value (right.add 27#64) := hp 27
  have e296 : E.read (%296) = .value (right.add 28#64) := hp 28
  have e297 : E.read (%297) = .value (right.add 29#64) := hp 29
  have e298 : E.read (%298) = .value (right.add 30#64) := hp 30
  have e299 : E.read (%299) = .value (right.add 31#64) := hp 31
  have h0 := arithmetic_segment0 p g (E) (s) x
    (by simp (disch := decide) only [mlir_env, e7, e10, e50, e312, e313])
    (by simp (disch := decide) only [mlir_env, e7, e10, e50, e312, e313])
    (by simp (disch := decide) only [mlir_env, e7, e10, e50, e312, e313])
    (by simp (disch := decide) only [mlir_env, e7, e10, e50, e312, e313])
    (by simp (disch := decide) only [mlir_env, e7, e10, e50, e312, e313])
  have h1 := arithmetic_segment1 p g (arithmeticEnv0 (E) x) (s) x
    (by simp (disch := decide) only [arithmeticEnv0, mlir_env, e7, e8, e11, e12, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, mlir_env, e7, e8, e11, e12, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, mlir_env, e7, e8, e11, e12, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, mlir_env, e7, e8, e11, e12, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, mlir_env, e7, e8, e11, e12, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, mlir_env, e7, e8, e11, e12, e312, e313])
  have h2 := arithmetic_segment2 p g (arithmeticEnv1 (arithmeticEnv0 (E) x) x) (s) x
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, mlir_env, e8, e9, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, mlir_env, e8, e9, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, mlir_env, e8, e9, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, mlir_env, e8, e9, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, mlir_env, e8, e9, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, mlir_env, e8, e9, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, mlir_env, e8, e9, e312, e313])
  have h3 := arithmetic_segment3 p g (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) (s) x
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, mlir_env, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, mlir_env, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, mlir_env, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, mlir_env, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, mlir_env, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, mlir_env, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, mlir_env, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, mlir_env, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, mlir_env, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, mlir_env, e312, e313])
  have h4 := arithmetic_segment4 p g (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) (s) x
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, mlir_env, e7, e9, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, mlir_env, e7, e9, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, mlir_env, e7, e9, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, mlir_env, e7, e9, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, mlir_env, e7, e9, e312, e313])
  have h5 := arithmetic_segment5 p g (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) (s) x
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, mlir_env, e7, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, mlir_env, e7, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, mlir_env, e7, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, mlir_env, e7, e312, e313])
  have h6 := arithmetic_segment6 p g (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) (s) x
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, mlir_env, e7, e9, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, mlir_env, e7, e9, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, mlir_env, e7, e9, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, mlir_env, e7, e9, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, mlir_env, e7, e9, e312, e313])
  have h7 := arithmetic_segment7 p g (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) (s) x
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, mlir_env, e7, e8, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, mlir_env, e7, e8, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, mlir_env, e7, e8, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, mlir_env, e7, e8, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, mlir_env, e7, e8, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, mlir_env, e7, e8, e312, e313])
  have h8 := arithmetic_segment8 p g (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) (s) x
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, mlir_env, e7, e8, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, mlir_env, e7, e8, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, mlir_env, e7, e8, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, mlir_env, e7, e8, e312, e313])
  have hr9 : SmallRange (s).mem right 32 := by
    repeat apply SmallRange.storeAt
    exact hr
  have h9 := packing_segment0 p g (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) (s) right x hr9
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, mlir_env, e3, e64, e269, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, mlir_env, e3, e64, e269, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, mlir_env, e3, e64, e269, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, mlir_env, e3, e64, e269, e312, e313])
  have hr10 : SmallRange (packingState0 (s) right x).mem right 32 := by
    simp only [packingState0]
    repeat apply SmallRange.storeAt
    exact hr
  have h10 := packing_segment1 p g (packingEnv0 (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) x) (packingState0 (s) right x) right x hr10
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, mlir_env, e4, e5, e270, e271, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, mlir_env, e4, e5, e270, e271, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, mlir_env, e4, e5, e270, e271, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, mlir_env, e4, e5, e270, e271, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, mlir_env, e4, e5, e270, e271, e312, e313])
  have hr11 : SmallRange (packingState1 (packingState0 (s) right x) right x).mem right 32 := by
    simp only [packingState0, packingState1]
    repeat apply SmallRange.storeAt
    exact hr
  have h11 := packing_segment2 p g (packingEnv1 (packingEnv0 (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) x) x) (packingState1 (packingState0 (s) right x) right x) right x hr11
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, mlir_env, e1, e6, e272, e273, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, mlir_env, e1, e6, e272, e273, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, mlir_env, e1, e6, e272, e273, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, mlir_env, e1, e6, e272, e273, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, mlir_env, e1, e6, e272, e273, e312, e313])
  have hr12 : SmallRange (packingState2 (packingState1 (packingState0 (s) right x) right x) right x).mem right 32 := by
    simp only [packingState0, packingState1, packingState2]
    repeat apply SmallRange.storeAt
    exact hr
  have h12 := packing_segment3 p g (packingEnv2 (packingEnv1 (packingEnv0 (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) x) x) x) (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x hr12
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, mlir_env, e12, e14, e15, e16, e274, e275, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, mlir_env, e12, e14, e15, e16, e274, e275, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, mlir_env, e12, e14, e15, e16, e274, e275, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, mlir_env, e12, e14, e15, e16, e274, e275, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, mlir_env, e12, e14, e15, e16, e274, e275, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, mlir_env, e12, e14, e15, e16, e274, e275, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, mlir_env, e12, e14, e15, e16, e274, e275, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, mlir_env, e12, e14, e15, e16, e274, e275, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, mlir_env, e12, e14, e15, e16, e274, e275, e312, e313])
  have hr13 : SmallRange (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x).mem right 32 := by
    simp only [packingState0, packingState1, packingState2, packingState3]
    repeat apply SmallRange.storeAt
    exact hr
  have h13 := packing_segment4 p g (packingEnv3 (packingEnv2 (packingEnv1 (packingEnv0 (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) x) x) x) x) (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x hr13
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, mlir_env, e18, e19, e276, e277, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, mlir_env, e18, e19, e276, e277, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, mlir_env, e18, e19, e276, e277, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, mlir_env, e18, e19, e276, e277, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, mlir_env, e18, e19, e276, e277, e312, e313])
  have hr14 : SmallRange (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x).mem right 32 := by
    simp only [packingState0, packingState1, packingState2, packingState3, packingState4]
    repeat apply SmallRange.storeAt
    exact hr
  have h14 := packing_segment5 p g (packingEnv4 (packingEnv3 (packingEnv2 (packingEnv1 (packingEnv0 (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) x) x) x) x) x) (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x hr14
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, mlir_env, e21, e23, e278, e279, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, mlir_env, e21, e23, e278, e279, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, mlir_env, e21, e23, e278, e279, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, mlir_env, e21, e23, e278, e279, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, mlir_env, e21, e23, e278, e279, e312, e313])
  have hr15 : SmallRange (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x).mem right 32 := by
    simp only [packingState0, packingState1, packingState2, packingState3, packingState4, packingState5]
    repeat apply SmallRange.storeAt
    exact hr
  have h15 := packing_segment6 p g (packingEnv5 (packingEnv4 (packingEnv3 (packingEnv2 (packingEnv1 (packingEnv0 (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x hr15
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, mlir_env, e11, e17, e25, e280, e281, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, mlir_env, e11, e17, e25, e280, e281, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, mlir_env, e11, e17, e25, e280, e281, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, mlir_env, e11, e17, e25, e280, e281, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, mlir_env, e11, e17, e25, e280, e281, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, mlir_env, e11, e17, e25, e280, e281, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, mlir_env, e11, e17, e25, e280, e281, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, mlir_env, e11, e17, e25, e280, e281, e312, e313])
  have hr16 : SmallRange (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x).mem right 32 := by
    simp only [packingState0, packingState1, packingState2, packingState3, packingState4, packingState5, packingState6]
    repeat apply SmallRange.storeAt
    exact hr
  have h16 := packing_segment7 p g (packingEnv6 (packingEnv5 (packingEnv4 (packingEnv3 (packingEnv2 (packingEnv1 (packingEnv0 (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x hr16
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, mlir_env, e22, e28, e282, e283, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, mlir_env, e22, e28, e282, e283, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, mlir_env, e22, e28, e282, e283, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, mlir_env, e22, e28, e282, e283, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, mlir_env, e22, e28, e282, e283, e312, e313])
  have hr17 : SmallRange (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x).mem right 32 := by
    simp only [packingState0, packingState1, packingState2, packingState3, packingState4, packingState5, packingState6, packingState7]
    repeat apply SmallRange.storeAt
    exact hr
  have h17 := packing_segment8 p g (packingEnv7 (packingEnv6 (packingEnv5 (packingEnv4 (packingEnv3 (packingEnv2 (packingEnv1 (packingEnv0 (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x) right x hr17
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, mlir_env, e30, e31, e284, e285, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, mlir_env, e30, e31, e284, e285, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, mlir_env, e30, e31, e284, e285, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, mlir_env, e30, e31, e284, e285, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, mlir_env, e30, e31, e284, e285, e312, e313])
  have hr18 : SmallRange (packingState8 (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x) right x).mem right 32 := by
    simp only [packingState0, packingState1, packingState2, packingState3, packingState4, packingState5, packingState6, packingState7, packingState8]
    repeat apply SmallRange.storeAt
    exact hr
  have h18 := packing_segment9 p g (packingEnv8 (packingEnv7 (packingEnv6 (packingEnv5 (packingEnv4 (packingEnv3 (packingEnv2 (packingEnv1 (packingEnv0 (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) (packingState8 (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x hr18
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, mlir_env, e10, e33, e34, e286, e287, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, mlir_env, e10, e33, e34, e286, e287, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, mlir_env, e10, e33, e34, e286, e287, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, mlir_env, e10, e33, e34, e286, e287, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, mlir_env, e10, e33, e34, e286, e287, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, mlir_env, e10, e33, e34, e286, e287, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, mlir_env, e10, e33, e34, e286, e287, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, mlir_env, e10, e33, e34, e286, e287, e312, e313])
  have hr19 : SmallRange (packingState9 (packingState8 (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x).mem right 32 := by
    simp only [packingState0, packingState1, packingState2, packingState3, packingState4, packingState5, packingState6, packingState7, packingState8, packingState9]
    repeat apply SmallRange.storeAt
    exact hr
  have h19 := packing_segment10 p g (packingEnv9 (packingEnv8 (packingEnv7 (packingEnv6 (packingEnv5 (packingEnv4 (packingEnv3 (packingEnv2 (packingEnv1 (packingEnv0 (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) (packingState9 (packingState8 (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x hr19
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, mlir_env, e16, e29, e288, e289, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, mlir_env, e16, e29, e288, e289, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, mlir_env, e16, e29, e288, e289, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, mlir_env, e16, e29, e288, e289, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, mlir_env, e16, e29, e288, e289, e312, e313])
  have hr20 : SmallRange (packingState10 (packingState9 (packingState8 (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x).mem right 32 := by
    simp only [packingState0, packingState1, packingState2, packingState3, packingState4, packingState5, packingState6, packingState7, packingState8, packingState9, packingState10]
    repeat apply SmallRange.storeAt
    exact hr
  have h20 := packing_segment11 p g (packingEnv10 (packingEnv9 (packingEnv8 (packingEnv7 (packingEnv6 (packingEnv5 (packingEnv4 (packingEnv3 (packingEnv2 (packingEnv1 (packingEnv0 (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) (packingState10 (packingState9 (packingState8 (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x hr20
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, mlir_env, e36, e38, e290, e291, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, mlir_env, e36, e38, e290, e291, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, mlir_env, e36, e38, e290, e291, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, mlir_env, e36, e38, e290, e291, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, mlir_env, e36, e38, e290, e291, e312, e313])
  have hr21 : SmallRange (packingState11 (packingState10 (packingState9 (packingState8 (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x).mem right 32 := by
    simp only [packingState0, packingState1, packingState2, packingState3, packingState4, packingState5, packingState6, packingState7, packingState8, packingState9, packingState10, packingState11]
    repeat apply SmallRange.storeAt
    exact hr
  have h21 := packing_segment12 p g (packingEnv11 (packingEnv10 (packingEnv9 (packingEnv8 (packingEnv7 (packingEnv6 (packingEnv5 (packingEnv4 (packingEnv3 (packingEnv2 (packingEnv1 (packingEnv0 (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) (packingState11 (packingState10 (packingState9 (packingState8 (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x hr21
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, mlir_env, e13, e39, e40, e292, e293, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, mlir_env, e13, e39, e40, e292, e293, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, mlir_env, e13, e39, e40, e292, e293, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, mlir_env, e13, e39, e40, e292, e293, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, mlir_env, e13, e39, e40, e292, e293, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, mlir_env, e13, e39, e40, e292, e293, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, mlir_env, e13, e39, e40, e292, e293, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, mlir_env, e13, e39, e40, e292, e293, e312, e313])
  have hr22 : SmallRange (packingState12 (packingState11 (packingState10 (packingState9 (packingState8 (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x).mem right 32 := by
    simp only [packingState0, packingState1, packingState2, packingState3, packingState4, packingState5, packingState6, packingState7, packingState8, packingState9, packingState10, packingState11, packingState12]
    repeat apply SmallRange.storeAt
    exact hr
  have h22 := packing_segment13 p g (packingEnv12 (packingEnv11 (packingEnv10 (packingEnv9 (packingEnv8 (packingEnv7 (packingEnv6 (packingEnv5 (packingEnv4 (packingEnv3 (packingEnv2 (packingEnv1 (packingEnv0 (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) (packingState12 (packingState11 (packingState10 (packingState9 (packingState8 (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x hr22
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, packingEnv12, mlir_env, e13, e26, e294, e295, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, packingEnv12, mlir_env, e13, e26, e294, e295, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, packingEnv12, mlir_env, e13, e26, e294, e295, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, packingEnv12, mlir_env, e13, e26, e294, e295, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, packingEnv12, mlir_env, e13, e26, e294, e295, e312, e313])
  have hr23 : SmallRange (packingState13 (packingState12 (packingState11 (packingState10 (packingState9 (packingState8 (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x).mem right 32 := by
    simp only [packingState0, packingState1, packingState2, packingState3, packingState4, packingState5, packingState6, packingState7, packingState8, packingState9, packingState10, packingState11, packingState12, packingState13]
    repeat apply SmallRange.storeAt
    exact hr
  have h23 := packing_segment14 p g (packingEnv13 (packingEnv12 (packingEnv11 (packingEnv10 (packingEnv9 (packingEnv8 (packingEnv7 (packingEnv6 (packingEnv5 (packingEnv4 (packingEnv3 (packingEnv2 (packingEnv1 (packingEnv0 (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) (packingState13 (packingState12 (packingState11 (packingState10 (packingState9 (packingState8 (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x hr23
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, packingEnv12, packingEnv13, mlir_env, e35, e43, e296, e297, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, packingEnv12, packingEnv13, mlir_env, e35, e43, e296, e297, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, packingEnv12, packingEnv13, mlir_env, e35, e43, e296, e297, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, packingEnv12, packingEnv13, mlir_env, e35, e43, e296, e297, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, packingEnv12, packingEnv13, mlir_env, e35, e43, e296, e297, e312, e313])
  have hr24 : SmallRange (packingState14 (packingState13 (packingState12 (packingState11 (packingState10 (packingState9 (packingState8 (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x).mem right 32 := by
    simp only [packingState0, packingState1, packingState2, packingState3, packingState4, packingState5, packingState6, packingState7, packingState8, packingState9, packingState10, packingState11, packingState12, packingState13, packingState14]
    repeat apply SmallRange.storeAt
    exact hr
  have h24 := packing_segment15 p g (packingEnv14 (packingEnv13 (packingEnv12 (packingEnv11 (packingEnv10 (packingEnv9 (packingEnv8 (packingEnv7 (packingEnv6 (packingEnv5 (packingEnv4 (packingEnv3 (packingEnv2 (packingEnv1 (packingEnv0 (arithmeticEnv8 (arithmeticEnv7 (arithmeticEnv6 (arithmeticEnv5 (arithmeticEnv4 (arithmeticEnv3 (arithmeticEnv2 (arithmeticEnv1 (arithmeticEnv0 (E) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) x) (packingState14 (packingState13 (packingState12 (packingState11 (packingState10 (packingState9 (packingState8 (packingState7 (packingState6 (packingState5 (packingState4 (packingState3 (packingState2 (packingState1 (packingState0 (s) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x) right x hr24
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, packingEnv12, packingEnv13, packingEnv14, mlir_env, e44, e46, e298, e299, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, packingEnv12, packingEnv13, packingEnv14, mlir_env, e44, e46, e298, e299, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, packingEnv12, packingEnv13, packingEnv14, mlir_env, e44, e46, e298, e299, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, packingEnv12, packingEnv13, packingEnv14, mlir_env, e44, e46, e298, e299, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, packingEnv12, packingEnv13, packingEnv14, mlir_env, e44, e46, e298, e299, e312, e313])
    (by simp (disch := decide) only [arithmeticEnv0, arithmeticEnv1, arithmeticEnv2, arithmeticEnv3, arithmeticEnv4, arithmeticEnv5, arithmeticEnv6, arithmeticEnv7, arithmeticEnv8, packingEnv0, packingEnv1, packingEnv2, packingEnv3, packingEnv4, packingEnv5, packingEnv6, packingEnv7, packingEnv8, packingEnv9, packingEnv10, packingEnv11, packingEnv12, packingEnv13, packingEnv14, mlir_env, e44, e46, e298, e299, e312, e313])
  unfold scalarEnv scalarState
  rw [show 148 = 5 + 143 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h0, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 143 = 5 + 138 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h1, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 138 = 5 + 133 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h2, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 133 = 5 + 128 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h3, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 128 = 5 + 123 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h4, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 123 = 5 + 118 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h5, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 118 = 5 + 113 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h6, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 113 = 5 + 108 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h7, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 108 = 4 + 104 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h8, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 104 = 5 + 99 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h9, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 99 = 6 + 93 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h10, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 93 = 6 + 87 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h11, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 87 = 9 + 78 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h12, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 78 = 6 + 72 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h13, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 72 = 6 + 66 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h14, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 66 = 8 + 58 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h15, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 58 = 6 + 52 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h16, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 52 = 6 + 46 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h17, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 46 = 8 + 38 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h18, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 38 = 6 + 32 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h19, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 32 = 6 + 26 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h20, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 26 = 8 + 18 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h21, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 18 = 6 + 12 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h22, PoisonOr.value_bind, Nat.reduceAdd]
  rw [show 12 = 6 + 6 from rfl, Inline.segment_append]
  simp only [EffectM.bind_eq, h23, PoisonOr.value_bind, Nat.reduceAdd]
  exact h24

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
