import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline577Loads
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline577Frame

/-! Explicit live constants and pointers at pc577. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577
open LeanMLIR.RIR SerialFieldMul SerializerFrame
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000

structure Constants (E : Env program.Γ) : Prop where
  c1 : E.read (%1) = .value 40#64
  c3 : E.read (%3) = .value 8#64
  c4 : E.read (%4) = .value 16#64
  c5 : E.read (%5) = .value 24#64
  c6 : E.read (%6) = .value 32#64
  c7 : E.read (%7) = .value 51#64
  c8 : E.read (%8) = .value 2251799813685247#64
  c9 : E.read (%9) = .value 19#64
  c10 : E.read (%10) = .value 1#64
  c11 : E.read (%11) = .value 2#64
  c12 : E.read (%12) = .value 3#64
  c13 : E.read (%13) = .value 4#64
  c14 : E.read (%14) = .value 5#64
  c15 : E.read (%15) = .value 48#64
  c16 : E.read (%16) = .value 7#64
  c17 : E.read (%17) = .value 6#64
  c18 : E.read (%18) = .value 13#64
  c19 : E.read (%19) = .value 21#64
  c20 : E.read (%20) = .value 9#64
  c21 : E.read (%21) = .value 29#64
  c22 : E.read (%22) = .value 10#64
  c23 : E.read (%23) = .value 37#64
  c24 : E.read (%24) = .value 11#64
  c25 : E.read (%25) = .value 45#64
  c26 : E.read (%26) = .value 12#64
  c27 : E.read (%27) = .value 14#64
  c28 : E.read (%28) = .value 18#64
  c29 : E.read (%29) = .value 15#64
  c30 : E.read (%30) = .value 26#64
  c31 : E.read (%31) = .value 34#64
  c32 : E.read (%32) = .value 17#64
  c33 : E.read (%33) = .value 42#64
  c34 : E.read (%34) = .value 50#64
  c35 : E.read (%35) = .value 20#64
  c36 : E.read (%36) = .value 23#64
  c37 : E.read (%37) = .value 22#64
  c38 : E.read (%38) = .value 31#64
  c39 : E.read (%39) = .value 39#64
  c40 : E.read (%40) = .value 47#64
  c41 : E.read (%41) = .value 25#64
  c42 : E.read (%42) = .value 27#64
  c43 : E.read (%43) = .value 28#64
  c44 : E.read (%44) = .value 36#64
  c45 : E.read (%45) = .value 30#64
  c46 : E.read (%46) = .value 44#64

theorem constants_frame (E F : Env program.Γ) (hc : Constants E)
    (hf : Frame 431 E F) : Constants F := by
  constructor
  · change F.vals 1 = _
    rw [hf.2 1 (by decide)]
    exact hc.c1
  · change F.vals 3 = _
    rw [hf.2 3 (by decide)]
    exact hc.c3
  · change F.vals 4 = _
    rw [hf.2 4 (by decide)]
    exact hc.c4
  · change F.vals 5 = _
    rw [hf.2 5 (by decide)]
    exact hc.c5
  · change F.vals 6 = _
    rw [hf.2 6 (by decide)]
    exact hc.c6
  · change F.vals 7 = _
    rw [hf.2 7 (by decide)]
    exact hc.c7
  · change F.vals 8 = _
    rw [hf.2 8 (by decide)]
    exact hc.c8
  · change F.vals 9 = _
    rw [hf.2 9 (by decide)]
    exact hc.c9
  · change F.vals 10 = _
    rw [hf.2 10 (by decide)]
    exact hc.c10
  · change F.vals 11 = _
    rw [hf.2 11 (by decide)]
    exact hc.c11
  · change F.vals 12 = _
    rw [hf.2 12 (by decide)]
    exact hc.c12
  · change F.vals 13 = _
    rw [hf.2 13 (by decide)]
    exact hc.c13
  · change F.vals 14 = _
    rw [hf.2 14 (by decide)]
    exact hc.c14
  · change F.vals 15 = _
    rw [hf.2 15 (by decide)]
    exact hc.c15
  · change F.vals 16 = _
    rw [hf.2 16 (by decide)]
    exact hc.c16
  · change F.vals 17 = _
    rw [hf.2 17 (by decide)]
    exact hc.c17
  · change F.vals 18 = _
    rw [hf.2 18 (by decide)]
    exact hc.c18
  · change F.vals 19 = _
    rw [hf.2 19 (by decide)]
    exact hc.c19
  · change F.vals 20 = _
    rw [hf.2 20 (by decide)]
    exact hc.c20
  · change F.vals 21 = _
    rw [hf.2 21 (by decide)]
    exact hc.c21
  · change F.vals 22 = _
    rw [hf.2 22 (by decide)]
    exact hc.c22
  · change F.vals 23 = _
    rw [hf.2 23 (by decide)]
    exact hc.c23
  · change F.vals 24 = _
    rw [hf.2 24 (by decide)]
    exact hc.c24
  · change F.vals 25 = _
    rw [hf.2 25 (by decide)]
    exact hc.c25
  · change F.vals 26 = _
    rw [hf.2 26 (by decide)]
    exact hc.c26
  · change F.vals 27 = _
    rw [hf.2 27 (by decide)]
    exact hc.c27
  · change F.vals 28 = _
    rw [hf.2 28 (by decide)]
    exact hc.c28
  · change F.vals 29 = _
    rw [hf.2 29 (by decide)]
    exact hc.c29
  · change F.vals 30 = _
    rw [hf.2 30 (by decide)]
    exact hc.c30
  · change F.vals 31 = _
    rw [hf.2 31 (by decide)]
    exact hc.c31
  · change F.vals 32 = _
    rw [hf.2 32 (by decide)]
    exact hc.c32
  · change F.vals 33 = _
    rw [hf.2 33 (by decide)]
    exact hc.c33
  · change F.vals 34 = _
    rw [hf.2 34 (by decide)]
    exact hc.c34
  · change F.vals 35 = _
    rw [hf.2 35 (by decide)]
    exact hc.c35
  · change F.vals 36 = _
    rw [hf.2 36 (by decide)]
    exact hc.c36
  · change F.vals 37 = _
    rw [hf.2 37 (by decide)]
    exact hc.c37
  · change F.vals 38 = _
    rw [hf.2 38 (by decide)]
    exact hc.c38
  · change F.vals 39 = _
    rw [hf.2 39 (by decide)]
    exact hc.c39
  · change F.vals 40 = _
    rw [hf.2 40 (by decide)]
    exact hc.c40
  · change F.vals 41 = _
    rw [hf.2 41 (by decide)]
    exact hc.c41
  · change F.vals 42 = _
    rw [hf.2 42 (by decide)]
    exact hc.c42
  · change F.vals 43 = _
    rw [hf.2 43 (by decide)]
    exact hc.c43
  · change F.vals 44 = _
    rw [hf.2 44 (by decide)]
    exact hc.c44
  · change F.vals 45 = _
    rw [hf.2 45 (by decide)]
    exact hc.c45
  · change F.vals 46 = _
    rw [hf.2 46 (by decide)]
    exact hc.c46

structure Registers (E : Env program.Γ) (a b r q : Pointer) : Prop where
  constants : Constants E
  first : FirstLoadRegisters E a
  second : SecondLoadRegisters E b
  r63 : E.read (%63) = .value r
  q62 : E.read (%62) = .value q

theorem registers_frame (E F : Env program.Γ) (a b r q : Pointer)
    (he : Registers E a b r q) (hf : Frame 431 E F) : Registers F a b r q := by
  refine ⟨constants_frame E F he.constants hf, ?_, ?_, ?_, ?_⟩
  · constructor
    · change F.vals 75 = _
      rw [hf.2 75 (by decide)]
      exact he.first.a75
    · change F.vals 85 = _
      rw [hf.2 85 (by decide)]
      exact he.first.a85
    · change F.vals 87 = _
      rw [hf.2 87 (by decide)]
      exact he.first.a87
    · change F.vals 89 = _
      rw [hf.2 89 (by decide)]
      exact he.first.a89
    · change F.vals 91 = _
      rw [hf.2 91 (by decide)]
      exact he.first.a91
  · constructor
    · change F.vals 73 = _
      rw [hf.2 73 (by decide)]
      exact he.second.a73
    · change F.vals 3 = _
      rw [hf.2 3 (by decide)]
      exact he.second.c3
    · change F.vals 4 = _
      rw [hf.2 4 (by decide)]
      exact he.second.c4
    · change F.vals 5 = _
      rw [hf.2 5 (by decide)]
      exact he.second.c5
    · change F.vals 6 = _
      rw [hf.2 6 (by decide)]
      exact he.second.c6
  · change F.vals 63 = _
    rw [hf.2 63 (by decide)]
    exact he.r63
  · change F.vals 62 = _
    rw [hf.2 62 (by decide)]
    exact he.q62

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577
