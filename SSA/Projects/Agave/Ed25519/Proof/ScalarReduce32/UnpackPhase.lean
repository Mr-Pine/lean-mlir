import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.UnpackChunks

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def unpackV111 (s : GlobalState) (a : Pointer) : BitVec 64 :=
  let v95 : BitVec 32 := s.mem.readAt a 32
  let v96 : BitVec 64 := v95.setWidth 64
  let v97 : Pointer := a.add 4#64
  let v98 : BitVec 8 := s.mem.readAt (a.add 4#64) 8
  let v99 : BitVec 64 := v98.setWidth 64
  let v100 : BitVec 64 := v99 <<< 32
  let v101 : BitVec 64 := v100 ||| v96
  let v102 : Pointer := a.add 5#64
  let v103 : BitVec 8 := s.mem.readAt (a.add 5#64) 8
  let v104 : BitVec 64 := v103.setWidth 64
  let v105 : BitVec 64 := v104 <<< 40
  let v106 : BitVec 64 := v101 ||| v105
  let v107 : Pointer := a.add 6#64
  let v108 : BitVec 8 := s.mem.readAt (a.add 6#64) 8
  let v109 : BitVec 64 := v108.setWidth 64
  let v110 : BitVec 64 := v109 <<< 48
  let v111 : BitVec 64 := v106 ||| v110
  let v112 : Pointer := a.add 7#64
  let v113 : BitVec 8 := s.mem.readAt (a.add 7#64) 8
  let v114 : BitVec 64 := v113.setWidth 64
  let v115 : BitVec 64 := v114 <<< 56
  let v116 : BitVec 64 := v115 ||| v111
  v111

def unpackV116 (s : GlobalState) (a : Pointer) : BitVec 64 :=
  let v95 : BitVec 32 := s.mem.readAt a 32
  let v96 : BitVec 64 := v95.setWidth 64
  let v97 : Pointer := a.add 4#64
  let v98 : BitVec 8 := s.mem.readAt (a.add 4#64) 8
  let v99 : BitVec 64 := v98.setWidth 64
  let v100 : BitVec 64 := v99 <<< 32
  let v101 : BitVec 64 := v100 ||| v96
  let v102 : Pointer := a.add 5#64
  let v103 : BitVec 8 := s.mem.readAt (a.add 5#64) 8
  let v104 : BitVec 64 := v103.setWidth 64
  let v105 : BitVec 64 := v104 <<< 40
  let v106 : BitVec 64 := v101 ||| v105
  let v107 : Pointer := a.add 6#64
  let v108 : BitVec 8 := s.mem.readAt (a.add 6#64) 8
  let v109 : BitVec 64 := v108.setWidth 64
  let v110 : BitVec 64 := v109 <<< 48
  let v111 : BitVec 64 := v106 ||| v110
  let v112 : Pointer := a.add 7#64
  let v113 : BitVec 8 := s.mem.readAt (a.add 7#64) 8
  let v114 : BitVec 64 := v113.setWidth 64
  let v115 : BitVec 64 := v114 <<< 56
  let v116 : BitVec 64 := v115 ||| v111
  v116

def unpackV124 (s : GlobalState) (a : Pointer) : BitVec 64 :=
  let v117 : Pointer := a.add 8#64
  let v118 : BitVec 32 := s.mem.readAt (a.add 8#64) 32
  let v119 : BitVec 64 := v118.setWidth 64
  let v120 : Pointer := a.add 12#64
  let v121 : BitVec 8 := s.mem.readAt (a.add 12#64) 8
  let v122 : BitVec 64 := v121.setWidth 64
  let v123 : BitVec 64 := v122 <<< 32
  let v124 : BitVec 64 := v123 ||| v119
  let v125 : Pointer := a.add 13#64
  let v126 : BitVec 8 := s.mem.readAt (a.add 13#64) 8
  let v127 : BitVec 64 := v126.setWidth 64
  let v128 : BitVec 64 := v127 <<< 40
  let v129 : Pointer := a.add 14#64
  let v130 : BitVec 16 := s.mem.readAt (a.add 14#64) 16
  let v131 : BitVec 64 := v130.setWidth 64
  let v132 : BitVec 64 := v131 <<< 48
  let v133 : BitVec 64 := v132 ||| v128
  let v134 : BitVec 64 := v133 ||| v124
  v124

def unpackV133 (s : GlobalState) (a : Pointer) : BitVec 64 :=
  let v117 : Pointer := a.add 8#64
  let v118 : BitVec 32 := s.mem.readAt (a.add 8#64) 32
  let v119 : BitVec 64 := v118.setWidth 64
  let v120 : Pointer := a.add 12#64
  let v121 : BitVec 8 := s.mem.readAt (a.add 12#64) 8
  let v122 : BitVec 64 := v121.setWidth 64
  let v123 : BitVec 64 := v122 <<< 32
  let v124 : BitVec 64 := v123 ||| v119
  let v125 : Pointer := a.add 13#64
  let v126 : BitVec 8 := s.mem.readAt (a.add 13#64) 8
  let v127 : BitVec 64 := v126.setWidth 64
  let v128 : BitVec 64 := v127 <<< 40
  let v129 : Pointer := a.add 14#64
  let v130 : BitVec 16 := s.mem.readAt (a.add 14#64) 16
  let v131 : BitVec 64 := v130.setWidth 64
  let v132 : BitVec 64 := v131 <<< 48
  let v133 : BitVec 64 := v132 ||| v128
  let v134 : BitVec 64 := v133 ||| v124
  v133

def unpackV134 (s : GlobalState) (a : Pointer) : BitVec 64 :=
  let v117 : Pointer := a.add 8#64
  let v118 : BitVec 32 := s.mem.readAt (a.add 8#64) 32
  let v119 : BitVec 64 := v118.setWidth 64
  let v120 : Pointer := a.add 12#64
  let v121 : BitVec 8 := s.mem.readAt (a.add 12#64) 8
  let v122 : BitVec 64 := v121.setWidth 64
  let v123 : BitVec 64 := v122 <<< 32
  let v124 : BitVec 64 := v123 ||| v119
  let v125 : Pointer := a.add 13#64
  let v126 : BitVec 8 := s.mem.readAt (a.add 13#64) 8
  let v127 : BitVec 64 := v126.setWidth 64
  let v128 : BitVec 64 := v127 <<< 40
  let v129 : Pointer := a.add 14#64
  let v130 : BitVec 16 := s.mem.readAt (a.add 14#64) 16
  let v131 : BitVec 64 := v130.setWidth 64
  let v132 : BitVec 64 := v131 <<< 48
  let v133 : BitVec 64 := v132 ||| v128
  let v134 : BitVec 64 := v133 ||| v124
  v134

def unpackV147 (s : GlobalState) (a : Pointer) : BitVec 64 :=
  let v135 : Pointer := a.add 16#64
  let v136 : BitVec 16 := s.mem.readAt (a.add 16#64) 16
  let v137 : BitVec 64 := v136.setWidth 64
  let v138 : Pointer := a.add 18#64
  let v139 : BitVec 8 := s.mem.readAt (a.add 18#64) 8
  let v140 : BitVec 64 := v139.setWidth 64
  let v141 : BitVec 64 := v140 <<< 16
  let v142 : BitVec 64 := v141 ||| v137
  let v143 : Pointer := a.add 19#64
  let v144 : BitVec 8 := s.mem.readAt (a.add 19#64) 8
  let v145 : BitVec 64 := v144.setWidth 64
  let v146 : BitVec 64 := v145 <<< 24
  let v147 : BitVec 64 := v142 ||| v146
  let v148 : Pointer := a.add 20#64
  let v149 : BitVec 32 := s.mem.readAt (a.add 20#64) 32
  let v150 : BitVec 64 := v149.setWidth 64
  let v151 : BitVec 64 := v150 <<< 32
  let v152 : BitVec 64 := v151 ||| v147
  v147

def unpackV152 (s : GlobalState) (a : Pointer) : BitVec 64 :=
  let v135 : Pointer := a.add 16#64
  let v136 : BitVec 16 := s.mem.readAt (a.add 16#64) 16
  let v137 : BitVec 64 := v136.setWidth 64
  let v138 : Pointer := a.add 18#64
  let v139 : BitVec 8 := s.mem.readAt (a.add 18#64) 8
  let v140 : BitVec 64 := v139.setWidth 64
  let v141 : BitVec 64 := v140 <<< 16
  let v142 : BitVec 64 := v141 ||| v137
  let v143 : Pointer := a.add 19#64
  let v144 : BitVec 8 := s.mem.readAt (a.add 19#64) 8
  let v145 : BitVec 64 := v144.setWidth 64
  let v146 : BitVec 64 := v145 <<< 24
  let v147 : BitVec 64 := v142 ||| v146
  let v148 : Pointer := a.add 20#64
  let v149 : BitVec 32 := s.mem.readAt (a.add 20#64) 32
  let v150 : BitVec 64 := v149.setWidth 64
  let v151 : BitVec 64 := v150 <<< 32
  let v152 : BitVec 64 := v151 ||| v147
  v152

def unpackV160 (s : GlobalState) (a : Pointer) : BitVec 64 :=
  let v153 : Pointer := a.add 24#64
  let v154 : BitVec 8 := s.mem.readAt (a.add 24#64) 8
  let v155 : BitVec 64 := v154.setWidth 64
  let v156 : Pointer := a.add 25#64
  let v157 : BitVec 8 := s.mem.readAt (a.add 25#64) 8
  let v158 : BitVec 64 := v157.setWidth 64
  let v159 : BitVec 64 := v158 <<< 8
  let v160 : BitVec 64 := v159 ||| v155
  let v161 : Pointer := a.add 26#64
  let v162 : BitVec 32 := s.mem.readAt (a.add 26#64) 32
  let v163 : BitVec 64 := v162.setWidth 64
  let v164 : BitVec 64 := v163 <<< 16
  let v165 : Pointer := a.add 30#64
  let v166 : BitVec 16 := s.mem.readAt (a.add 30#64) 16
  let v167 : BitVec 64 := v166.setWidth 64
  let v168 : BitVec 64 := v167 <<< 48
  let v169 : BitVec 64 := v168 ||| v164
  let v170 : BitVec 64 := v169 ||| v160
  v160

def unpackV169 (s : GlobalState) (a : Pointer) : BitVec 64 :=
  let v153 : Pointer := a.add 24#64
  let v154 : BitVec 8 := s.mem.readAt (a.add 24#64) 8
  let v155 : BitVec 64 := v154.setWidth 64
  let v156 : Pointer := a.add 25#64
  let v157 : BitVec 8 := s.mem.readAt (a.add 25#64) 8
  let v158 : BitVec 64 := v157.setWidth 64
  let v159 : BitVec 64 := v158 <<< 8
  let v160 : BitVec 64 := v159 ||| v155
  let v161 : Pointer := a.add 26#64
  let v162 : BitVec 32 := s.mem.readAt (a.add 26#64) 32
  let v163 : BitVec 64 := v162.setWidth 64
  let v164 : BitVec 64 := v163 <<< 16
  let v165 : Pointer := a.add 30#64
  let v166 : BitVec 16 := s.mem.readAt (a.add 30#64) 16
  let v167 : BitVec 64 := v166.setWidth 64
  let v168 : BitVec 64 := v167 <<< 48
  let v169 : BitVec 64 := v168 ||| v164
  let v170 : BitVec 64 := v169 ||| v160
  v169

def unpackV170 (s : GlobalState) (a : Pointer) : BitVec 64 :=
  let v153 : Pointer := a.add 24#64
  let v154 : BitVec 8 := s.mem.readAt (a.add 24#64) 8
  let v155 : BitVec 64 := v154.setWidth 64
  let v156 : Pointer := a.add 25#64
  let v157 : BitVec 8 := s.mem.readAt (a.add 25#64) 8
  let v158 : BitVec 64 := v157.setWidth 64
  let v159 : BitVec 64 := v158 <<< 8
  let v160 : BitVec 64 := v159 ||| v155
  let v161 : Pointer := a.add 26#64
  let v162 : BitVec 32 := s.mem.readAt (a.add 26#64) 32
  let v163 : BitVec 64 := v162.setWidth 64
  let v164 : BitVec 64 := v163 <<< 16
  let v165 : Pointer := a.add 30#64
  let v166 : BitVec 16 := s.mem.readAt (a.add 30#64) 16
  let v167 : BitVec 64 := v166.setWidth 64
  let v168 : BitVec 64 := v167 <<< 48
  let v169 : BitVec 64 := v168 ||| v164
  let v170 : BitVec 64 := v169 ||| v160
  v170

structure UnpackReady (E : Env program.Γ) (a : Pointer) (scratch : Fin 4 → Pointer) : Prop where
  input : E.read (%arg1) = .value a
  p0 : E.read (%72) = .value (scratch 0)
  p1 : E.read (%73) = .value (scratch 1)
  p2 : E.read (%74) = .value (scratch 2)
  p3 : E.read (%75) = .value (scratch 3)
  c1 : E.read (%1) = .value 4#64
  c2 : E.read (%2) = .value 32#64
  c3 : E.read (%3) = .value 5#64
  c4 : E.read (%4) = .value 40#64
  c5 : E.read (%5) = .value 6#64
  c6 : E.read (%6) = .value 48#64
  c7 : E.read (%7) = .value 7#64
  c8 : E.read (%8) = .value 56#64
  c9 : E.read (%9) = .value 8#64
  c10 : E.read (%10) = .value 12#64
  c11 : E.read (%11) = .value 13#64
  c12 : E.read (%12) = .value 14#64
  c13 : E.read (%13) = .value 16#64
  c14 : E.read (%14) = .value 18#64
  c15 : E.read (%15) = .value 19#64
  c16 : E.read (%16) = .value 24#64
  c17 : E.read (%17) = .value 20#64
  c18 : E.read (%18) = .value 25#64
  c19 : E.read (%19) = .value 26#64
  c20 : E.read (%20) = .value 30#64
  c21 : E.read (%21) = .value 0#64
  c22 : E.read (%22) = .value 36#64
  c23 : E.read (%23) = .value 4503599627370495#64

def unpackPhaseResult (E : Env program.Γ) (s : GlobalState) (a : Pointer)
    (scratch : Fin 4 → Pointer) : Env program.Γ × GlobalState :=
  let q0 : Env program.Γ × GlobalState := (E, s)
  let q1 := (unpackEnv0 q0.1 a q0.2, q0.2)
  let q2 := (unpackEnv1 q1.1 a q1.2, q1.2)
  let q3 := unpackScratch0Result q2.1 q2.2 (scratch 1) (unpackV134 s a)
  let q4 := (unpackEnv2 q3.1 a q3.2, q3.2)
  let q5 := unpackScratch1Result q4.1 q4.2 (scratch 2) (unpackV152 q3.2 a)
  let q6 := (unpackEnv3 q5.1 a q5.2, q5.2)
  let q7 := unpackScratch2Result q6.1 q6.2 (scratch 3) (unpackV170 q5.2 a)
  let q8 := unpackScratch3Result q7.1 q7.2 (scratch 0) (scratch 1) (scratch 2) (scratch 3) 0#64
  let q9 := (unpackTailEnv q8.1 (unpackV169 q5.2 a) (unpackV160 q5.2 a)
    (unpackV152 q3.2 a) (unpackV147 q3.2 a) (unpackV133 s a) (unpackV124 s a)
    (unpackV116 s a) (unpackV111 s a), q8.2)
  q9

/-- Execute the complete unpack phase while retaining all intermediate
scratch stores. Input/scratch aliasing is not silently ruled out: later loads
observe the concrete state produced by earlier private writes. -/
theorem unpack_phase (E : Env program.Γ) (s : GlobalState) (a : Pointer)
    (scratch : Fin 4 → Pointer) (hr : UnpackReady E a scratch)
    (ha : SmallRange s.mem a 32)
    (hfit : ∀ i, SmallRange s.mem (scratch i) 8) :
    List.foldlM Instr.run E unpack s = .value (unpackPhaseResult E s a scratch) := by
  let q0 : Env program.Γ × GlobalState := (E, s)
  let q1 := (unpackEnv0 q0.1 a q0.2, q0.2)
  let q2 := (unpackEnv1 q1.1 a q1.2, q1.2)
  let q3 := unpackScratch0Result q2.1 q2.2 (scratch 1) (unpackV134 s a)
  let q4 := (unpackEnv2 q3.1 a q3.2, q3.2)
  let q5 := unpackScratch1Result q4.1 q4.2 (scratch 2) (unpackV152 q3.2 a)
  let q6 := (unpackEnv3 q5.1 a q5.2, q5.2)
  let q7 := unpackScratch2Result q6.1 q6.2 (scratch 3) (unpackV170 q5.2 a)
  let q8 := unpackScratch3Result q7.1 q7.2 (scratch 0) (scratch 1) (scratch 2) (scratch 3) 0#64
  let q9 := (unpackTailEnv q8.1 (unpackV169 q5.2 a) (unpackV160 q5.2 a)
    (unpackV152 q3.2 a) (unpackV147 q3.2 a) (unpackV133 s a) (unpackV124 s a)
    (unpackV116 s a) (unpackV111 s a), q8.2)
  have hf0a : SmallRange q0.2.mem a 32 := by
    dsimp only [q0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170]
    repeat' apply SmallRange.storeAt
    exact ha
  have h0 := unpack_chunk0 q0.1 a q0.2 hf0a
    (by simpa [q0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.input)
    (by simpa [q0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c1)
    (by simpa [q0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c2)
    (by simpa [q0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c3)
    (by simpa [q0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c4)
    (by simpa [q0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c5)
    (by simpa [q0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c6)
    (by simpa [q0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c7)
    (by simpa [q0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c8)
  change List.foldlM Instr.run q0.1 unpackBlock0.body q0.2 = .value q1 at h0
  have hf1a : SmallRange q1.2.mem a 32 := by
    dsimp only [q0, q1, unpackEnv0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170]
    repeat' apply SmallRange.storeAt
    exact ha
  have h1 := unpack_chunk1 q1.1 a q1.2 hf1a
    (by simpa [q0, q1, unpackEnv0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.input)
    (by simpa [q0, q1, unpackEnv0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c2)
    (by simpa [q0, q1, unpackEnv0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c4)
    (by simpa [q0, q1, unpackEnv0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c6)
    (by simpa [q0, q1, unpackEnv0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c9)
    (by simpa [q0, q1, unpackEnv0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c10)
    (by simpa [q0, q1, unpackEnv0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c11)
    (by simpa [q0, q1, unpackEnv0, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c12)
  change List.foldlM Instr.run q1.1 unpackBlock1.body q1.2 = .value q2 at h1
  have hf3a : SmallRange q3.2.mem a 32 := by
    dsimp only [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170]
    repeat' apply SmallRange.storeAt
    exact ha
  have h3 := unpack_chunk2 q3.1 a q3.2 hf3a
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.input)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c2)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c13)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c14)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c15)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c16)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c17)
  change List.foldlM Instr.run q3.1 unpackBlock2.body q3.2 = .value q4 at h3
  have hf5a : SmallRange q5.2.mem a 32 := by
    dsimp only [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170]
    repeat' apply SmallRange.storeAt
    exact ha
  have h5 := unpack_chunk3 q5.1 a q5.2 hf5a
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.input)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c6)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c9)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c13)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c16)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c18)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c19)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c20)
  change List.foldlM Instr.run q5.1 unpackBlock3.body q5.2 = .value q6 at h5
  have hf2p1 : SmallRange q2.2.mem (scratch 1) 8 := by
    dsimp only [q0, q1, unpackEnv0, q2, unpackEnv1, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170]
    repeat' apply SmallRange.storeAt
    exact hfit 1
  have h2 := unpackScratch0_execute q2.1 q2.2 (scratch 1) (unpackV134 s a) hf2p1
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.p1)
    (by simp [q0, q1, unpackEnv0, q2, unpackEnv1, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env])
  change List.foldlM Instr.run q2.1 unpackScratch0Block.body q2.2 = .value q3 at h2
  have hf4p2 : SmallRange q4.2.mem (scratch 2) 8 := by
    dsimp only [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170]
    repeat' apply SmallRange.storeAt
    exact hfit 2
  have h4 := unpackScratch1_execute q4.1 q4.2 (scratch 2) (unpackV152 q3.2 a) hf4p2
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.p2)
    (by simp [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env])
  change List.foldlM Instr.run q4.1 unpackScratch1Block.body q4.2 = .value q5 at h4
  have hf6p3 : SmallRange q6.2.mem (scratch 3) 8 := by
    dsimp only [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170]
    repeat' apply SmallRange.storeAt
    exact hfit 3
  have h6 := unpackScratch2_execute q6.1 q6.2 (scratch 3) (unpackV170 q5.2 a) hf6p3
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.p3)
    (by simp [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env])
  change List.foldlM Instr.run q6.1 unpackScratch2Block.body q6.2 = .value q7 at h6
  have hf7p0 : SmallRange q7.2.mem (scratch 0) 8 := by
    dsimp only [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170]
    repeat' apply SmallRange.storeAt
    exact hfit 0
  have hf7p1 : SmallRange q7.2.mem (scratch 1) 8 := by
    dsimp only [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170]
    repeat' apply SmallRange.storeAt
    exact hfit 1
  have hf7p2 : SmallRange q7.2.mem (scratch 2) 8 := by
    dsimp only [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170]
    repeat' apply SmallRange.storeAt
    exact hfit 2
  have hf7p3 : SmallRange q7.2.mem (scratch 3) 8 := by
    dsimp only [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170]
    repeat' apply SmallRange.storeAt
    exact hfit 3
  have h7 := unpackScratch3_execute q7.1 q7.2 (scratch 0) (scratch 1) (scratch 2) (scratch 3) 0#64
    hf7p0
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.p0)
    hf7p1
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.p1)
    hf7p2
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.p2)
    hf7p3
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.p3)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c21)
  change List.foldlM Instr.run q7.1 unpackScratch3Block.body q7.2 = .value q8 at h7
  have h8 := unpack_tail q8.1 q8.2
    (unpackV169 q5.2 a) (unpackV160 q5.2 a) (unpackV152 q3.2 a)
    (unpackV147 q3.2 a) (unpackV133 s a) (unpackV124 s a) (unpackV116 s a) (unpackV111 s a)
    (by simp [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, q8, unpackScratch3Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env])
    (by simp [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, q8, unpackScratch3Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env])
    (by simp [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, q8, unpackScratch3Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env])
    (by simp [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, q8, unpackScratch3Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env])
    (by simp [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, q8, unpackScratch3Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env])
    (by simp [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, q8, unpackScratch3Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env])
    (by simp [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, q8, unpackScratch3Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env])
    (by simp [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, q8, unpackScratch3Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env])
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, q8, unpackScratch3Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c13)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, q8, unpackScratch3Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c16)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, q8, unpackScratch3Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c22)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, q8, unpackScratch3Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c23)
    (by simpa [q0, q1, unpackEnv0, q2, unpackEnv1, q3, unpackScratch0Result, q4, unpackEnv2, q5, unpackScratch1Result, q6, unpackEnv3, q7, unpackScratch2Result, q8, unpackScratch3Result, unpackV111, unpackV116, unpackV124, unpackV133, unpackV134, unpackV147, unpackV152, unpackV160, unpackV169, unpackV170, mlir_env] using hr.c10)
    (by
      exact unpack_exact_shift (q5.2.mem.readAt (a.add 30#64) 16)
        (q5.2.mem.readAt (a.add 26#64) 32))
  change List.foldlM Instr.run q8.1 unpackTailBlock.body q8.2 = .value q9 at h8
  have hf : List.foldlM Instr.run q0.1 unpack q0.2 = .value q9 := by
    rw [unpack_body_decomposition]
    simp only [List.foldlM_append, EffectM.bind_eq, unpack_prefix,
      h0, h1, h2, h3, h4, h5, h6, h7, h8, PoisonOr.value_bind]
  exact hf

end Agave.Ed25519.ScalarReduce32.Execution
