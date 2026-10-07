import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.UnpackChunk3

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Lifetimes and alias declarations have their imported RIR no-op semantics. -/
theorem unpack_prefix (E : Env program.Γ) (s : GlobalState) :
    List.foldlM Instr.run E ((program.entry.body.drop 95).take 11) s =
      .value (E, s) := rfl

/-- This is the concrete shape of register %169 in the final load chunk. -/
theorem unpack_exact_shift (hi : BitVec 16) (lo : BitVec 32) :
    ((hi.setWidth 64 <<< 48) ||| (lo.setWidth 64 <<< 16)).extractLsb' 0 16 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  interval_cases i <;> simp [BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]

def unpackTailBlock : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 193).take 10}

def unpackTailEnv (E : Env program.Γ)
    (u169 u160 u152 u147 u133 u124 u116 u111 : BitVec 64) : Env program.Γ :=
  let v171 := u169 >>> 16
  let v172 := ((u160 ++ u152) <<< 36).extractLsb' 64 64
  let v173 := ((u147 ++ u133) <<< 24).extractLsb' 64 64
  let v174 := v173 &&& 4503599627370495#64
  let v175 := ((u124 ++ u116) <<< 12).extractLsb' 64 64
  let v176 := u111 &&& 4503599627370495#64
  E[%171 := .value v171, %172 := .value v172, %173 := .value v173,
    %174 := .value v174, %175 := .value v175, %176 := .value v176]

theorem unpack_tail (E : Env program.Γ) (s : GlobalState)
    (u169 u160 u152 u147 u133 u124 u116 u111 : BitVec 64)
    (h169 : E.read (%169) = .value u169)
    (h160 : E.read (%160) = .value u160)
    (h152 : E.read (%152) = .value u152)
    (h147 : E.read (%147) = .value u147)
    (h133 : E.read (%133) = .value u133)
    (h124 : E.read (%124) = .value u124)
    (h116 : E.read (%116) = .value u116)
    (h111 : E.read (%111) = .value u111)
    (hk13 : E.read (%13) = .value 16#64)
    (hk16 : E.read (%16) = .value 24#64)
    (hk22 : E.read (%22) = .value 36#64)
    (hk23 : E.read (%23) = .value 4503599627370495#64)
    (hk10 : E.read (%10) = .value 12#64)
    (hexact : u169.extractLsb' 0 16 = 0) :
    unpackTailBlock.runBodyFrom E 0 s =
      .value (unpackTailEnv E u169 u160 u152 u147 u133 u124 u116 u111, s) := by
  suffices ∀ (E' : Env program.Γ), E' = E →
      unpackTailBlock.runBodyFrom E' 0 s =
        .value (unpackTailEnv E u169 u160 u152 u147 u133 u124 u116 u111, s) by
    exact this E rfl
  intro E' hE
  step_pure [h169, h160, h152, h147, h133, h124, h116, h111, hk13, hk16, hk22, hk23, hk10, hexact]
  step_pure [h169, h160, h152, h147, h133, h124, h116, h111, hk13, hk16, hk22, hk23, hk10, hexact]
  step_pure [h169, h160, h152, h147, h133, h124, h116, h111, hk13, hk16, hk22, hk23, hk10, hexact]
  step_pure [h169, h160, h152, h147, h133, h124, h116, h111, hk13, hk16, hk22, hk23, hk10, hexact]
  step_pure [h169, h160, h152, h147, h133, h124, h116, h111, hk13, hk16, hk22, hk23, hk10, hexact]
  step_pure [h169, h160, h152, h147, h133, h124, h116, h111, hk13, hk16, hk22, hk23, hk10, hexact]
  step_pure [h169, h160, h152, h147, h133, h124, h116, h111, hk13, hk16, hk22, hk23, hk10, hexact]
  step_pure [h169, h160, h152, h147, h133, h124, h116, h111, hk13, hk16, hk22, hk23, hk10, hexact]
  step_pure [h169, h160, h152, h147, h133, h124, h116, h111, hk13, hk16, hk22, hk23, hk10, hexact]
  step_pure [h169, h160, h152, h147, h133, h124, h116, h111, hk13, hk16, hk22, hk23, hk10, hexact]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
