import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def productBlock0 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 212).take 3}

def productEnv0 (E : Env program.Γ) (x0 x1 x2 x3 x4 : BitVec 64) : Env program.Γ :=
  let v177 : BitVec 128 := x0.setWidth 128
  let v178 : BitVec 128 := (v177) * 4302102966953709#128
  E[%177 := .value v177][%178 := .value v178]

def productWord0 (x0 x1 x2 x3 x4 : BitVec 64) : BitVec 128 :=
  let v177 : BitVec 128 := x0.setWidth 128
  let v178 : BitVec 128 := (v177) * 4302102966953709#128
  v178

theorem product_chunk0 (E : Env program.Γ) (s : GlobalState)
    (x0 x1 x2 x3 x4 : BitVec 64) (p81 : Pointer)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    (hr : SmallRange s.mem p81 16)
    (hp : E.read (%81) = .value p81)
    (h176 : E.read (%176) = .value (x0))
    (hk24 : E.read (%24) = .value 4302102966953709#128)
    : productBlock0.runBodyFrom E 0 s =
      .value (productEnv0 E x0 x1 x2 x3 x4,
        {s with mem := s.mem.storeAt p81 (productWord0 x0 x1 x2 x3 x4)}) := by
  let v177 : BitVec 128 := x0.setWidth 128
  have h177nonneg := product_limb_nonneg x0 hx0
  let v178 : BitVec 128 := (v177) * 4302102966953709#128
  obtain ⟨h178u, h178s, h178n⟩ := product_constant_flags x0 4302102966953709#128 hx0 (by decide)
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      productBlock0.runBodyFrom E' 0 S =
        .value (productEnv0 E x0 x1 x2 x3 x4,
          {s with mem := s.mem.storeAt p81 (productWord0 x0 x1 x2 x3 x4)}) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf : Fits S.mem p81 128 := by rw [hS]; exact hr.fits
  step_pure [h176, hk24, h177nonneg]
  step_pure [h176, hk24, h178u, h178s]
  step_store [hp]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

/-- Exact natural column value established alongside the emitted flags. -/
theorem product_word0_toNat (x0 x1 x2 x3 x4 : BitVec 64)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    : (productWord0 x0 x1 x2 x3 x4).toNat = (x0.toNat * 4302102966953709) := by
  let v177 : BitVec 128 := x0.setWidth 128
  have h177nonneg := product_limb_nonneg x0 hx0
  let v178 : BitVec 128 := (v177) * 4302102966953709#128
  obtain ⟨h178u, h178s, h178n⟩ := product_constant_flags x0 4302102966953709#128 hx0 (by decide)
  change v178.toNat = _
  norm_num [v177, v178, h178n]

end Agave.Ed25519.ScalarReduce32.Execution
