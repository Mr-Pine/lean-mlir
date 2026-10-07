import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def productBlock8 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 265).take 2}

def productEnv8 (E : Env program.Γ) (x0 x1 x2 x3 x4 : BitVec 64) : Env program.Γ :=
  let v222 : BitVec 128 := (x4.setWidth 128) * 17592186044415#128
  E[%222 := .value v222]

def productWord8 (x0 x1 x2 x3 x4 : BitVec 64) : BitVec 128 :=
  let v222 : BitVec 128 := (x4.setWidth 128) * 17592186044415#128
  v222

theorem product_chunk8 (E : Env program.Γ) (s : GlobalState)
    (x0 x1 x2 x3 x4 : BitVec 64) (p89 : Pointer)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    (hr : SmallRange s.mem p89 16)
    (hp : E.read (%89) = .value p89)
    (h204 : E.read (%204) = .value (x4.setWidth 128))
    (hk28 : E.read (%28) = .value 17592186044415#128)
    : productBlock8.runBodyFrom E 0 s =
      .value (productEnv8 E x0 x1 x2 x3 x4,
        {s with mem := s.mem.storeAt p89 (productWord8 x0 x1 x2 x3 x4)}) := by
  let v222 : BitVec 128 := (x4.setWidth 128) * 17592186044415#128
  obtain ⟨h222u, h222s, h222n⟩ := product_constant_flags x4 17592186044415#128 hx4 (by decide)
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      productBlock8.runBodyFrom E' 0 S =
        .value (productEnv8 E x0 x1 x2 x3 x4,
          {s with mem := s.mem.storeAt p89 (productWord8 x0 x1 x2 x3 x4)}) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf : Fits S.mem p89 128 := by rw [hS]; exact hr.fits
  step_pure [h204, hk28, h222u, h222s]
  step_store [hp]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

/-- Exact natural column value established alongside the emitted flags. -/
theorem product_word8_toNat (x0 x1 x2 x3 x4 : BitVec 64)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    : (productWord8 x0 x1 x2 x3 x4).toNat = (x4.toNat * 17592186044415) := by
  let v222 : BitVec 128 := (x4.setWidth 128) * 17592186044415#128
  obtain ⟨h222u, h222s, h222n⟩ := product_constant_flags x4 17592186044415#128 hx4 (by decide)
  change v222.toNat = _
  norm_num [v222, h222n]

end Agave.Ed25519.ScalarReduce32.Execution
