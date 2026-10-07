import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductChunk0
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductChunk1
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductChunk2
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductChunk3
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductChunk4
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductChunk5
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductChunk6
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductChunk7
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductChunk8
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Phases
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Montgomery

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Arithmetic
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 512

theorem product_prefix (E : Env program.Γ) (s : GlobalState) :
    List.foldlM Instr.run E ((program.entry.body.drop 203).take 9) s =
      .value (E, s) := rfl

theorem product_suffix (E : Env program.Γ) (s : GlobalState) :
    List.foldlM Instr.run E ((program.entry.body.drop 267).take 5) s =
      .value (E, s) := rfl

theorem product_body_decomposition : multiplication =
    (program.entry.body.drop 203).take 9 ++
    productBlock0.body ++ productBlock1.body ++ productBlock2.body ++ productBlock3.body ++ productBlock4.body ++ productBlock5.body ++ productBlock6.body ++ productBlock7.body ++ productBlock8.body ++
    (program.entry.body.drop 267).take 5 := rfl

/-- The nine machine columns multiply the input's radix-52 value by the
literal source R. No Montgomery factor is supplied by a caller assumption. -/
theorem product_columns_value (x0 x1 x2 x3 x4 : BitVec 64)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    : wideLimbs ((productWord0 x0 x1 x2 x3 x4).toNat) ((productWord1 x0 x1 x2 x3 x4).toNat) ((productWord2 x0 x1 x2 x3 x4).toNat) ((productWord3 x0 x1 x2 x3 x4).toNat) ((productWord4 x0 x1 x2 x3 x4).toNat) ((productWord5 x0 x1 x2 x3 x4).toNat) ((productWord6 x0 x1 x2 x3 x4).toNat) ((productWord7 x0 x1 x2 x3 x4).toNat) ((productWord8 x0 x1 x2 x3 x4).toNat) =
      limbs x0.toNat x1.toNat x2.toNat x3.toNat x4.toNat * sourceR := by
  rw [product_word0_toNat x0 x1 x2 x3 x4 hx0 hx1 hx2 hx3 hx4,
    product_word1_toNat x0 x1 x2 x3 x4 hx0 hx1 hx2 hx3 hx4,
    product_word2_toNat x0 x1 x2 x3 x4 hx0 hx1 hx2 hx3 hx4,
    product_word3_toNat x0 x1 x2 x3 x4 hx0 hx1 hx2 hx3 hx4,
    product_word4_toNat x0 x1 x2 x3 x4 hx0 hx1 hx2 hx3 hx4,
    product_word5_toNat x0 x1 x2 x3 x4 hx0 hx1 hx2 hx3 hx4,
    product_word6_toNat x0 x1 x2 x3 x4 hx0 hx1 hx2 hx3 hx4,
    product_word7_toNat x0 x1 x2 x3 x4 hx0 hx1 hx2 hx3 hx4,
    product_word8_toNat x0 x1 x2 x3 x4 hx0 hx1 hx2 hx3 hx4]
  simp only [wideLimbs, limbs, sourceR]
  ring

end Agave.Ed25519.ScalarReduce32.Execution
