import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Locals
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Cutpoints

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Challenge

def entryEnv (E : Env program.Γ) (s : GlobalState) (count : BitVec 8)
    (blocks : BitVec 128) : Env program.Γ :=
  paddingEnv (allocatedEnv E s) (slot s 5) (slot s 3) count blocks

set_option maxRecDepth 20000
set_option maxHeartbeats 1800000

/-- The imported entry block, including all seventy allocations and its
actual conditional edge. The count and block counter are read from caller
memory; the length arithmetic has no non-wrapping precondition. -/
theorem entry_block (p : Primitives) (E : Env program.Γ) (s : GlobalState)
    (src : Pointer) (count : BitVec 8) (blocks : BitVec 128)
    (hsrc : E.read (%arg1) = .value src) (hwf : s.WF)
    (hs : SmallRange s.mem src 208)
    (hcount : s.mem.readAt (src.add 127#64) 8 = count)
    (hblocks : s.mem.readAt (src.add 192#64) 128 = blocks)
    (hp : count.toNat < 128) :
    (program p).runFrom E 0 s =
      (program p).runFrom (entryEnv E s count blocks)
        (if Agave.Ed25519.SHA512.needsTwoBlocks count then 1 else 2)
        (entryState s src count) := by
  have hl := locals_allocated s hwf
  have ht := padding_tail (allocatedEnv E s) (allocateSlots s slotSizes)
    src (slot s 5) (slot s 3) count blocks
    (by simpa [allocatedEnv, mlir_env] using hsrc)
    (by simp [allocatedEnv, mlir_env]) (by simp [allocatedEnv, mlir_env])
    (by simp [allocatedEnv, mlir_env]) (by simp [allocatedEnv, mlir_env])
    (by simp [allocatedEnv, mlir_env]) (by simp [allocatedEnv, mlir_env])
    (by simp [allocatedEnv, mlir_env]) (by simp [allocatedEnv, mlir_env])
    (by simp [allocatedEnv, mlir_env]) (by simp [allocatedEnv, mlir_env])
    (by simp [allocatedEnv, mlir_env]) (by simp [allocatedEnv, mlir_env])
    (by simp [allocatedEnv, mlir_env])
    (allocateSlots_live _ hwf hs) hl.context hl.buffer
    (slot_ne_caller s 5 (by decide) src hwf hs)
    (slot_ne s 3 5 (by decide) (by decide) (by decide))
    (by rw [allocateSlots_read _ hwf
          (smallRange_add hs (k := 127) (count := 1) (by decide)), hcount])
    (by rw [allocateSlots_read _ hwf
          (smallRange_add hs (k := 192) (count := 16) (by decide)), hblocks]) hp
  have hbody : program.bb0.runBodyFrom E 0 s =
      .value (entryEnv E s count blocks, entryState s src count) := by
    rw [runBodyFrom_slice program.bb0 E (allocatedEnv E s) s
      (allocateSlots s slotSizes) 0 151 (by simpa using allocation_prefix E s)]
    exact ht
  have hblock : program.bb0.run program.blockParams E s =
      .value ((entryEnv E s count blocks,
        .inr (if Agave.Ed25519.SHA512.needsTwoBlocks count then 1 else 2)),
        entryState s src count) := by
    rw [BasicBlock.run_eq]
    simp only [EffectM.bind_eq, hbody, PoisonOr.value_bind]
    cases hcond : Agave.Ed25519.SHA512.needsTwoBlocks count <;>
      simp [EffectM.bind_eq, hbody, program.bb0, Exit.run, Jump.run,
        entryEnv, paddingEnv, mlir_env, hcond, Regs.read_nil,
        Env.writeMany_nil, EffectM.pure_eq]
  rw [Func.runFrom_eq]
  change (program.bb0.run program.blockParams E s >>= fun x =>
    (program p).continue x.1.1 x.1.2 x.2) = _
  rw [hblock]
  rfl

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
