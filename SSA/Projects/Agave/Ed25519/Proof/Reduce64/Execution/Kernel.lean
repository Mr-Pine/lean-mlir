import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.StageConstants
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.StageCarryA
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.StageCarryB
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.StageFold
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.StagePacking
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.StageStores

namespace Agave.Ed25519.Reduce64.Execution
open LeanMLIR.RIR

attribute [local implicit_reducible] Ty.width
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Read the actual four u64 lanes in each of the ten input columns. -/
def readColumns (m : MemoryState) (p : Pointer) : Columns4 :=
  fun k => Vector.ofFn fun lane =>
    (m.readAt (p.add (BitVec.ofNat 64 (32 * k.val))) 256).extractLsb'
      (64 * lane.val) 64

/-- Actual execution of the verbatim extracted RIR kernel. The separate
instruction-slice lemmas cover [0,54), [54,67), [67,85), [85,106), [106,129),
and [129,138). No arithmetic input bound is needed for this wrapping-word
statement. Each slice exposes only the register facts needed by the next one. -/
theorem kernel_call_of_reads (dst src : Pointer) (s : GlobalState) (z : Columns4)
    (hwf : s.WF) (hdst : SmallRange s.mem dst 160) (hsrc : SmallRange s.mem src 320)
    (hreads : ∀ k : Fin 10,
      (Ty.vec 4 64).unflatten
        (s.mem.readAt (src.add (BitVec.ofNat 64 (32 * k.val))) 256) = Ty.wrap (z k)) :
    program.call (program.args (.value dst) (.value src)) s =
      .value (.nil, {s with mem := storeOutputs s.mem dst z}) := by
  func_init
  block_init
  apply constants_cont E S dst src _ _ (by assumption)
  intro E hargs hconstants
  apply carryA_cont E S dst src z _ _
    (by simpa only [hS] using hsrc) (by simpa only [hS] using hreads)
    hargs hconstants
  intro E hargs hconstants hcarryA
  apply carryB_cont E S dst src z _ _
    (by simpa only [hS] using hsrc) (by simpa only [hS] using hreads)
    hargs hconstants hcarryA
  intro E hargs hconstants hcarryB
  apply fold_cont E S dst src z _ _
    (by simpa only [hS] using hsrc) (by simpa only [hS] using hreads)
    hargs hconstants hcarryB
  intro E hargs hconstants hreduced
  apply packing_cont E S dst src z _ _ hargs hconstants hreduced
  intro E hargs hconstants hpacked
  have htail := stores_run E S dst src z
    (by simpa only [hS] using hdst) hargs hconstants hpacked
  rw [htail]
  simp only [PoisonOr.value_bind, reduceBlockExit, Exit.run,
    Regs.read_nil, EffectM.pure_eq, reduceFuncContinue]
  try rw [hS]

/-- The memory-to-memory endpoint, with input columns obtained from the initial
memory rather than supplied as an independent model. -/
theorem kernel_call (dst src : Pointer) (s : GlobalState)
    (hwf : s.WF) (hdst : SmallRange s.mem dst 160) (hsrc : SmallRange s.mem src 320) :
    program.call (program.args (.value dst) (.value src)) s =
      .value (.nil, {s with mem := storeOutputs s.mem dst (readColumns s.mem src)}) := by
  apply kernel_call_of_reads dst src s _ hwf hdst hsrc
  intro k
  simp [readColumns, Ty.extractVecElem, Nat.mul_comm]

end Agave.Ed25519.Reduce64.Execution
