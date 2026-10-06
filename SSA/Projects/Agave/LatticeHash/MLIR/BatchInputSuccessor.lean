/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchTransposePath
import SSA.Projects.Agave.LatticeHash.MLIR.BatchHeaderSemantics
import SSA.Projects.Agave.LatticeHash.MLIR.BatchInit8
import SSA.Projects.Agave.LatticeHash.MLIR.BatchUpdate

namespace AgaveLatticeHash.MLIR.BatchInputSuccessor
open LeanMLIR SLLVM
open InstCombine (LLVM)

noncomputable def nonroot (W : Header8Ctx.Valuation) : SuccArgs agave_batch_8.cfgSigs :=
  let V := BatchHeader.values8 W
  ⟨19, rfl, V ⟨35, rfl⟩ ::ₕ V ⟨34, rfl⟩ ::ₕ V ⟨33, rfl⟩ ::ₕ V ⟨32, rfl⟩ ::ₕ V ⟨31, rfl⟩ ::ₕ V ⟨30, rfl⟩ ::ₕ V ⟨29, rfl⟩ ::ₕ V ⟨28, rfl⟩ ::ₕ V ⟨27, rfl⟩ ::ₕ V ⟨26, rfl⟩ ::ₕ V ⟨24, rfl⟩ ::ₕ V ⟨20, rfl⟩ ::ₕ V ⟨17, rfl⟩ ::ₕ .nil⟩

noncomputable def root (W : Header8Ctx.Valuation) : SuccArgs agave_batch_8.cfgSigs :=
  let V := BatchHeader.values8 W
  ⟨18, rfl, V ⟨35, rfl⟩ ::ₕ V ⟨34, rfl⟩ ::ₕ V ⟨33, rfl⟩ ::ₕ V ⟨32, rfl⟩ ::ₕ V ⟨31, rfl⟩ ::ₕ V ⟨30, rfl⟩ ::ₕ V ⟨29, rfl⟩ ::ₕ V ⟨28, rfl⟩ ::ₕ V ⟨20, rfl⟩ ::ₕ V ⟨17, rfl⟩ ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem nonroot_eq (A : agave_batch_8.cfgCtx.Valuation) (W : Header8Ctx.Valuation)
    (lo hi : Vector (Vector (BitVec 32) 8) 8) :
    BatchTranspose.nonrootTarget8 (BatchFieldForward.afterAll A W lo hi) = nonroot W := by
  rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem root_eq (A : agave_batch_8.cfgCtx.Valuation) (W : Header8Ctx.Valuation)
    (lo hi : Vector (Vector (BitVec 32) 8) 8) :
    BatchTranspose.rootTarget8 (BatchFieldForward.afterAll A W lo hi) = root W := by
  rfl


def sizes (ms : Fin 8 → AgaveConcrete.Message) (t : Nat) : Vector (BitVec 32) 8 :=
  Vector.ofFn fun lane => BitVec.ofNat 32
    (AgaveBatchControl.blockSize (ms lane).length (batchOffset (ms lane).length t))

def flags (ms : Fin 8 → AgaveConcrete.Message) (t : Nat) : Vector (BitVec 32) 8 :=
  Vector.ofFn fun lane => BitVec.ofNat 32
    (AgaveBatchControl.blockFlags (ms lane).length (batchOffset (ms lane).length t))

def nonrootAt (ms : Fin 8 → AgaveConcrete.Message) (t : Nat) : SuccArgs agave_batch_8.cfgSigs :=
  ⟨19, rfl, (packCV8 (BatchUpdate.stateCV8 ms t 7)).map PoisonOr.value ::ₕ (packCV8 (BatchUpdate.stateCV8 ms t 6)).map PoisonOr.value ::ₕ (packCV8 (BatchUpdate.stateCV8 ms t 5)).map PoisonOr.value ::ₕ (packCV8 (BatchUpdate.stateCV8 ms t 4)).map PoisonOr.value ::ₕ (packCV8 (BatchUpdate.stateCV8 ms t 3)).map PoisonOr.value ::ₕ (packCV8 (BatchUpdate.stateCV8 ms t 2)).map PoisonOr.value ::ₕ (packCV8 (BatchUpdate.stateCV8 ms t 1)).map PoisonOr.value ::ₕ (packCV8 (BatchUpdate.stateCV8 ms t 0)).map PoisonOr.value ::ₕ
    (BatchUpdate.offsetsAt8 ms t).map PoisonOr.value ::ₕ
    (BatchUpdate.advancedAt8 ms t).map PoisonOr.value ::ₕ
    (BatchTransposePath.activeVector ms t).map PoisonOr.value ::ₕ
    (flags ms t).map PoisonOr.value ::ₕ (sizes ms t).map PoisonOr.value ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem nonroot_represented (s : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 8 → AgaveConcrete.Message) (t : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024) :
    nonroot (BatchHeader.represented s src len out sched panic ms t) = nonrootAt ms t := by
  unfold nonroot nonrootAt
  dsimp only
  congr 14
  · apply Vector.ext
    intro i hi
    simp only [BatchUpdate.advancedAt8, Vector.getElem_map, Vector.getElem_ofFn]
    exact BatchHeader.advanced_lane s src len out sched panic ms t ⟨i, hi⟩
  · apply Vector.ext
    intro i hi
    simp only [BatchTransposePath.activeVector, Vector.getElem_map, Vector.getElem_ofFn]
    exact BatchHeader.active_lane s src len out sched panic ms t ⟨i, hi⟩ hms
  · apply Vector.ext
    intro i hi
    simp only [flags, Vector.getElem_map, Vector.getElem_ofFn]
    exact BatchHeader.flags_lane s src len out sched panic ms t ⟨i, hi⟩ hms
  · apply Vector.ext
    intro i hi
    simp only [sizes, Vector.getElem_map, Vector.getElem_ofFn]
    exact BatchHeader.size_lane s src len out sched panic ms t ⟨i, hi⟩ hms


def rootAt (ms : Fin 8 → AgaveConcrete.Message) (t : Nat) : SuccArgs agave_batch_8.cfgSigs :=
  ⟨18, rfl, (packCV8 (BatchUpdate.stateCV8 ms t 7)).map PoisonOr.value ::ₕ (packCV8 (BatchUpdate.stateCV8 ms t 6)).map PoisonOr.value ::ₕ (packCV8 (BatchUpdate.stateCV8 ms t 5)).map PoisonOr.value ::ₕ (packCV8 (BatchUpdate.stateCV8 ms t 4)).map PoisonOr.value ::ₕ (packCV8 (BatchUpdate.stateCV8 ms t 3)).map PoisonOr.value ::ₕ (packCV8 (BatchUpdate.stateCV8 ms t 2)).map PoisonOr.value ::ₕ (packCV8 (BatchUpdate.stateCV8 ms t 1)).map PoisonOr.value ::ₕ (packCV8 (BatchUpdate.stateCV8 ms t 0)).map PoisonOr.value ::ₕ
    (flags ms t).map PoisonOr.value ::ₕ (sizes ms t).map PoisonOr.value ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem root_represented (s : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 8 → AgaveConcrete.Message) (t : Nat) (hms : ∀ lane, (ms lane).length ≤ 1024) :
    root (BatchHeader.represented s src len out sched panic ms t) = rootAt ms t := by
  unfold root rootAt
  dsimp only
  congr 11
  · apply Vector.ext
    intro i hi
    simp only [flags, Vector.getElem_map, Vector.getElem_ofFn]
    exact BatchHeader.flags_lane s src len out sched panic ms t ⟨i, hi⟩ hms
  · apply Vector.ext
    intro i hi
    simp only [sizes, Vector.getElem_map, Vector.getElem_ofFn]
    exact BatchHeader.size_lane s src len out sched panic ms t ⟨i, hi⟩ hms

end AgaveLatticeHash.MLIR.BatchInputSuccessor
