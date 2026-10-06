import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundData
import SSA.Projects.Agave.LatticeHash.MLIR.PrefixIndices
namespace AgaveLatticeHash.MLIR.BatchRoundBranches
open LeanMLIR SLLVM BatchRounds
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
@[simp] theorem finalMap8_20_at0 :
    finalMap8_20 (t := SLLVM.Ty.bitvec 1) ⟨0, rfl⟩ = ⟨0, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at1 :
    finalMap8_20 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨1, rfl⟩ = ⟨1, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at3 :
    finalMap8_20 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨3, rfl⟩ = ⟨3, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at4 :
    finalMap8_20 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨4, rfl⟩ = ⟨4, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at6 :
    finalMap8_20 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨6, rfl⟩ = ⟨6, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at23 :
    finalMap8_20 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨23, rfl⟩ = ⟨23, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at25 :
    finalMap8_20 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨25, rfl⟩ = ⟨25, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at26 :
    finalMap8_20 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨26, rfl⟩ = ⟨26, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at28 :
    finalMap8_20 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨28, rfl⟩ = ⟨28, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at45 :
    finalMap8_20 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨45, rfl⟩ = ⟨45, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at47 :
    finalMap8_20 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨47, rfl⟩ = ⟨47, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at48 :
    finalMap8_20 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨48, rfl⟩ = ⟨48, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at50 :
    finalMap8_20 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨50, rfl⟩ = ⟨50, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at67 :
    finalMap8_20 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨67, rfl⟩ = ⟨67, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at69 :
    finalMap8_20 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨69, rfl⟩ = ⟨69, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at70 :
    finalMap8_20 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨70, rfl⟩ = ⟨70, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at72 :
    finalMap8_20 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨72, rfl⟩ = ⟨72, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_20_at177 :
    finalMap8_20 (t := SLLVM.Ty.bitvec 64) ⟨177, rfl⟩ = ⟨177, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem origin8_20_at0 :
    prefix8_20.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 1))) ⟨0, rfl⟩ = ⟨178, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_20_at1 :
    prefix8_20.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 64))) ⟨1, rfl⟩ = ⟨179, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_20_at2 :
    prefix8_20.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 64))) ⟨2, rfl⟩ = ⟨180, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_20_at3 :
    prefix8_20.contextHom (t := SLLVM.Ty.arith (.vector 4 (.bitvec 64))) ⟨3, rfl⟩ = ⟨181, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_20_at4 :
    prefix8_20.contextHom (t := SLLVM.Ty.arith (.vector 4 (.bitvec 64))) ⟨4, rfl⟩ = ⟨182, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_20_at5 :
    prefix8_20.contextHom (t := SLLVM.Ty.arith (.vector 4 (.bitvec 64))) ⟨5, rfl⟩ = ⟨183, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_20_at6 :
    prefix8_20.contextHom (t := SLLVM.Ty.arith (.vector 4 (.bitvec 64))) ⟨6, rfl⟩ = ⟨184, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_20_at7 :
    prefix8_20.contextHom (t := SLLVM.Ty.arith (.vector 4 (.bitvec 64))) ⟨7, rfl⟩ = ⟨185, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_20_at8 :
    prefix8_20.contextHom (t := SLLVM.Ty.arith (.vector 4 (.bitvec 64))) ⟨8, rfl⟩ = ⟨186, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_20_at9 :
    prefix8_20.contextHom (t := SLLVM.Ty.arith (.vector 4 (.bitvec 64))) ⟨9, rfl⟩ = ⟨187, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_20_at10 :
    prefix8_20.contextHom (t := SLLVM.Ty.arith (.vector 4 (.bitvec 64))) ⟨10, rfl⟩ = ⟨188, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem finalMap8_23_at0 :
    finalMap8_23 (t := SLLVM.Ty.bitvec 1) ⟨0, rfl⟩ = ⟨0, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at1 :
    finalMap8_23 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨1, rfl⟩ = ⟨1, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at3 :
    finalMap8_23 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨3, rfl⟩ = ⟨3, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at4 :
    finalMap8_23 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨4, rfl⟩ = ⟨4, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at6 :
    finalMap8_23 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨6, rfl⟩ = ⟨6, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at23 :
    finalMap8_23 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨23, rfl⟩ = ⟨23, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at25 :
    finalMap8_23 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨25, rfl⟩ = ⟨25, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at26 :
    finalMap8_23 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨26, rfl⟩ = ⟨26, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at28 :
    finalMap8_23 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨28, rfl⟩ = ⟨28, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at45 :
    finalMap8_23 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨45, rfl⟩ = ⟨45, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at47 :
    finalMap8_23 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨47, rfl⟩ = ⟨47, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at48 :
    finalMap8_23 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨48, rfl⟩ = ⟨48, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at50 :
    finalMap8_23 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨50, rfl⟩ = ⟨50, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at67 :
    finalMap8_23 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨67, rfl⟩ = ⟨67, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at69 :
    finalMap8_23 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨69, rfl⟩ = ⟨69, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at70 :
    finalMap8_23 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨70, rfl⟩ = ⟨70, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at72 :
    finalMap8_23 (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨72, rfl⟩ = ⟨72, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap8_23_at177 :
    finalMap8_23 (t := SLLVM.Ty.bitvec 64) ⟨177, rfl⟩ = ⟨177, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem origin8_23_at0 :
    prefix8_23.contextHom (t := SLLVM.Ty.bitvec 64) ⟨0, rfl⟩ = ⟨178, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at1 :
    prefix8_23.contextHom (t := SLLVM.Ty.ptr) ⟨1, rfl⟩ = ⟨179, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at2 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨2, rfl⟩ = ⟨180, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at3 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨3, rfl⟩ = ⟨181, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at4 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨4, rfl⟩ = ⟨182, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at5 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨5, rfl⟩ = ⟨183, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at6 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨6, rfl⟩ = ⟨184, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at7 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨7, rfl⟩ = ⟨185, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at8 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨8, rfl⟩ = ⟨186, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at9 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨9, rfl⟩ = ⟨187, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at10 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨10, rfl⟩ = ⟨188, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at11 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨11, rfl⟩ = ⟨189, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at12 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨12, rfl⟩ = ⟨190, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at13 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨13, rfl⟩ = ⟨191, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at14 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨14, rfl⟩ = ⟨192, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at15 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨15, rfl⟩ = ⟨193, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at16 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨16, rfl⟩ = ⟨194, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at17 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨17, rfl⟩ = ⟨195, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at18 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨18, rfl⟩ = ⟨196, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin8_23_at19 :
    prefix8_23.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 32))) ⟨19, rfl⟩ = ⟨197, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
end AgaveLatticeHash.MLIR.BatchRoundBranches
