/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundData
import SSA.Projects.Agave.LatticeHash.MLIR.PrefixIndices
namespace AgaveLatticeHash.MLIR.BatchRoundBranches
open LeanMLIR SLLVM BatchRounds
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
@[simp] theorem finalMap16_7_at0 :
    finalMap16_7 (t := SLLVM.Ty.bitvec 1) ⟨0, rfl⟩ = ⟨0, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at1 :
    finalMap16_7 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨1, rfl⟩ = ⟨1, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at3 :
    finalMap16_7 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨3, rfl⟩ = ⟨3, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at4 :
    finalMap16_7 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨4, rfl⟩ = ⟨4, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at6 :
    finalMap16_7 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨6, rfl⟩ = ⟨6, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at23 :
    finalMap16_7 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨23, rfl⟩ = ⟨23, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at25 :
    finalMap16_7 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨25, rfl⟩ = ⟨25, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at26 :
    finalMap16_7 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨26, rfl⟩ = ⟨26, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at28 :
    finalMap16_7 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨28, rfl⟩ = ⟨28, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at45 :
    finalMap16_7 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨45, rfl⟩ = ⟨45, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at47 :
    finalMap16_7 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨47, rfl⟩ = ⟨47, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at48 :
    finalMap16_7 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨48, rfl⟩ = ⟨48, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at50 :
    finalMap16_7 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨50, rfl⟩ = ⟨50, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at67 :
    finalMap16_7 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨67, rfl⟩ = ⟨67, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at69 :
    finalMap16_7 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨69, rfl⟩ = ⟨69, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at70 :
    finalMap16_7 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨70, rfl⟩ = ⟨70, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at72 :
    finalMap16_7 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨72, rfl⟩ = ⟨72, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_7_at177 :
    finalMap16_7 (t := SLLVM.Ty.bitvec 64) ⟨177, rfl⟩ = ⟨177, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem origin16_7_at0 :
    prefix16_7.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 8))) ⟨0, rfl⟩ = ⟨178, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at1 :
    prefix16_7.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨1, rfl⟩ = ⟨179, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at2 :
    prefix16_7.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨2, rfl⟩ = ⟨180, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at3 :
    prefix16_7.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨3, rfl⟩ = ⟨181, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at4 :
    prefix16_7.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨4, rfl⟩ = ⟨182, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at5 :
    prefix16_7.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨5, rfl⟩ = ⟨183, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at6 :
    prefix16_7.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨6, rfl⟩ = ⟨184, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at7 :
    prefix16_7.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨7, rfl⟩ = ⟨185, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at8 :
    prefix16_7.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨8, rfl⟩ = ⟨186, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at9 :
    prefix16_7.contextHom (t := SLLVM.Ty.bitvec 64) ⟨9, rfl⟩ = ⟨187, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at10 :
    prefix16_7.contextHom (t := SLLVM.Ty.bitvec 64) ⟨10, rfl⟩ = ⟨188, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at11 :
    prefix16_7.contextHom (t := SLLVM.Ty.bitvec 64) ⟨11, rfl⟩ = ⟨189, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at12 :
    prefix16_7.contextHom (t := SLLVM.Ty.bitvec 64) ⟨12, rfl⟩ = ⟨190, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at13 :
    prefix16_7.contextHom (t := SLLVM.Ty.bitvec 64) ⟨13, rfl⟩ = ⟨191, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at14 :
    prefix16_7.contextHom (t := SLLVM.Ty.bitvec 64) ⟨14, rfl⟩ = ⟨192, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at15 :
    prefix16_7.contextHom (t := SLLVM.Ty.bitvec 64) ⟨15, rfl⟩ = ⟨193, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at16 :
    prefix16_7.contextHom (t := SLLVM.Ty.bitvec 64) ⟨16, rfl⟩ = ⟨194, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at17 :
    prefix16_7.contextHom (t := SLLVM.Ty.bitvec 64) ⟨17, rfl⟩ = ⟨195, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at18 :
    prefix16_7.contextHom (t := SLLVM.Ty.bitvec 64) ⟨18, rfl⟩ = ⟨196, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at19 :
    prefix16_7.contextHom (t := SLLVM.Ty.bitvec 64) ⟨19, rfl⟩ = ⟨197, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at20 :
    prefix16_7.contextHom (t := SLLVM.Ty.bitvec 64) ⟨20, rfl⟩ = ⟨198, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at21 :
    prefix16_7.contextHom (t := SLLVM.Ty.bitvec 64) ⟨21, rfl⟩ = ⟨199, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at22 :
    prefix16_7.contextHom (t := SLLVM.Ty.bitvec 64) ⟨22, rfl⟩ = ⟨200, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at23 :
    prefix16_7.contextHom (t := SLLVM.Ty.bitvec 64) ⟨23, rfl⟩ = ⟨201, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at24 :
    prefix16_7.contextHom (t := SLLVM.Ty.bitvec 64) ⟨24, rfl⟩ = ⟨202, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at25 :
    prefix16_7.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 64))) ⟨25, rfl⟩ = ⟨203, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_7_at26 :
    prefix16_7.contextHom (t := SLLVM.Ty.arith (.vector 8 (.bitvec 64))) ⟨26, rfl⟩ = ⟨204, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem finalMap16_10_at0 :
    finalMap16_10 (t := SLLVM.Ty.bitvec 1) ⟨0, rfl⟩ = ⟨0, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at1 :
    finalMap16_10 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨1, rfl⟩ = ⟨1, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at3 :
    finalMap16_10 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨3, rfl⟩ = ⟨3, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at4 :
    finalMap16_10 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨4, rfl⟩ = ⟨4, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at6 :
    finalMap16_10 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨6, rfl⟩ = ⟨6, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at23 :
    finalMap16_10 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨23, rfl⟩ = ⟨23, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at25 :
    finalMap16_10 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨25, rfl⟩ = ⟨25, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at26 :
    finalMap16_10 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨26, rfl⟩ = ⟨26, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at28 :
    finalMap16_10 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨28, rfl⟩ = ⟨28, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at45 :
    finalMap16_10 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨45, rfl⟩ = ⟨45, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at47 :
    finalMap16_10 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨47, rfl⟩ = ⟨47, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at48 :
    finalMap16_10 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨48, rfl⟩ = ⟨48, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at50 :
    finalMap16_10 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨50, rfl⟩ = ⟨50, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at67 :
    finalMap16_10 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨67, rfl⟩ = ⟨67, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at69 :
    finalMap16_10 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨69, rfl⟩ = ⟨69, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at70 :
    finalMap16_10 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨70, rfl⟩ = ⟨70, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at72 :
    finalMap16_10 (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨72, rfl⟩ = ⟨72, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem finalMap16_10_at177 :
    finalMap16_10 (t := SLLVM.Ty.bitvec 64) ⟨177, rfl⟩ = ⟨177, rfl⟩ := by
  apply Subtype.ext
  rfl
@[simp] theorem origin16_10_at0 :
    prefix16_10.contextHom (t := SLLVM.Ty.bitvec 64) ⟨0, rfl⟩ = ⟨178, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_10_at1 :
    prefix16_10.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨1, rfl⟩ = ⟨179, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_10_at2 :
    prefix16_10.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨2, rfl⟩ = ⟨180, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_10_at3 :
    prefix16_10.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨3, rfl⟩ = ⟨181, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_10_at4 :
    prefix16_10.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨4, rfl⟩ = ⟨182, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_10_at5 :
    prefix16_10.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨5, rfl⟩ = ⟨183, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_10_at6 :
    prefix16_10.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨6, rfl⟩ = ⟨184, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_10_at7 :
    prefix16_10.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨7, rfl⟩ = ⟨185, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_10_at8 :
    prefix16_10.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨8, rfl⟩ = ⟨186, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_10_at9 :
    prefix16_10.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨9, rfl⟩ = ⟨187, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
@[simp] theorem origin16_10_at10 :
    prefix16_10.contextHom (t := SLLVM.Ty.arith (.vector 16 (.bitvec 32))) ⟨10, rfl⟩ = ⟨188, rfl⟩ := by
  apply Subtype.ext
  rw [BlockPrefix.contextHom_val]
  rfl
end AgaveLatticeHash.MLIR.BatchRoundBranches
