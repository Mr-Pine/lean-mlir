import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionMachine
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionWords
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Packing

namespace Agave.Ed25519.Avx2FieldMul.Execution
open LeanMLIR.RIR

/-- Four parallel raw-word columns, prior to the common reduce64 schedule. -/
def rawColumns4 (a b : Blocks) : Reduce64.Execution.Columns4 :=
  fun k => Vector.ofFn fun lane => rawColumn (unpackBlocks a lane) (unpackBlocks b lane) k

def inputNat (a : Blocks) (lane : Fin 4) : Limbs :=
  fun i => (unpackBlocks a lane i).toNat

theorem rawColumn_toNat (a b : RawLimbs)
    (ha : LeftBound (fun i => (a i).toNat))
    (hb : RightBound (fun i => (b i).toNat)) (k : Fin 10) :
    (rawColumn a b k).toNat = column (fun i => (a i).toNat) (fun i => (b i).toNat) k := by
  have hw := rawColumn_eq_wordColumn ha hb k
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hw
  rw [hw]
  exact asymmetric_wordColumn_toNat ha hb k

theorem rawColumns4_toNat (a b : Blocks) (lane : Fin 4)
    (ha : LeftBound (inputNat a lane)) (hb : RightBound (inputNat b lane))
    (k : Fin 10) :
    ((rawColumns4 a b k)[lane]).toNat = column (inputNat a lane) (inputNat b lane) k := by
  unfold inputNat at *
  simpa [rawColumns4] using rawColumn_toNat (unpackBlocks a lane)
    (unpackBlocks b lane) ha hb k

theorem rawColumns4_bound (a b : Blocks) (lane : Fin 4)
    (ha : LeftBound (inputNat a lane)) (hb : RightBound (inputNat b lane)) :
    Reduce64.ColumnsBound (fun k => ((rawColumns4 a b k)[lane]).toNat) := by
  intro k
  change ((rawColumns4 a b k)[lane]).toNat < 2^63
  rw [rawColumns4_toNat a b lane ha hb]
  exact asymmetric_column_lt_i64 ha hb k

end Agave.Ed25519.Avx2FieldMul.Execution
