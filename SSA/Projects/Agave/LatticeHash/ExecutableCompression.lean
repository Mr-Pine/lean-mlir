/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.Equivalence

/-!
Materialized BLAKE3 evaluators and proofs that they implement the scalar model.
The evaluators support kernel reduction and executable fixture checks; this
module contains no fixtures or executable tests.
-/
namespace Blake3Compression.Executable

/-- Materialized states make compression evaluation efficient. -/
def vectorStep (s : Vector Word 16) (a b c d : Fin 16) (x y : Word) : Vector Word 16 :=
  Vector.ofFn (gStep scalarG s.get a b c d x y)

@[simp] theorem ofFn_get (s : State Word) : (Vector.ofFn s).get = s := by
  funext i
  simp [Vector.get]
  rfl

@[simp] theorem vectorStep_get (s : Vector Word 16) (a b c d : Fin 16) (x y : Word) :
    (vectorStep s a b c d x y).get = gStep scalarG s.get a b c d x y := by
  exact ofFn_get _

def vectorRound (s : Vector Word 16) (m : State Word) (r : Fin 7) : Vector Word 16 :=
  let m := fun i => m (schedule r i)
  let s := vectorStep s 0 4 8 12 (m 0) (m 1)
  let s := vectorStep s 1 5 9 13 (m 2) (m 3)
  let s := vectorStep s 2 6 10 14 (m 4) (m 5)
  let s := vectorStep s 3 7 11 15 (m 6) (m 7)
  let s := vectorStep s 0 5 10 15 (m 8) (m 9)
  let s := vectorStep s 1 6 11 12 (m 10) (m 11)
  let s := vectorStep s 2 7 8 13 (m 12) (m 13)
  vectorStep s 3 4 9 14 (m 14) (m 15)

@[simp] theorem vectorRound_get (s : Vector Word 16) (m : State Word) (r : Fin 7) :
    (vectorRound s m r).get = roundFn scalarG s.get m r := by
  simp only [vectorRound, vectorStep_get, roundFn]

def vectorRounds : List (Fin 7) → Vector Word 16 → State Word → Vector Word 16
  | [], s, _ => s
  | r :: rs, s, m => vectorRounds rs (vectorRound s m r) m

@[simp] theorem vectorRounds_get (rs : List (Fin 7)) (s : Vector Word 16) (m : State Word) :
    (vectorRounds rs s m).get = rounds scalarG rs s.get m := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => simp only [vectorRounds, ih, rounds, vectorRound_get]

def vectorCompress (cv : CV Word) (m : State Word) (counter : Counter)
    (blockLen flags : Word) : State Word :=
  let s := vectorRounds sevenRoundSchedule (Vector.ofFn (scalarInit cv counter blockLen flags)) m
  feedForward (· ^^^ ·) cv s.get

theorem vectorCompress_eq (cv : CV Word) (m : State Word) (counter : Counter) (blockLen flags : Word) :
    vectorCompress cv m counter blockLen flags = scalarCompress cv m counter blockLen flags := by
  simp only [vectorCompress, vectorRounds_get, ofFn_get, scalarCompress,
    scalarCompressPre, sevenRounds]

def vectorXofBlock (cv : CV Word) (m : State Word) (counter : Counter) (blockLen flags : Word) : Block Byte :=
  scalarSerialize (vectorCompress cv m counter blockLen (flags ||| 8))

theorem vectorXofBlock_eq (cv : CV Word) (m : State Word) (counter : Counter) (blockLen flags : Word) :
    vectorXofBlock cv m counter blockLen flags = scalarXofBlock cv m counter blockLen flags := by
  rw [vectorXofBlock, vectorCompress_eq]
  rfl

/-- Materialize the compression output to prevent repeated executable recomputation. -/
def vectorCompressState (cv : CV Word) (m : State Word) (counter : Counter)
    (blockLen flags : Word) : Vector Word 16 :=
  let s := vectorRounds sevenRoundSchedule (Vector.ofFn (scalarInit cv counter blockLen flags)) m
  Vector.ofFn (feedForward (· ^^^ ·) cv s.get)

theorem vectorCompressState_get (cv : CV Word) (m : State Word) (counter : Counter)
    (blockLen flags : Word) :
    (vectorCompressState cv m counter blockLen flags).get = scalarCompress cv m counter blockLen flags := by
  simp only [vectorCompressState, ofFn_get, vectorRounds_get, scalarCompress,
    scalarCompressPre, sevenRounds]

/-- Materialize all eight CV words between successive input blocks. -/
def vectorPrefix (message : Nat → Byte) (len : Nat) : Nat → Vector Word 8
  | 0 => Vector.ofFn AgaveConcrete.iv
  | j + 1 =>
    let out := vectorCompressState (vectorPrefix message len j).get
      (AgaveConcrete.decodeBlock (AgaveBatchControl.scalarBlock message len j))
      0 64 (if j = 0 then 1 else 0)
    Vector.ofFn (fun i => out.get (i.castAdd 8))

theorem vectorPrefix_get (message : Nat → Byte) (len j : Nat) :
    (vectorPrefix message len j).get =
      AgaveBatchControl.scalarPrefix AgaveConcrete.compress AgaveConcrete.iv message len j := by
  induction j with
  | zero =>
    funext i
    simp [vectorPrefix, AgaveBatchControl.scalarPrefix, Vector.get]
    rfl
  | succ j ih =>
    have get8 (s : CV Word) : (Vector.ofFn s).get = s := by
      funext i
      simp [Vector.get]
      rfl
    simp only [vectorPrefix, get8, vectorCompressState_get, ih,
      AgaveBatchControl.scalarPrefix, AgaveConcrete.compress]
    split <;> rfl

/-- Exact executable scalar XOF, with materialized CVs only as an evaluation optimization. -/
def vectorChunkBlock (message : Nat → Byte) (len : Nat) (out : Fin 32) : Vector Byte 64 :=
  let cv := vectorPrefix message len (AgaveBatchControl.rootIndex len)
  let state := vectorCompressState cv.get
    (AgaveConcrete.decodeBlock (AgaveBatchControl.scalarBlock message len
      (AgaveBatchControl.rootIndex len)))
    (BitVec.ofNat 64 out.val)
    (BitVec.ofNat 32 (AgaveBatchControl.scalarRootSize len))
    (BitVec.ofNat 32 (AgaveBatchControl.scalarRootFlags len))
  Vector.ofFn (scalarSerialize state.get)

theorem vectorChunkBlock_eq (m : AgaveConcrete.Message) (out : Fin 32) :
    (vectorChunkBlock (AgaveConcrete.bytes m) m.length out).get =
      scalarSerialize (AgaveConcrete.oneChunkWords m out) := by
  have get64 (s : Block Byte) : (Vector.ofFn s).get = s := by
    funext i
    exact Vector.getElem_ofFn i.isLt
  simp only [vectorChunkBlock, get64, vectorCompressState_get, vectorPrefix_get,
    AgaveConcrete.oneChunkWords, AgaveBatchControl.scalarXofAt, AgaveConcrete.xof,
    AgaveConcrete.counter, Nat.mul_zero, Nat.add_zero]

end Blake3Compression.Executable
