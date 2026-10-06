/- Released under Apache 2.0 license as described in the file LICENSE. -/
import Std
import SSA.Projects.Agave.LatticeHash.Primitives

/-!
Word-level BLAKE3 compression and an independently evaluated lane-lifted core.

Constants and update order follow Firedancer's `fd_blake3_ref.c` and
`fd_blake3_private.h`. This is a specification-layer SIMD refinement theorem;
it does not claim a refinement theorem for C memory, machine instructions,
compiler lowering, batch dispatch, or the surrounding tree hash.

All words are `BitVec 32`; counters are `BitVec 64`.
The lane count is arbitrary, including zero (projection then has no inhabitant).
-/
namespace Blake3Compression

abbrev Word := BitVec 32
abbrev Byte := BitVec 8
abbrev Counter := BitVec 64
abbrev State (α : Type) := Fin 16 → α
abbrev CV (α : Type) := Fin 8 → α
abbrev Block (α : Type) := Fin 64 → α
abbrev Lanes (n : Nat) := Fin n → Word
abbrev Counters (n : Nat) := Fin n → Counter

structure Quad (α : Type) where
  a : α
  b : α
  c : α
  d : α

def project {n k : Nat} (s : Fin k → Lanes n) (lane : Fin n) : Fin k → Word :=
  fun i => s i lane

def projectQuad {n : Nat} (q : Quad (Lanes n)) (lane : Fin n) : Quad Word :=
  ⟨q.a lane, q.b lane, q.c lane, q.d lane⟩

/-- Scalar G: additions wrap modulo 2^32 and rotations are right rotations. -/
def scalarG (a b c d x y : Word) : Quad Word :=
  let a := a + b + x
  let d := (d ^^^ a).rotateRight 16
  let c := c + d
  let b := (b ^^^ c).rotateRight 12
  let a := a + b + y
  let d := (d ^^^ a).rotateRight 8
  let c := c + d
  let b := (b ^^^ c).rotateRight 7
  ⟨a, b, c, d⟩

/-- SIMD primitives: each operation applies to all lanes. -/
def laneAdd {n : Nat} (a b : Lanes n) : Lanes n := fun l => a l + b l
def laneXor {n : Nat} (a b : Lanes n) : Lanes n := fun l => a l ^^^ b l
def laneOr {n : Nat} (a b : Lanes n) : Lanes n := fun l => a l ||| b l
/-- AVX2 has no packed u32 rotate, so its four source arms use shift/or. -/
def avx2RotateWord (x : Word) (r : Nat) : Word :=
  match r with
  | 16 => (x >>> 16) ||| (x <<< 16)
  | 12 => (x >>> 12) ||| (x <<< 20)
  | 8 => (x >>> 8) ||| (x <<< 24)
  | 7 => (x >>> 7) ||| (x <<< 25)
  | _ => x.rotateRight r

theorem avx2RotateWord_eq (x : Word) (r : Nat) :
    avx2RotateWord x r = x.rotateRight r := by
  unfold avx2RotateWord
  split
  · exact AgaveLattice.ror16 x
  · exact AgaveLattice.ror12 x
  · exact AgaveLattice.ror8 x
  · exact AgaveLattice.ror7 x
  · rfl

/-- Width eight executes the AVX2 shift/or arms. Width sixteen executes the
    AVX-512 native rotate semantics. Other widths retain the scalar model. -/
def laneRotateRight {n : Nat} (a : Lanes n) (r : Nat) : Lanes n :=
  fun l => if n = 8 then avx2RotateWord (a l) r else (a l).rotateRight r

@[simp] theorem laneRotateRight_project {n : Nat} (a : Lanes n) (r : Nat)
    (l : Fin n) : laneRotateRight a r l = (a l).rotateRight r := by
  unfold laneRotateRight
  split
  · exact avx2RotateWord_eq _ _
  · rfl

/-- The SIMD G is assembled from SIMD operations, not a map of scalarG. -/
def laneG {n : Nat} (a b c d x y : Lanes n) : Quad (Lanes n) :=
  let a := laneAdd (laneAdd a b) x
  let d := laneRotateRight (laneXor d a) 16
  let c := laneAdd c d
  let b := laneRotateRight (laneXor b c) 12
  let a := laneAdd (laneAdd a b) y
  let d := laneRotateRight (laneXor d a) 8
  let c := laneAdd c d
  let b := laneRotateRight (laneXor b c) 7
  ⟨a, b, c, d⟩

@[simp] theorem laneG_project {n : Nat} (a b c d x y : Lanes n) (l : Fin n) :
    projectQuad (laneG a b c d x y) l = scalarG (a l) (b l) (c l) (d l) (x l) (y l) := by
  simp only [projectQuad, laneG, laneAdd, laneXor, laneRotateRight_project, scalarG]

abbrev GFn (α : Type) := α → α → α → α → α → α → Quad α

/-- Commit a G result to four state positions. The round uses distinct positions. -/
def gStep {α : Type} (g : GFn α) (s : State α)
    (a b c d : Fin 16) (x y : α) : State α :=
  let q := g (s a) (s b) (s c) (s d) x y
  fun i => if i = a then q.a else if i = b then q.b else
    if i = c then q.c else if i = d then q.d else s i

@[simp] theorem gStep_project {n : Nat} (s : State (Lanes n))
    (a b c d : Fin 16) (x y : Lanes n) (l : Fin n) :
    project (gStep laneG s a b c d x y) l =
      gStep scalarG (project s l) a b c d (x l) (y l) := by
  have hq := laneG_project (s a) (s b) (s c) (s d) x y l
  funext i
  simp only [project, gStep]
  split
  · exact congrArg Quad.a hq
  split
  · exact congrArg Quad.b hq
  split
  · exact congrArg Quad.c hq
  split
  · exact congrArg Quad.d hq
  · rfl

/-- Exact message schedule rows from FD_BLAKE3_MSG_SCHEDULE. -/
def messageSchedule : Vector (Vector (Fin 16) 16) 7 := #v[
  #v[ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,10,11,12,13,14,15],
  #v[ 2, 6, 3,10, 7, 0, 4,13, 1,11,12, 5, 9,14,15, 8],
  #v[ 3, 4,10,12,13, 2, 7,14, 6, 5, 9, 0,11,15, 8, 1],
  #v[10, 7,12, 9,14, 3,13,15, 4, 0,11, 2, 5, 8, 1, 6],
  #v[12,13, 9,11,15,10,14, 8, 7, 2, 5, 3, 0, 1, 6, 4],
  #v[ 9,14,11, 5, 8,12,15, 1,13, 3, 0,10, 2, 6, 4, 7],
  #v[11,15, 5, 0, 1, 9, 8, 6,14,10, 2,12, 3, 4, 7,13]]

def schedule (r : Fin 7) (i : Fin 16) : Fin 16 :=
  (messageSchedule.get r).get i

/-- One round: four column G operations followed by four diagonal G operations. -/
def roundFn {α : Type} (g : GFn α) (s : State α) (m : State α) (r : Fin 7) : State α :=
  let m := fun i => m (schedule r i)
  let s := gStep g s 0 4 8 12 (m 0) (m 1)
  let s := gStep g s 1 5 9 13 (m 2) (m 3)
  let s := gStep g s 2 6 10 14 (m 4) (m 5)
  let s := gStep g s 3 7 11 15 (m 6) (m 7)
  let s := gStep g s 0 5 10 15 (m 8) (m 9)
  let s := gStep g s 1 6 11 12 (m 10) (m 11)
  let s := gStep g s 2 7 8 13 (m 12) (m 13)
  gStep g s 3 4 9 14 (m 14) (m 15)

@[simp] theorem roundFn_project {n : Nat} (s m : State (Lanes n)) (r : Fin 7) (l : Fin n) :
    project (roundFn laneG s m r) l = roundFn scalarG (project s l) (project m l) r := by
  simp only [roundFn, gStep_project, project]

def rounds {α : Type} (g : GFn α) : List (Fin 7) → State α → State α → State α
  | [], s, _ => s
  | r :: rs, s, m => rounds g rs (roundFn g s m r) m

/-- Projection commutes with every round sequence, not just the BLAKE3 sequence. -/
theorem rounds_project {n : Nat} (rs : List (Fin 7)) (s m : State (Lanes n)) (l : Fin n) :
    project (rounds laneG rs s m) l = rounds scalarG rs (project s l) (project m l) := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    simp only [rounds, ih, roundFn_project]

def sevenRoundSchedule : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

def sevenRounds {α : Type} (g : GFn α) (s m : State α) : State α :=
  rounds g sevenRoundSchedule s m

theorem sevenRounds_project {n : Nat} (s m : State (Lanes n)) (l : Fin n) :
    project (sevenRounds laneG s m) l = sevenRounds scalarG (project s l) (project m l) :=
  rounds_project sevenRoundSchedule s m l

/-- Initialization is shared structural wiring; arithmetic remains word-specific. -/
def initState {α : Type} (cv : CV α) (constant : Word → α)
    (counterLow counterHigh blockLen flags : α) : State α :=
  fun i => match i.val with
  | 0 => cv 0 | 1 => cv 1 | 2 => cv 2 | 3 => cv 3
  | 4 => cv 4 | 5 => cv 5 | 6 => cv 6 | 7 => cv 7
  | 8 => constant 0x6A09E667 | 9 => constant 0xBB67AE85
  | 10 => constant 0x3C6EF372 | 11 => constant 0xA54FF53A
  | 12 => counterLow | 13 => counterHigh | 14 => blockLen | _ => flags

def scalarInit (cv : CV Word) (counter : Counter) (blockLen flags : Word) : State Word :=
  initState cv id (counter.extractLsb' 0 32) (counter.extractLsb' 32 32) blockLen flags

def laneInit {n : Nat} (cv : CV (Lanes n)) (counter : Counters n)
    (blockLen flags : Lanes n) : State (Lanes n) :=
  initState cv (fun w _ => w) (fun l => (counter l).extractLsb' 0 32)
    (fun l => (counter l).extractLsb' 32 32) blockLen flags

@[simp] theorem laneInit_project {n : Nat} (cv : CV (Lanes n)) (counter : Counters n)
    (blockLen flags : Lanes n) (l : Fin n) :
    project (laneInit cv counter blockLen flags) l =
      scalarInit (project cv l) (counter l) (blockLen l) (flags l) := by
  funext i
  simp only [project, laneInit, scalarInit, initState]
  split <;> simp_all

def scalarCompressPre (cv : CV Word) (m : State Word) (counter : Counter)
    (blockLen flags : Word) : State Word :=
  sevenRounds scalarG (scalarInit cv counter blockLen flags) m

def laneCompressPre {n : Nat} (cv : CV (Lanes n)) (m : State (Lanes n))
    (counter : Counters n) (blockLen flags : Lanes n) : State (Lanes n) :=
  sevenRounds laneG (laneInit cv counter blockLen flags) m

@[simp] theorem laneCompressPre_project {n : Nat} (cv : CV (Lanes n)) (m : State (Lanes n))
    (counter : Counters n) (blockLen flags : Lanes n) (l : Fin n) :
    project (laneCompressPre cv m counter blockLen flags) l =
      scalarCompressPre (project cv l) (project m l) (counter l) (blockLen l) (flags l) := by
  simp only [laneCompressPre, scalarCompressPre, sevenRounds_project, laneInit_project]

/-- Low half is state[0..7] XOR state[8..15]; high half is state[8..15] XOR input CV. -/
def feedForward {α : Type} (xor : α → α → α) (cv : CV α) (s : State α) : State α :=
  fun i => if h : i.val < 8 then
      xor (s i) (s ⟨i.val + 8, by omega⟩)
    else xor (s i) (cv ⟨i.val - 8, by omega⟩)

@[simp] theorem feedForward_project {n : Nat} (cv : CV (Lanes n))
    (s : State (Lanes n)) (l : Fin n) :
    project (feedForward laneXor cv s) l =
      feedForward (· ^^^ ·) (project cv l) (project s l) := by
  funext i
  simp only [feedForward, project]
  split <;> rfl

def scalarCompress (cv : CV Word) (m : State Word) (counter : Counter)
    (blockLen flags : Word) : State Word :=
  feedForward (· ^^^ ·) cv (scalarCompressPre cv m counter blockLen flags)

def laneCompress {n : Nat} (cv : CV (Lanes n)) (m : State (Lanes n))
    (counter : Counters n) (blockLen flags : Lanes n) : State (Lanes n) :=
  feedForward laneXor cv (laneCompressPre cv m counter blockLen flags)

/-- Full 16-word compression equivalence for every lane and arbitrary inputs. -/
theorem laneCompress_project {n : Nat} (cv : CV (Lanes n)) (m : State (Lanes n))
    (counter : Counters n) (blockLen flags : Lanes n) (l : Fin n) :
    project (laneCompress cv m counter blockLen flags) l =
      scalarCompress (project cv l) (project m l) (counter l) (blockLen l) (flags l) := by
  simp only [laneCompress, scalarCompress, feedForward_project, laneCompressPre_project]

def scalarCompressCV (cv : CV Word) (m : State Word) (counter : Counter)
    (blockLen flags : Word) : CV Word :=
  fun i => scalarCompress cv m counter blockLen flags (i.castAdd 8)

def laneCompressCV {n : Nat} (cv : CV (Lanes n)) (m : State (Lanes n))
    (counter : Counters n) (blockLen flags : Lanes n) : CV (Lanes n) :=
  fun i => laneCompress cv m counter blockLen flags (i.castAdd 8)

theorem laneCompressCV_project {n : Nat} (cv : CV (Lanes n)) (m : State (Lanes n))
    (counter : Counters n) (blockLen flags : Lanes n) (l : Fin n) :
    project (laneCompressCV cv m counter blockLen flags) l =
      scalarCompressCV (project cv l) (project m l) (counter l) (blockLen l) (flags l) := by
  funext i
  exact congrFun (laneCompress_project cv m counter blockLen flags l) (i.castAdd 8)

/-- Serialize all 16 output words to 64 bytes, in little-endian order. -/
def scalarSerialize (s : State Word) : Block Byte :=
  fun i => (s ⟨i.val / 4, by omega⟩).extractLsb' (8 * (i.val % 4)) 8

def laneSerialize {n : Nat} (s : State (Lanes n)) : Block (Fin n → Byte) :=
  fun i l => (s ⟨i.val / 4, by omega⟩ l).extractLsb' (8 * (i.val % 4)) 8

theorem laneSerialize_project {n : Nat} (s : State (Lanes n)) (l : Fin n) :
    (fun i => laneSerialize s i l) = scalarSerialize (project s l) := by
  rfl

/-- One root XOF output block; the counter is the 64-byte output-block index. -/
def scalarXofBlock (cv : CV Word) (m : State Word) (outputCounter : Counter)
    (blockLen flags : Word) : Block Byte :=
  scalarSerialize (scalarCompress cv m outputCounter blockLen (flags ||| 8))

def laneXofBlock {n : Nat} (cv : CV (Lanes n)) (m : State (Lanes n))
    (outputCounter : Counters n) (blockLen flags : Lanes n) : Block (Fin n → Byte) :=
  laneSerialize (laneCompress cv m outputCounter blockLen (laneOr flags (fun _ => 8)))

/-- Every byte of every lane's root XOF block equals scalar compression. -/
theorem laneXofBlock_project {n : Nat} (cv : CV (Lanes n)) (m : State (Lanes n))
    (outputCounter : Counters n) (blockLen flags : Lanes n) (l : Fin n) :
    (fun i => laneXofBlock cv m outputCounter blockLen flags i l) =
      scalarXofBlock (project cv l) (project m l) (outputCounter l) (blockLen l) (flags l) := by
  unfold laneXofBlock scalarXofBlock
  rw [laneSerialize_project, laneCompress_project]
  rfl

end Blake3Compression

#print axioms Blake3Compression.laneG_project
#print axioms Blake3Compression.roundFn_project
#print axioms Blake3Compression.rounds_project
#print axioms Blake3Compression.sevenRounds_project
#print axioms Blake3Compression.laneCompressPre_project
#print axioms Blake3Compression.laneCompress_project
#print axioms Blake3Compression.laneCompressCV_project
#print axioms Blake3Compression.laneXofBlock_project
