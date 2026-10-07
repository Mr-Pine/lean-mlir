import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGBlocks
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Ladder

namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Tables (F)
open Avx2PointAdd (Point pointReduced pointValue)
open Avx2PointAdd.Phases
set_option maxRecDepth 10000

def additionIndex5 (a pos : Nat) : Fin 64 :=
  ⟨(nafMagnitude5 a pos).val / 2, by have h := (nafMagnitude5 a pos).isLt; omega⟩

def additionIndex8 (b pos : Nat) : Fin 64 :=
  ⟨(nafMagnitude8 b pos).val / 2, by have h := (nafMagnitude8 b pos).isLt; omega⟩

/-- Static register facts for bb22; point registers and the proved digit index are supplied separately. -/
structure AdditionStatic22 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch) (base : Pointer) : Prop where
  constants : Avx2PointAdd.CFG.Constants E
  r3 : E.read (%3) = .value 32#64
  r20 : E.read (%20) = .value 64#64
  r21 : E.read (%21) = .value 96#64
  r22 : E.read (%22) = .value 128#64
  r153 : E.read (%153) = .value 160#64
  r250 : E.read (%250) = .value q.right
  r251 : E.read (%251) = .value q.left
  r252 : E.read (%252) = .value q.product
  r253 : E.read (%253) = .value q.prepared
  r254 : E.read (%254) = .value q.negative
  r261 : E.read (%261) = .value q.output
  r264 : E.read (%264) = .value base
  r355 : E.read (%355) = .value (q.negative.add 32#64)
  r356 : E.read (%356) = .value (q.negative.add 64#64)
  r357 : E.read (%357) = .value (q.negative.add 96#64)
  r358 : E.read (%358) = .value (q.negative.add 128#64)
  r359 : E.read (%359) = .value (q.prepared.add 32#64)
  r360 : E.read (%360) = .value (q.prepared.add 64#64)
  r361 : E.read (%361) = .value (q.prepared.add 96#64)
  r362 : E.read (%362) = .value (q.prepared.add 128#64)
  r363 : E.read (%363) = .value (q.left.add 32#64)
  r364 : E.read (%364) = .value (q.left.add 64#64)
  r365 : E.read (%365) = .value (q.left.add 96#64)
  r366 : E.read (%366) = .value (q.left.add 128#64)
  r367 : E.read (%367) = .value (q.right.add 32#64)
  r368 : E.read (%368) = .value (q.right.add 64#64)
  r369 : E.read (%369) = .value (q.right.add 96#64)
  r370 : E.read (%370) = .value (q.right.add 128#64)
  r371 : E.read (%371) = .value (q.output.add 32#64)
  r372 : E.read (%372) = .value (q.output.add 64#64)
  r373 : E.read (%373) = .value (q.output.add 96#64)
  r374 : E.read (%374) = .value (q.output.add 128#64)

theorem AdditionStatic22.input (h : AdditionStatic22 E q base)
    (hp : PointReads .doubled E P)
    (hi : E.read (%527) = .value (BitVec.ofNat 64 index.val)) :
    Avx2PointAdd.CFG.Input22 E q base index P := by
  refine ⟨h.constants, h.r3, h.r20, h.r21, h.r22, h.r153, h.r250, h.r251, h.r252, h.r253, h.r254, h.r261, h.r264, h.r355, h.r356, h.r357, h.r358, h.r359, h.r360, h.r361, h.r362, h.r363, h.r364, h.r365, h.r366, h.r367, h.r368, h.r369, h.r370, h.r371, h.r372, h.r373, h.r374, ?_, ?_, ?_, ?_, ?_, hi⟩
  · simpa [pointReg] using hp 0
  · simpa [pointReg] using hp 1
  · simpa [pointReg] using hp 2
  · simpa [pointReg] using hp 3
  · simpa [pointReg] using hp 4

/-- Static register facts for bb25; point registers and the proved digit index are supplied separately. -/
structure AdditionStatic25 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch) (base : Pointer) : Prop where
  constants : Avx2PointAdd.CFG.Constants E
  r153 : E.read (%153) = .value 160#64
  r246 : E.read (%246) = .value q.right
  r247 : E.read (%247) = .value q.left
  r248 : E.read (%248) = .value q.product
  r249 : E.read (%249) = .value q.prepared
  r262 : E.read (%262) = .value q.output
  r264 : E.read (%264) = .value base
  r339 : E.read (%339) = .value (q.prepared.add 32#64)
  r340 : E.read (%340) = .value (q.prepared.add 64#64)
  r341 : E.read (%341) = .value (q.prepared.add 96#64)
  r342 : E.read (%342) = .value (q.prepared.add 128#64)
  r343 : E.read (%343) = .value (q.left.add 32#64)
  r344 : E.read (%344) = .value (q.left.add 64#64)
  r345 : E.read (%345) = .value (q.left.add 96#64)
  r346 : E.read (%346) = .value (q.left.add 128#64)
  r347 : E.read (%347) = .value (q.right.add 32#64)
  r348 : E.read (%348) = .value (q.right.add 64#64)
  r349 : E.read (%349) = .value (q.right.add 96#64)
  r350 : E.read (%350) = .value (q.right.add 128#64)
  r351 : E.read (%351) = .value (q.output.add 32#64)
  r352 : E.read (%352) = .value (q.output.add 64#64)
  r353 : E.read (%353) = .value (q.output.add 96#64)
  r354 : E.read (%354) = .value (q.output.add 128#64)

theorem AdditionStatic25.input (h : AdditionStatic25 E q base)
    (hp : PointReads .doubled E P)
    (hi : E.read (%625) = .value (BitVec.ofNat 64 index.val)) :
    Avx2PointAdd.CFG.Input25 E q base index P := by
  refine ⟨h.constants, h.r153, h.r246, h.r247, h.r248, h.r249, h.r262, h.r264, h.r339, h.r340, h.r341, h.r342, h.r343, h.r344, h.r345, h.r346, h.r347, h.r348, h.r349, h.r350, h.r351, h.r352, h.r353, h.r354, ?_, ?_, ?_, ?_, ?_, hi⟩
  · simpa [pointReg] using hp 0
  · simpa [pointReg] using hp 1
  · simpa [pointReg] using hp 2
  · simpa [pointReg] using hp 3
  · simpa [pointReg] using hp 4

/-- Static register facts for bb29; point registers and the proved digit index are supplied separately. -/
structure AdditionStatic29 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch) (base : Pointer) : Prop where
  constants : Avx2PointAdd.CFG.Constants E
  r3 : E.read (%3) = .value 32#64
  r20 : E.read (%20) = .value 64#64
  r21 : E.read (%21) = .value 96#64
  r22 : E.read (%22) = .value 128#64
  r153 : E.read (%153) = .value 160#64
  r224 : E.read (%224) = .value base
  r241 : E.read (%241) = .value q.right
  r242 : E.read (%242) = .value q.left
  r243 : E.read (%243) = .value q.product
  r244 : E.read (%244) = .value q.prepared
  r245 : E.read (%245) = .value q.negative
  r259 : E.read (%259) = .value q.output
  r391 : E.read (%391) = .value (q.negative.add 32#64)
  r392 : E.read (%392) = .value (q.negative.add 64#64)
  r393 : E.read (%393) = .value (q.negative.add 96#64)
  r394 : E.read (%394) = .value (q.negative.add 128#64)
  r395 : E.read (%395) = .value (q.prepared.add 32#64)
  r396 : E.read (%396) = .value (q.prepared.add 64#64)
  r397 : E.read (%397) = .value (q.prepared.add 96#64)
  r398 : E.read (%398) = .value (q.prepared.add 128#64)
  r399 : E.read (%399) = .value (q.left.add 32#64)
  r400 : E.read (%400) = .value (q.left.add 64#64)
  r401 : E.read (%401) = .value (q.left.add 96#64)
  r402 : E.read (%402) = .value (q.left.add 128#64)
  r403 : E.read (%403) = .value (q.right.add 32#64)
  r404 : E.read (%404) = .value (q.right.add 64#64)
  r405 : E.read (%405) = .value (q.right.add 96#64)
  r406 : E.read (%406) = .value (q.right.add 128#64)
  r407 : E.read (%407) = .value (q.output.add 32#64)
  r408 : E.read (%408) = .value (q.output.add 64#64)
  r409 : E.read (%409) = .value (q.output.add 96#64)
  r410 : E.read (%410) = .value (q.output.add 128#64)

theorem AdditionStatic29.input (h : AdditionStatic29 E q base)
    (hp : PointReads .afterA E P)
    (hi : E.read (%708) = .value (BitVec.ofNat 64 index.val)) :
    Avx2PointAdd.CFG.Input29 E q base index P := by
  refine ⟨h.constants, h.r3, h.r20, h.r21, h.r22, h.r153, h.r224, h.r241, h.r242, h.r243, h.r244, h.r245, h.r259, h.r391, h.r392, h.r393, h.r394, h.r395, h.r396, h.r397, h.r398, h.r399, h.r400, h.r401, h.r402, h.r403, h.r404, h.r405, h.r406, h.r407, h.r408, h.r409, h.r410, ?_, ?_, ?_, ?_, ?_, hi⟩
  · simpa [pointReg] using hp 3
  · simpa [pointReg] using hp 2
  · simpa [pointReg] using hp 1
  · simpa [pointReg] using hp 0
  · simpa [pointReg] using hp 4

/-- Static register facts for bb33; point registers and the proved digit index are supplied separately. -/
structure AdditionStatic33 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch) (base : Pointer) : Prop where
  constants : Avx2PointAdd.CFG.Constants E
  r153 : E.read (%153) = .value 160#64
  r224 : E.read (%224) = .value base
  r237 : E.read (%237) = .value q.right
  r238 : E.read (%238) = .value q.left
  r239 : E.read (%239) = .value q.product
  r240 : E.read (%240) = .value q.prepared
  r260 : E.read (%260) = .value q.output
  r375 : E.read (%375) = .value (q.prepared.add 32#64)
  r376 : E.read (%376) = .value (q.prepared.add 64#64)
  r377 : E.read (%377) = .value (q.prepared.add 96#64)
  r378 : E.read (%378) = .value (q.prepared.add 128#64)
  r379 : E.read (%379) = .value (q.left.add 32#64)
  r380 : E.read (%380) = .value (q.left.add 64#64)
  r381 : E.read (%381) = .value (q.left.add 96#64)
  r382 : E.read (%382) = .value (q.left.add 128#64)
  r383 : E.read (%383) = .value (q.right.add 32#64)
  r384 : E.read (%384) = .value (q.right.add 64#64)
  r385 : E.read (%385) = .value (q.right.add 96#64)
  r386 : E.read (%386) = .value (q.right.add 128#64)
  r387 : E.read (%387) = .value (q.output.add 32#64)
  r388 : E.read (%388) = .value (q.output.add 64#64)
  r389 : E.read (%389) = .value (q.output.add 96#64)
  r390 : E.read (%390) = .value (q.output.add 128#64)

theorem AdditionStatic33.input (h : AdditionStatic33 E q base)
    (hp : PointReads .afterA E P)
    (hi : E.read (%813) = .value (BitVec.ofNat 64 index.val)) :
    Avx2PointAdd.CFG.Input33 E q base index P := by
  refine ⟨h.constants, h.r153, h.r224, h.r237, h.r238, h.r239, h.r240, h.r260, h.r375, h.r376, h.r377, h.r378, h.r379, h.r380, h.r381, h.r382, h.r383, h.r384, h.r385, h.r386, h.r387, h.r388, h.r389, h.r390, ?_, ?_, ?_, ?_, ?_, hi⟩
  · simpa [pointReg] using hp 3
  · simpa [pointReg] using hp 2
  · simpa [pointReg] using hp 1
  · simpa [pointReg] using hp 0
  · simpa [pointReg] using hp 4

/-- The cache relation concerns stored input bytes and their represented table
entry. Context preservation is only a scratch-memory frame property. -/
structure AdditionMemory (ctx : LocalContext) (table : TableIndex → Extended F)
    (side : Bool) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (da db : Pointer)
    (q : Scratch) (base : Pointer) (index : Fin 64) (bytes : Nat) : Prop where
  memory : MemoryReady s q (tableRow base index)
  tableRange : Reduce64.Execution.SmallRange s.mem base bytes
  indexRange : 160 * index.val + 160 ≤ bytes
  cache : ∃ C : Point, pointReduced C ∧
    Avx2FieldMul.Execution.readBlocks s.mem (tableRow base index) = packPoint C ∧
    pointValue C = avx2Cache (table (side, index.val))
  digitsA : ∀ k, (q.written k).id ≠ da.id
  digitsB : ∀ k, (q.written k).id ≠ db.id
  contextFrame : ∀ s', OutputFrame q s s' → ctx E s'

theorem DigitMemory.of_pointAddFrame (h : DigitMemory s da db a b)
    (hf : OutputFrame q s s')
    (ha : ∀ k, (q.written k).id ≠ da.id)
    (hb : ∀ k, (q.written k).id ≠ db.id) : DigitMemory s' da db a b := by
  refine ⟨hf.live da 256 h.bufferA, hf.live db 256 h.bufferB, ?_, ?_⟩
  · intro i
    exact (hf.read _ 8 (by simpa using ha)).trans (h.readA i)
  · intro i
    exact (hf.read _ 8 (by simpa using hb)).trans (h.readB i)

theorem LadderReady.of_pointAddFrame (hs : ContextStable ctx)
    (h : LadderReady ctx a b da db E s pos)
    (hm : AdditionMemory ctx table side E s da db q base index bytes)
    (hf : OutputFrame q s s') (hr : RegisterFrame 427 avx2Kernel.Γ.n E E') :
    LadderReady ctx a b da db E' s' pos :=
  ⟨h.control.of_frame hr, cursor_of_frame pos hr h.cursor,
    h.digits.of_pointAddFrame hf hm.digitsA hm.digitsB,
    hs E E' s' (hr.weaken (by decide) (Nat.le_refl _)) (hm.contextFrame s' hf)⟩

end Agave.Ed25519.DoubleBase.ExecutionAvx2
