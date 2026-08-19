#!/usr/bin/env python3
"""Generate SSA/Projects/Firedancer/Avx512/Proof/fd_r43x6_quad_mul_fast.lean.

Mirrors the data flow of the lifted region (instruction indices %0-%92) at the
N level, over the `pl`/`ph` limb functions of Spec/Common.lean and the QUAD
layout of Spec/Quad.lean.

Usage: gen_quad_mul_proof.py [--upto N]   (truncate after %N, close with sorry)
"""
import re
import sys

ARGV = sys.argv[1:]
UPTO = int(ARGV[1]) if len(ARGV) >= 2 and ARGV[0] == '--upto' else None

# The valuation the derivation reads its block arguments from; every `simp only`
# that unfolds a block argument has to name it.
VAL = 'quadValMem6'


# ---------------------------------------------------------------- lane algebra
# Lane i of a QUAD vector holds element i%4.  The three x-vectors are shuffled
# into per-limb broadcasts, so lane i of `X k` is limb k of element i%4.  The
# y-vectors are read directly, so lane i of arg3/4/5 is limb 0/1/2 of element
# i%4 in the low half and limb 3/4/5 in the high half.

def el(i):  return i % 4
def yo(i):  return 0 if i < 4 else 3

def Xl(k, i): return f"X {el(i)} {k}"
def Yl(m, i): return f"Y {el(i)} {m + yo(i)}"

def pl_(k, m, i):  return f"pl ({Xl(k,i)}) ({Yl(m,i)})"
def ph_(k, m, i):  return f"ph ({Xl(k,i)}) ({Yl(m,i)})"
def phR(k, m, i):  return f"phRaw ({Xl(k,i)}) ({Yl(m,i)})"

def sum_lanes(f, pairs):
    """Left-associated accumulation, as the madd52 chain builds it."""
    return [ " + ".join(f(k, m, i) for (k, m) in pairs) for i in range(8) ]

# ------------------------------------------------------------------ the chains
# madd52lo chains: partial column I in the low half, column I+3 in the high.
LO = {
  12: [(0,0)],
  13: [(1,0)],                  14: [(1,0),(0,1)],
  15: [(2,0)],                  16: [(2,0),(1,1)],           17: [(2,0),(1,1),(0,2)],
  18: [(3,0)],                  19: [(3,0),(2,1)],           20: [(3,0),(2,1),(1,2)],
  21: [(4,0)],                  22: [(4,0),(3,1)],           23: [(4,0),(3,1),(2,2)],
  24: [(5,0)],                  25: [(5,0),(4,1)],           26: [(5,0),(4,1),(3,2)],
  27: [(5,1)],                  28: [(5,1),(4,2)],
  29: [(5,2)],
}
# madd52hi chains, accumulated raw and shifted by 9 as a whole.
HI = {
  30: [(0,0)],
  33: [(1,0)],                  34: [(1,0),(0,1)],
  37: [(2,0)],                  38: [(2,0),(1,1)],           39: [(2,0),(1,1),(0,2)],
  42: [(3,0)],                  43: [(3,0),(2,1)],           44: [(3,0),(2,1),(1,2)],
  47: [(4,0)],                  48: [(4,0),(3,1)],           49: [(4,0),(3,1),(2,2)],
  52: [(5,0)],                  53: [(5,0),(4,1)],           54: [(5,0),(4,1),(3,2)],
  57: [(5,1)],                  58: [(5,1),(4,2)],
  61: [(5,2)],
}
# shl-by-9 of a hi accumulator, and the add that folds it into the lo partial.
SHL9 = {31: 30, 35: 34, 40: 39, 45: 44, 50: 49, 55: 54, 59: 58, 62: 61}
FOLD = {32: (31, 14), 36: (35, 17), 41: (40, 20), 46: (45, 23),
        51: (50, 26), 56: (55, 28), 60: (59, 29)}

val = {}          # index -> list of 8 lane strings

# %6-%11: the limb broadcasts, `wwl_pack_halves( x03,0, x03,0 )` and friends
for i, k in ((6, 0), (7, 1), (8, 2), (9, 3), (10, 4), (11, 5)):
    val[i] = [Xl(k, j) for j in range(8)]

for i, pairs in LO.items():
    val[i] = sum_lanes(pl_, pairs)
for i, pairs in HI.items():
    val[i] = sum_lanes(phR, pairs)
for i, src in SHL9.items():
    val[i] = sum_lanes(ph_, HI[src])          # (raw sum) * 512 = sum of ph
for i, (hi, lo) in FOLD.items():
    val[i] = [f"({val[hi][j]}) + ({val[lo][j]})" for j in range(8)]

# The eight completed partial columns: low half column I, high half column I+3.
P = {0: 12, 1: 32, 2: 36, 3: 41, 4: 46, 5: 51, 6: 56, 7: 60, 8: 62}

def swap(v):      return [v[(j+4) % 8] for j in range(8)]
def blend(u, w):  return u[0:4] + w[4:8]

# half swaps of the columns that straddle both halves
for i, src in ((63, 41), (64, 46), (65, 51)):
    val[i] = swap(val[src])

# za: low half already column I, high half needs the swapped partial added
for i, (sw, base) in ((66, (63, 12)), (68, (64, 32)), (70, (65, 36))):
    val[i] = [f"({val[sw][j]}) + ({val[base][j]})" for j in range(8)]
for i, (base, add) in ((67, (12, 66)), (69, (32, 68)), (71, (36, 70))):
    val[i] = blend(val[base], val[add])

# zb: mirror image
for i, (a, b) in ((72, (56, 63)), (74, (60, 64)), (76, (62, 65))):
    val[i] = [f"({val[a][j]}) + ({val[b][j]})" for j in range(8)]
for i, (base, keep) in ((73, (72, 56)), (75, (74, 60)), (77, (76, 62))):
    val[i] = blend(val[base], val[keep])

# za + 152*zb, as shl 7 plus mul 24
for shl7, add1, mul24, add2, za, zb in (
        (78, 79, 80, 81, 67, 73),
        (82, 83, 84, 85, 69, 75),
        (86, 87, 88, 89, 71, 77)):
    val[shl7] = [f"({val[zb][j]}) * 128" for j in range(8)]
    val[add1] = [f"({val[shl7][j]}) + ({val[za][j]})" for j in range(8)]
    val[mul24] = [f"({val[zb][j]}) * 24" for j in range(8)]
    val[add2] = [f"({val[add1][j]}) + ({val[mul24][j]})" for j in range(8)]



# The 24 lanes of the kernel's result: the three output vectors, in the order
# `quadCat` concatenates them. The kernel never forms this vector -- it writes
# the three separately -- but the `lane_*` lemmas are indexed by it.
RESULT_LANES = val[81] + val[85] + val[89]

# --------------------------------------------------------------------- naming
# Every value carries the name `fd_r43x6_inl.h` gives it. Where LLVM split one
# C assignment into several instructions the parts get a suffix: `_lo`/`_hi`
# for the two `madd52` chains, `_hiRaw` before the `wwl_shl(...,9)` that scales
# a hi accumulator, and a digit for an intermediate step of a chain.
NAME = {6:'x00', 7:'x11', 8:'x22', 9:'x33', 10:'x44', 11:'x55', 12:'p0_q3'}
_lo = {(13,14):'p1_q4', (15,16,17):'p2_q5', (18,19,20):'p3_q6', (21,22,23):'p4_q7',
       (24,25,26):'p5_q8', (27,28):'p6_q9', (29,):'p7_qa'}
for idxs, nm in _lo.items():
    for n, ix in enumerate(idxs):
        NAME[ix] = f"{nm}_lo{n+1}" if ix != idxs[-1] else f"{nm}_lo"
_hi = {(30,):'p1_q4', (33,34):'p2_q5', (37,38,39):'p3_q6', (42,43,44):'p4_q7',
       (47,48,49):'p5_q8', (52,53,54):'p6_q9', (57,58):'p7_qa', (61,):'p8_qb'}
for idxs, nm in _hi.items():
    for n, ix in enumerate(idxs):
        NAME[ix] = f"{nm}_hiRaw{n+1}" if ix != idxs[-1] else f"{nm}_hiRaw"
for ix, nm in ((31,'p1_q4'), (35,'p2_q5'), (40,'p3_q6'), (45,'p4_q7'),
               (50,'p5_q8'), (55,'p6_q9'), (59,'p7_qa'), (62,'p8_qb')):
    NAME[ix] = f"{nm}_hi"
for ix, nm in ((32,'p1_q4'), (36,'p2_q5'), (41,'p3_q6'), (46,'p4_q7'),
               (51,'p5_q8'), (56,'p6_q9'), (60,'p7_qa')):
    NAME[ix] = nm
NAME[62] = 'p8_qb'   # the shl *is* the whole value: there is no lo chain here
NAME.update({63:'q6_p3', 64:'q7_p4', 65:'q8_p5'})
NAME.update({66:'za03_add', 67:'za03', 68:'za14_add', 69:'za14',
             70:'za25_add', 71:'za25', 72:'zb03_add', 73:'zb03',
             74:'zb14_add', 75:'zb14', 76:'zb25_add', 77:'zb25'})
NAME.update({78:'zb03_shl7', 79:'z03_part', 80:'zb03_mul24', 81:'z03',
             82:'zb14_shl7', 83:'z14_part', 84:'zb14_mul24', 85:'z14',
             86:'zb25_shl7', 87:'z25_part', 88:'zb25_mul24', 89:'z25'})

# which previously named values each instruction reads (so the tactic unfolds
# exactly those, instead of `+zetaDelta` dragging in every earlier definition)
USES = {}
for lst, base in ((list(LO), 'lo'), (list(HI), 'hi')):
    pass
def uses(i):
    src = {13:[], 14:[13], 15:[], 16:[15], 17:[16], 18:[], 19:[18], 20:[19],
           21:[], 22:[21], 23:[22], 24:[], 25:[24], 26:[25], 27:[], 28:[27],
           29:[], 30:[], 31:[30], 32:[31,14], 33:[], 34:[33], 35:[34],
           36:[35,17], 37:[], 38:[37], 39:[38], 40:[39], 41:[40,20],
           42:[], 43:[42], 44:[43], 45:[44], 46:[45,23], 47:[], 48:[47],
           49:[48], 50:[49], 51:[50,26], 52:[], 53:[52], 54:[53], 55:[54],
           56:[55,28], 57:[], 58:[57], 59:[58], 60:[59,29], 61:[], 62:[61],
           63:[41], 64:[46], 65:[51], 66:[63,12], 67:[12,66], 68:[64,32],
           69:[32,68], 70:[65,36], 71:[36,70], 72:[56,63], 73:[72,56],
           74:[60,64], 75:[74,60], 76:[62,65], 77:[76,62],
           78:[73], 79:[78,67], 80:[73], 81:[79,80],
           82:[75], 83:[82,69], 84:[75], 85:[83,84],
           86:[77], 87:[86,71], 88:[77], 89:[87,88]}
    ops = list(src.get(i, []))
    # a product reads exactly one limb broadcast -- the multiplicand of its own
    # madd52, i.e. the x-limb of the step this instruction adds
    steps = LO.get(i) or HI.get(i)
    if steps:
        ops.append(6 + steps[-1][0])
    return [NAME[k] for k in ops if k in NAME]

# ---------------------------------------------------------------- emit helpers
out = []
STOPPED = [False]
def emit(s=""):
    if not STOPPED[0]: out.append(s)

def params(lanes):
    body = " ".join(str(l) for l in lanes)
    ps = [v for v in ("X", "Y") if f"{v} " in body]
    return ps

def sig(i):
    """`name X Y` as the proof refers to it."""
    return " ".join([NAME[i]] + params(val[i]))

def stop(i):
    if UPTO is not None and i > UPTO and not STOPPED[0]:
        out.append("  sorry"); STOPPED[0] = True
    return STOPPED[0]

DOC = {
 6:"limb 0 of each element, broadcast to both halves: `wwl_pack_halves( x03,0, x03,0 )`",
 7:"limb 1 broadcast", 8:"limb 2 broadcast", 9:"limb 3 broadcast",
 10:"limb 4 broadcast", 11:"limb 5 broadcast",
 12:"column 0 in the low half, part of column 3 in the high",
 63:"`p3_q6` with its halves swapped, so each column meets its other part",
 64:"`p4_q7` with its halves swapped", 65:"`p5_q8` with its halves swapped",
 67:"columns 0 and 3, the `wwv_add_if( 0xF0, ... )` blend",
 69:"columns 1 and 4", 71:"columns 2 and 5",
 73:"columns 6 and 9, the `wwv_add_if( 0x0F, ... )` blend",
 75:"columns 7 and 10", 77:"columns 8 and 11",
 81:"`za03 + 152*zb03`, limbs 0 and 3 of all four elements",
 85:"limbs 1 and 4", 89:"limbs 2 and 5",
}


# Which arithmetic-normalising lemmas each lane actually needs, calibrated
# against `linter.unusedSimpArgs`: a lane that forms no commuted product or
# no zero operand does not need the corresponding one.
LANE_DROPS = {0: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 1: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 2: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 3: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 4: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 5: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 6: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 7: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 8: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 9: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 10: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 11: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 12: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 13: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 14: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 15: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 16: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 17: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 18: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 19: ['Nat.mul_assoc', 'Nat.mul_left_comm', 'Nat.zero_div', 'Nat.zero_mul'], 20: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 21: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 22: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 23: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul']}

def emit_lane_lemmas():
    vecs = {0: 'a', 1: 'b', 2: 'c',
            3: 'a', 4: 'b', 5: 'c'}
    yvecs = {0: 'd', 1: 'e',
             2: 'f', 3: 'd',
             4: 'e', 5: 'f'}
    def lane_of(sym, j, k):
        tbl = vecs if sym == 'X' else yvecs
        return f"{tbl[k]}[{j + (4 if k >= 3 else 0)}].toNat"
    def concrete(s):
        return re.sub(r'([XY]) (\d) (\d)',
                      lambda m: lane_of(m.group(1), int(m.group(2)), int(m.group(3))), s)
    limb_of = {}
    for n, k in enumerate([0, 3, 1, 4, 2, 5]):
        for j in range(4):
            limb_of[4 * n + j] = k
    emit("/-! ## The result lanes, against the specification")
    emit()
    emit("One lemma per lane of the result, in the vocabulary the derivation")
    emit("leaves behind: its `let`s are zeta-unfolded down to lanes, while the")
    emit("specification still reads `quadMulLimb … j`. Proving these separately")
    emit("keeps the last step of the derivation a rewrite rather than a")
    emit("twenty-four-fold re-normalisation of the whole result. -/")
    emit()
    for i, expr in enumerate(RESULT_LANES):
        j, k = i % 4, limb_of[i]
        emit(f"private theorem lane_{i} (a b c d e f : Vector (BitVec 64) 8) :")
        emit(f"    {concrete(expr)}")
        emit(f"      = limb (quadLimb a b c {j}) (quadLimb d e f {j}) {k} := by")
        keep = [n for n in ["Nat.mul_comm", "Nat.mul_left_comm",
                            "Nat.zero_div", "Nat.zero_mul"]
                if n not in LANE_DROPS[i]]
        emit(f"  simp only [limb, col, ph, pl, quadLimb, vlane, {', '.join(keep)}]")
        emit("  ring_nf")
        emit()

def emit_abbrevs():
    """No longer emits anything: every value is introduced as a `let` at the
    point the program computes it (see `step`)."""
    return

def step(i, tac):
    if stop(i): return
    emit(f"  denote_step_all v {i}")
    if i in DOC:
        emit(f"  -- {NAME[i]}: {DOC[i]}")
    lanes = val[i]
    if any(l is None for l in lanes):
        parts = [".poison" if l is None else f".value (BitVec.ofNat 64 ({l}))" for l in lanes]
        emit(f"  let {NAME[i]} : Vector (PoisonOr (BitVec 64)) {len(lanes)} := #v[{', '.join(parts)}]")
    else:
        emit(f"  let {NAME[i]} := toBitVecValue 64 #v[{', '.join(lanes)}]")
    unf = sorted(set(uses(i)) | {NAME[i]})
    if tac.startswith("quad_vecbin"):
        unf = [VAL] + unf
    emit(f"  have h{NAME[i]} : v{i} = {NAME[i]} := by {tac} hv{i} with {', '.join(unf)}")
    emit(f"  subst h{NAME[i]}")
    # `hv<i>` is now `<name> = <denotation>`, spent; retiring it keeps the
    # context to the live values rather than one hypothesis per instruction
    emit(f"  denote_clear v {i} {i}")

TAIL = r"""
/-! ## What the kernel writes

The derivation above says the region *is* three whole-vector stores. Combining
it with `Proof/Mem.lean` turns that into a statement about memory; everything
about the *values* -- ring correctness and the width table -- follows below, on
the three vectors the kernel writes. -/

/-- **The kernel's effect on memory.** Given three live, big-enough
destinations, the region runs without UB and leaves exactly the three
specified vectors behind. No aliasing hypothesis is needed: if two
destinations coincide the later write wins, which is what the nested
`writeVec`s say. -/
theorem run_fd_r43x6_quad_mul_fast (a b c d e f : Vector (BitVec 64) 8)
    (ha : R43x6.U47 a) (hb : R43x6.U47 b) (hc : R43x6.U47 c)
    (hd : R43x6.U47 d) (he : R43x6.U47 e) (hf : R43x6.U47 f)
    (p₀ p₁ p₂ : Pointer) (s : GlobalState)
    (h₀ : Fits s.mem p₀ 512)
    (h₁ : Fits (s.mem.writeVec p₀ (quadMulVec03 a b c d e f)) p₁ 512)
    (h₂ : Fits ((s.mem.writeVec p₀ (quadMulVec03 a b c d e f)).writeVec p₁
      (quadMulVec14 a b c d e f)) p₂ 512) :
    (fd_r43x6_quad_mul_fast.denote
        (quadValMem6 (.value p₀) (.value p₁) (.value p₂) a b c d e f)).run s
      = .value (HVector.nil,
          { s with mem := ((s.mem.writeVec p₀ (quadMulVec03 a b c d e f)).writeVec p₁
              (quadMulVec14 a b c d e f)).writeVec p₂ (quadMulVec25 a b c d e f) }) := by
  rw [denote_fd_r43x6_quad_mul_fast a b c d e f ha hb hc hd he hf]
  exact run_storeVec3 h₀ h₁ h₂

/-- **Correctness, against memory.** Given three live, big-enough and pairwise
distinct destinations, the region runs without UB and each pointer afterwards
addresses the vector the specification predicts for it.

The distinctness hypotheses are an assumption about the *caller*: the kernel's
pointer parameters carry `nocapture noundef writeonly` and not `noalias`, so
nothing in the IR rules out aliasing. At the one call site,
`FD_R43X6_QUAD_MUL_FAST` passes `&_R03, &_R14, &_R25` -- three distinct
locals. -/
theorem fd_r43x6_quad_mul_fast_readback (a b c d e f : Vector (BitVec 64) 8)
    (ha : R43x6.U47 a) (hb : R43x6.U47 b) (hc : R43x6.U47 c)
    (hd : R43x6.U47 d) (he : R43x6.U47 e) (hf : R43x6.U47 f)
    (p₀ p₁ p₂ : Pointer) (s : GlobalState)
    (h₀ : Fits s.mem p₀ 512) (h₁ : Fits s.mem p₁ 512) (h₂ : Fits s.mem p₂ 512)
    (d₀₁ : p₀.id ≠ p₁.id) (d₀₂ : p₀.id ≠ p₂.id) (d₁₂ : p₁.id ≠ p₂.id) :
    let m' := ((s.mem.writeVec p₀ (quadMulVec03 a b c d e f)).writeVec p₁
      (quadMulVec14 a b c d e f)).writeVec p₂ (quadMulVec25 a b c d e f)
    (fd_r43x6_quad_mul_fast.denote
          (quadValMem6 (.value p₀) (.value p₁) (.value p₂) a b c d e f)).run s
        = .value (HVector.nil, { s with mem := m' })
      ∧ (SLLVM.load (.value p₀) QVecTy).run m'
          = .value ((quadMulVec03 a b c d e f).map PoisonOr.value, m')
      ∧ (SLLVM.load (.value p₁) QVecTy).run m'
          = .value ((quadMulVec14 a b c d e f).map PoisonOr.value, m')
      ∧ (SLLVM.load (.value p₂) QVecTy).run m'
          = .value ((quadMulVec25 a b c d e f).map PoisonOr.value, m') := by
  refine ⟨run_fd_r43x6_quad_mul_fast a b c d e f ha hb hc hd he hf p₀ p₁ p₂ s h₀
      (fits_splice h₁) (fits_splice (fits_splice h₂)), ?_⟩
  exact storeVec3_readback h₀ h₁ h₂ d₀₁ d₀₂ d₁₂

/-! ## What the kernel computes

Stated per QUAD lane `j < 4`, since the kernel is four independent
multiplies. -/

/-- Reading element `j` back out of the three result vectors recovers the
specified limbs. -/
theorem quadMul_limbs (a b c d e f : Vector (BitVec 64) 8)
    (ha : R43x6.U47 a) (hb : R43x6.U47 b) (hc : R43x6.U47 c)
    (hd : R43x6.U47 d) (he : R43x6.U47 e) (hf : R43x6.U47 f)
    (j : ℕ) (hj : j < 4) (k : ℕ) (hk : k < 6) :
    quadLimb (quadMulVec03 a b c d e f) (quadMulVec14 a b c d e f)
        (quadMulVec25 a b c d e f) j k
      = quadMulLimb a b c d e f j k :=
  quadLimb_slice_quadVec24 _ j hj k hk
    (fun i hi k' hk' => by
      have := quadMulLimb_lt_two_pow_63 a b c d e f ha hb hc hd he hf i hi k' hk'
      omega)

/-- **Correctness.** In each of the four QUAD lanes, the limbs the kernel
produces decode to the product of the two decoded inputs in `GF(2^255 - 19)`. -/
theorem quadMul_zmod (a b c d e f : Vector (BitVec 64) 8) (j : ℕ) :
    ((pack (quadMulLimb a b c d e f j) : ℕ) : ZMod p)
      = ((pack (quadLimb a b c j) : ℕ) : ZMod p)
        * ((pack (quadLimb d e f j) : ℕ) : ZMod p) :=
  pack_quadMulLimb_zmod a b c d e f j

/-! ## Output bounds

The `fd_r43x6.h` width table, on each of the three vectors the kernel writes. -/

private theorem quadMul_bounds_of (a b c d e f : Vector (BitVec 64) 8) (N : ℕ)
    (hN : N ≤ 2 ^ 63)
    (hb : ∀ j < 4, ∀ k < 6, quadMulLimb a b c d e f j k < N) :
    (R43x6.BoundedUpper ((N : Int) - 1) (quadMulVec03 a b c d e f)
      ∧ R43x6.BoundedLower 0 (quadMulVec03 a b c d e f))
    ∧ (R43x6.BoundedUpper ((N : Int) - 1) (quadMulVec14 a b c d e f)
      ∧ R43x6.BoundedLower 0 (quadMulVec14 a b c d e f))
    ∧ (R43x6.BoundedUpper ((N : Int) - 1) (quadMulVec25 a b c d e f)
      ∧ R43x6.BoundedLower 0 (quadMulVec25 a b c d e f)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [quadMulVec03, quadMulVec14, quadMulVec25] <;>
    exact quadVec_bounds _ _ _ N hN
      (fun j hj => ⟨hb j hj _ (by omega), hb j hj _ (by omega)⟩)

/-- **`u47` in, `u63` out**, on every vector the kernel writes. -/
theorem quadMul_u47_u63 (a b c d e f : Vector (BitVec 64) 8)
    (ha : R43x6.U47 a) (hb : R43x6.U47 b) (hc : R43x6.U47 c)
    (hd : R43x6.U47 d) (he : R43x6.U47 e) (hf : R43x6.U47 f) :
    R43x6.U63 (quadMulVec03 a b c d e f)
      ∧ R43x6.U63 (quadMulVec14 a b c d e f)
      ∧ R43x6.U63 (quadMulVec25 a b c d e f) := by
  have := quadMul_bounds_of a b c d e f (2 ^ 63) (by omega)
    (fun j hj k hk => quadMulLimb_lt_u47 a b c d e f ha hb hc hd he hf j hj k hk)
  exact_mod_cast this

/-- **`u44` in, `u62` out**, on every vector the kernel writes. -/
theorem quadMul_u44_u62 (a b c d e f : Vector (BitVec 64) 8)
    (ha : R43x6.U44 a) (hb : R43x6.U44 b) (hc : R43x6.U44 c)
    (hd : R43x6.U44 d) (he : R43x6.U44 e) (hf : R43x6.U44 f) :
    R43x6.U62 (quadMulVec03 a b c d e f)
      ∧ R43x6.U62 (quadMulVec14 a b c d e f)
      ∧ R43x6.U62 (quadMulVec25 a b c d e f) := by
  have := quadMul_bounds_of a b c d e f (2 ^ 62) (by omega)
    (fun j hj k hk => quadMulLimb_lt_u44 a b c d e f ha hb hc hd he hf j hj k hk)
  exact_mod_cast this

end Firedancer.Avx512
"""

# ------------------------------------------------------------------- preamble
VECS = "abcdef"
BOUNDS = [f"b{v}" for v in VECS]

emit('''/-
Released under Apache 2.0 license as described in the file LICENSE.
NOTE: generated by `gen_quad_mul_proof.py`; edit that and regenerate.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.fd_r43x6_quad_mul_fast
import SSA.Projects.Firedancer.Avx512.Proof.Mem
import SSA.Projects.Firedancer.Avx512.Spec.fd_r43x6_quad_mul_fast

/-!
# `fd_r43x6_quad_mul_fast` multiplies four field elements at once

This is the kernel lifted **verbatim** -- three `!llvm.ptr` out-parameters and
three `llvm.store`s, with no extraction probe. The derivation shows the region
denotes to exactly three whole-vector stores of the specified results;
`Proof/Mem.lean` turns that into a statement about memory.

The derivation runs at the N level throughout: each of the 93 instructions is
reduced to a vector of `BitVec.ofNat 64` applied to an expression over `pl`
and `ph` (`Spec/Common.lean`), so it lands directly on `quadMulVec`. Every
intermediate is introduced as a `let` at the point the program computes it,
under the name `fd_r43x6_inl.h` gives it, so the derivation reads against the C
line by line. Where LLVM split one C assignment across several instructions the
parts carry a suffix: `_lo`/`_hi` for the two `madd52` chains, `_hiRaw` for a
hi accumulator before the `wwl_shl( ..., 9 )` that scales it, and a digit for a
step of a chain.

Each step names in its `with` list exactly the values it reads; `simp only`
zeta-delta-unfolds those and leaves the rest folded, which is what keeps a
step's simp set small.

## Hypotheses

`R43x6.U47` on all six input vectors. There are no zero-lane hypotheses: a
QUAD has no ignored lanes, so every product the kernel forms stays inside one
lane and the four multiplications never mix (see `Spec/Quad.lean`).
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
''')

emit_abbrevs()
emit_lane_lemmas()

emit('''/-! ## The derivation

The bound facts `quad_vpmadd52` needs: a `vpmadd52h` lane reads
`(u % 2^52) * (v % 2^52) / 2^52`, which is `phRaw u v` only when both operands
are already below `2^52`, and `u47` inputs are. One quantified lemma per input
vector rather than one per lane keeps the simp set small.

`Lean.mkIdent` escapes macro hygiene so these refer to the `have`s of the
theorem below, which the generated body names by convention. -/
''')
emit('local macro "quad_shuffle " h:term " with " ns:Lean.Parser.Tactic.simpLemma,* : tactic =>')
emit(f'  `(tactic| denote_shuffle $h with {VAL}, quadLimb, vlane, $ns,*)')
emit()
emit('local macro "quad_madd52 " h:term " with " ns:Lean.Parser.Tactic.simpLemma,* : tactic =>')
emit(f'  `(tactic| quad_vpmadd52 $h with {VAL},')
emit("      " + ", ".join(f"$(Lean.mkIdent `{b}):term" for b in BOUNDS) + ", $ns,*)")
emit()
emit()

emit('set_option maxHeartbeats 40000000 in')
emit('set_option maxRecDepth 100000 in')
emit('/-- **Limb derivation**: on unreduced inputs the region denotes to exactly')
emit('three whole-vector stores, of the three vectors the specification predicts,')
emit('through the three pointer parameters in declaration order. All 90')
emit('instructions are carried through at the N level. -/')
emit('theorem denote_fd_r43x6_quad_mul_fast (a b c d e f : Vector (BitVec 64) 8)')
emit('    (ha : R43x6.U47 a) (hb : R43x6.U47 b) (hc : R43x6.U47 c)')
emit('    (hd : R43x6.U47 d) (he : R43x6.U47 e) (hf : R43x6.U47 f)')
emit('    (p₀ p₁ p₂ : SLLVM.Ptr) :')
emit('    fd_r43x6_quad_mul_fast.denote (quadValMem6 p₀ p₁ p₂ a b c d e f) =')
emit('      (do storeVec p₀ ((quadMulVec03 a b c d e f).map PoisonOr.value)')
emit('          storeVec p₁ ((quadMulVec14 a b c d e f).map PoisonOr.value)')
emit('          storeVec p₂ ((quadMulVec25 a b c d e f).map PoisonOr.value)')
emit('          pure (HVector.nil :')
emit('            HVector TyDenote.toType ([] : List SLLVM.Ty))) := by')
for v, hyp in zip(VECS, ("ha", "hb", "hc", "hd", "he", "hf")):
    emit(f"  have b{v} : ∀ (i : ℕ) (h : i < 8),")
    emit(f"      ({v}[i]'h).toNat % 4503599627370496 = ({v}[i]'h).toNat := fun i h =>")
    emit(f"    Nat.mod_eq_of_lt (by have := unn_toNat {v} 47 (by omega) {hyp} i h; omega)")
emit('  unfold fd_r43x6_quad_mul_fast')
emit('  let X : ℕ → ℕ → ℕ := quadLimb a b c')
emit('  let Y : ℕ → ℕ → ℕ := quadLimb d e f')
emit()
emit('  -- the constants: `_zz`, the `wwl_shl` amounts and the `152 = 128 + 24` fold')
emit('  denote_step_all v 5')
emit('  let zeroVec := toBitVecValue 64 (Vector.replicate 8 0)')
emit('  let nineVec := toBitVecValue 64 (Vector.replicate 8 9)')
emit('  let sevenVec := toBitVecValue 64 (Vector.replicate 8 7)')
emit('  let tf4Vec := toBitVecValue 64 (Vector.replicate 8 24)')
emit('  have hzz : v2 = zeroVec := by denote_dense hv2')
emit('  have h9 : v3 = nineVec := by denote_dense hv3')
emit('  have h7 : v4 = sevenVec := by denote_dense hv4')
emit('  have h24 : v5 = tf4Vec := by denote_dense hv5')
emit('  subst hzz h9 h7 h24')
emit('  denote_clear v 1 1')
emit()
emit('  -- x00 .. x55: `wwl_pack_halves( x03,0, x03,0 )` and friends')
for i in range(6, 12):
    step(i, "quad_shuffle")
emit()
emit('  -- p0_q3 .. p8_qb: the 36 madd52 products, column I low, column I+3 high')
for i in sorted(set(list(LO) + list(HI) + list(SHL9) + list(FOLD))):
    step(i, "quad_madd52" if (i in LO or i in HI)
            else "quad_vecbin_ring" if i in SHL9 else "quad_vecbin")
emit()
emit('  -- q6_p3 .. q8_p5, then za/zb and the `za + 152*zb` fold')
for i in list(range(63, 90)):
    step(i, "quad_shuffle" if i in (63, 64, 65, 67, 69, 71, 73, 75, 77) else "quad_vecbin")
emit()
if not stop(90):
    emit('  -- the three stores. `denote_step_all` stops at %89: a store has an')
    emit('  -- impure operation, so there is nothing left to push into the')
    emit('  -- valuation. What remains is to identify the three stored values with')
    emit('  -- the specification, which is the `lane_*` lemmas above, and then to')
    emit('  -- read the stores off the denotation.')
    for name, spec, lo in (('z03', 'quadMulVec03', 0),
                           ('z14', 'quadMulVec14', 8),
                           ('z25', 'quadMulVec25', 16)):
        emit(f'  have e{name} : {name} = ({spec} a b c d e f).map PoisonOr.value := by')
        emit('    apply Vector.ext')
        emit('    intro i hi')
        emit('    interval_cases i')
        emit(f'    all_goals simp only [{spec}, quadVec, quadMulLimb, toBitVecValue,')
        emit(f'      {name}, X, Y, quadLimb, vlane,')
        emit('      Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,')
        emit('      List.getElem_cons_zero, List.getElem_cons_succ,')
        emit('      ' + ', '.join(f'lane_{lo + k}' for k in range(8)) + ']')
    emit('  simp only [Com.denote_var, Expr.denote_unfold, Expr.denoteOp,')
    emit('    EffectKind.liftEffect_rfl, simp_denote, storeVec, quadValMem6,')
    emit('    Function.comp_def, Ctxt.Valuation.nil_append, map_eq_pure_bind,')
    emit('    bind_assoc, pure_bind, Ctxt.Valuation.cons_last, ez03, ez14, ez25]')
emit(TAIL)

print("\n".join(out))
