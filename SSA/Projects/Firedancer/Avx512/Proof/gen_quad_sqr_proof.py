#!/usr/bin/env python3
"""Generate SSA/Projects/Firedancer/Avx512/Proof/fd_r43x6_quad_sqr_fast.lean.

Mirrors the data flow of the lifted region (instruction indices %0-%117) at the
N level, over the `pl`/`ph` limb functions of Spec/Common.lean and the QUAD
layout of Spec/Quad.lean.

Usage: gen_quad_sqr_proof.py [--upto N]   (truncate after %N, close with sorry)
"""
import re, sys

UPTO = int(sys.argv[2]) if len(sys.argv) >= 3 and sys.argv[1] == '--upto' else None

def el(i): return i % 4

# ---------------------------------------------------------------- lane algebra
# Each operand vector, as the (element, limb) its lanes hold; None is a zero
# lane.  The mirror-symmetric schedule packs column k and column 11-k into the
# two halves of one vector, so unlike the multiply the limb a lane carries
# differs between the halves in more than a constant offset.
VEC = {
  'A'  : [(el(i), 0 if i < 4 else 3) for i in range(8)],   # arg0 = x03
  'B'  : [(el(i), 1 if i < 4 else 4) for i in range(8)],   # arg1 = x14
  'C'  : [(el(i), 2 if i < 4 else 5) for i in range(8)],   # arg2 = x25
  'x05': [(el(i), 0 if i < 4 else 5) for i in range(8)],
  'x12': [(el(i), 1 if i < 4 else 2) for i in range(8)],
  'x34': [(el(i), 3 if i < 4 else 4) for i in range(8)],
  'x41': [(el(i), 4 if i < 4 else 1) for i in range(8)],
  'x23': [(el(i), 2 if i < 4 else 3) for i in range(8)],
  'x52': [(el(i), 5 if i < 4 else 2) for i in range(8)],
  'x4z': [(el(i), 4) if i < 4 else None for i in range(8)],
}

def opn(name, i, dbl=False):
    t = VEC[name][i]
    if t is None: return "0"
    s = f"X {t[0]} {t[1]}"
    return f"(2 * {s})" if dbl else f"({s})"

def prod(f, u, v, i):
    """One `pl`/`ph`/`phRaw` term; u and v are (name, doubled) pairs."""
    return f"{f} {opn(u[0], i, u[1])} {opn(v[0], i, v[1])}"

def chain(f, steps):
    return [" + ".join(prod(f, u, v, i) for (u, v) in steps) for i in range(8)]

A = ('A', False); B = ('B', False); C = ('C', False)
A2 = ('A', True); B2 = ('B', True)
x05 = ('x05', False); x05_2 = ('x05', True)
x12 = ('x12', False); x12_2 = ('x12', True)
x34 = ('x34', False); x41 = ('x41', False)
x23 = ('x23', False); x52 = ('x52', False); x4z = ('x4z', False)

# madd52lo chains, and the madd52hi chains that mirror them
STEPS = {
  53: [(x05, x05)],
  54: [(x05_2, B)],
  55: [(B, B)],                    56: [(B, B), (A2, C)],
  57: [(A2, x34)],                 58: [(A2, x34), (x12_2, C)],
  59: [(x23, x23)],                60: [(x23, x23), (x05_2, x41)],
  61: [(x23, x23), (x05_2, x41), (x12_2, x34)],
  62: [(A2, x52)],                 63: [(A2, x52), (B2, x4z)],
}
HSTEPS = {
  64: STEPS[53], 66: STEPS[54],
  68: STEPS[55], 69: STEPS[56],
  71: STEPS[57], 72: STEPS[58],
  74: STEPS[59], 75: STEPS[60], 76: STEPS[61],
  78: STEPS[62], 79: STEPS[63],
}
SHL9 = {65: 64, 67: 66, 70: 69, 73: 72, 77: 76, 80: 79}

val = {}
for i in (42, 43, 44, 45, 46, 47, 48):
    nm = {42:'x05', 43:'x12', 44:'x34', 45:'x41', 46:'x23', 47:'x52', 48:'x4z'}[i]
    val[i] = [opn(nm, j) for j in range(8)]
for i, nm in ((49, 'A'), (50, 'B'), (51, 'x05'), (52, 'x12')):
    val[i] = [f"2 * {opn(nm, j)}" for j in range(8)]
for i, st in STEPS.items():
    val[i] = chain("pl", st)
for i, st in HSTEPS.items():
    val[i] = chain("phRaw", st)
for i, src in SHL9.items():
    val[i] = chain("ph", HSTEPS[src])

ZLO = ["0"] * 8          # %19 lanes 0-3 (lanes 4-7 poison, never selected)
ZHI = ["0"] * 8          # %39 lanes 4-7 (lanes 0-3 poison, never selected)

def sh(u, w, mask):
    both = u + w
    return [both[m] for m in mask]

L, H = [0,1,2,3,8,9,10,11], [4,5,6,7,12,13,14,15]

val[81] = sh(val[53], val[58], L)
val[82] = sh(ZLO,      val[70], L)
val[83] = [f"({val[82][j]}) + ({val[81][j]})" for j in range(8)]      # za03
val[84] = sh(val[54], val[61], L)
val[85] = sh(val[65], val[73], L)
val[86] = [f"({val[85][j]}) + ({val[84][j]})" for j in range(8)]      # za14
val[87] = sh(val[56], val[63], L)
val[88] = sh(val[67], val[77], L)
val[89] = sh(ZLO,      val[63], [0,1,2,3,12,13,14,15])
val[90] = sh(val[61], val[54], H)
val[91] = sh(val[80], val[70], H)
val[92] = [f"({val[91][j]}) + ({val[90][j]})" for j in range(8)]
val[93] = sh(val[80], ZHI,     [0,1,2,3,12,13,14,15])
val[94] = [f"({val[92][j]}) + ({val[93][j]})" for j in range(8)]      # zb03
val[95] = sh(val[58], val[53], H)
val[96] = sh(val[77], val[67], H)
val[97] = [f"({val[96][j]}) + ({val[95][j]})" for j in range(8)]      # zb14
val[98] = sh(val[56], ZHI,     H)
val[99] = sh(val[73], val[65], H)
val[100] = [f"({val[99][j]}) + ({val[98][j]})" for j in range(8)]     # zb25

val[101] = [f"({val[94][j]}) * 128" for j in range(8)]
val[102] = [f"({val[83][j]}) + ({val[101][j]})" for j in range(8)]
val[103] = [f"({val[94][j]}) * 24" for j in range(8)]
val[104] = [f"({val[102][j]}) + ({val[103][j]})" for j in range(8)]   # z03
val[105] = [f"({val[97][j]}) * 128" for j in range(8)]
val[106] = [f"({val[86][j]}) + ({val[105][j]})" for j in range(8)]
val[107] = [f"({val[97][j]}) * 24" for j in range(8)]
val[108] = [f"({val[106][j]}) + ({val[107][j]})" for j in range(8)]   # z14
val[109] = [f"({val[100][j]}) * 128" for j in range(8)]
val[110] = [f"({val[100][j]}) * 24" for j in range(8)]
val[111] = [f"({val[89][j]}) + ({val[87][j]})" for j in range(8)]
val[112] = [f"({val[111][j]}) + ({val[109][j]})" for j in range(8)]
val[113] = [f"({val[112][j]}) + ({val[110][j]})" for j in range(8)]
val[114] = [f"({val[113][j]}) + ({val[88][j]})" for j in range(8)]    # z25
val[115] = val[104] + val[108]
val[116] = val[114] + [None] * 8
val[117] = val[115] + val[114]

# --------------------------------------------------------------------- naming
# Every value under the name `fd_r43x6_inl.h` gives it. Suffixes mark the
# pieces LLVM split one C assignment into: `_lo`/`_raw` for a step of a
# `madd52lo`/`madd52hi` chain, `_add`/`_shl7`/`_mul24` for the fold.
NAME = {42:'x05', 43:'x12', 44:'x34', 45:'x41', 46:'x23', 47:'x52', 48:'x4z',
        49:'two_x03', 50:'two_x14', 51:'two_x05', 52:'two_x12',
        53:'p0a', 54:'p19', 55:'p28_lo1', 56:'p28', 57:'p37_lo1', 58:'p37',
        59:'p46_lo1', 60:'p46_lo2', 61:'p46', 62:'p55_lo1', 63:'p55',
        64:'q1b_raw', 65:'q1b', 66:'q2a_raw', 67:'q2a',
        68:'q39_raw1', 69:'q39_raw', 70:'q39',
        71:'q48_raw1', 72:'q48_raw', 73:'q48',
        74:'q57_raw1', 75:'q57_raw2', 76:'q57_raw', 77:'q57',
        78:'q66_raw1', 79:'q66_raw', 80:'q66',
        81:'za03_p', 82:'za03_q', 83:'za03',
        84:'za14_p', 85:'za14_q', 86:'za14',
        87:'za25_p', 88:'za25_q', 89:'za25_hi',
        90:'zb03_p', 91:'zb03_q', 92:'zb03_pq', 93:'zb03_lo', 94:'zb03',
        95:'zb14_p', 96:'zb14_q', 97:'zb14',
        98:'zb25_p', 99:'zb25_q', 100:'zb25',
        101:'zb03_shl7', 102:'z03_part', 103:'zb03_mul24', 104:'z03',
        105:'zb14_shl7', 106:'z14_part', 107:'zb14_mul24', 108:'z14',
        109:'zb25_shl7', 110:'zb25_mul24', 111:'za25_a', 112:'za25_b',
        113:'za25_c', 114:'z25',
        115:'z03_z14', 116:'z25_wide', 117:'z'}

# what each instruction reads, so the tactic unfolds exactly those
SRC = {49:[], 50:[], 51:[42], 52:[43],
       53:[42], 54:[51], 55:[], 56:[55,49], 57:[49,44], 58:[57,52],
       59:[46], 60:[59,51,45], 61:[60,52,44], 62:[49,47], 63:[62,50,48],
       64:[42], 65:[64], 66:[51], 67:[66], 68:[], 69:[68,49], 70:[69],
       71:[49,44], 72:[71,52], 73:[72], 74:[46], 75:[74,51,45], 76:[75,52,44],
       77:[76], 78:[49,47], 79:[78,50,48], 80:[79],
       81:[53,58], 82:[70], 83:[82,81], 84:[54,61], 85:[65,73], 86:[85,84],
       87:[56,63], 88:[67,77], 89:[63], 90:[61,54], 91:[80,70], 92:[91,90],
       93:[80], 94:[92,93], 95:[58,53], 96:[77,67], 97:[96,95],
       98:[56], 99:[73,65], 100:[99,98],
       101:[94], 102:[83,101], 103:[94], 104:[102,103],
       105:[97], 106:[86,105], 107:[97], 108:[106,107],
       109:[100], 110:[100], 111:[89,87], 112:[111,109], 113:[112,110],
       114:[113,88], 115:[104,108], 116:[114], 117:[115,116]}

def uses(i):
    names = [NAME[k] for k in SRC.get(i, []) if k in NAME]
    # `two_x03` and `two_x14` shift a block argument, so their operand is a bare
    # lane; every other shift is of an already-computed `BitVec.ofNat` vector
    if i in (49, 50):
        names.append("shl_lane")
    return names

# ---------------------------------------------------------------- emit helpers
out = []
STOPPED = [False]
def emit(s=""):
    if not STOPPED[0]: out.append(s)

def params(lanes):
    body = " ".join(str(l) for l in lanes)
    return ["X"] if "X " in body else []

def sig(i):
    return " ".join([NAME[i]] + params(val[i]))

def stop(i):
    if UPTO is not None and i > UPTO and not STOPPED[0]:
        out.append("  sorry"); STOPPED[0] = True
    return STOPPED[0]

DOC = {
 42:"`wwl_pack_h0_h1( x03, x25 )`: limb 0 in the low half, limb 5 in the high",
 43:"limbs 1 and 2", 44:"limbs 3 and 4", 45:"limbs 4 and 1",
 46:"limbs 2 and 3", 47:"limbs 5 and 2",
 48:"limb 4 and a zero -- the kernel's own constant, so that the mirrored schedule has a partner for `2*p41l`",
 53:"columns 0 and 10", 54:"columns 1 and 9", 56:"columns 2 and 8",
 58:"columns 3 and 7", 61:"columns 4 and 6",
 63:"column 5, split across *both* halves; they are re-joined below",
 65:"columns 1 and 11", 67:"columns 2 and 10", 70:"columns 3 and 9",
 73:"columns 4 and 8", 77:"columns 5 and 7",
 80:"column 6, likewise split across both halves",
 83:"columns 0 and 3", 86:"columns 1 and 4",
 94:"columns 6 and 9", 97:"columns 7 and 10", 100:"columns 8 and 11",
 104:"`za03 + 152*zb03`, limbs 0 and 3 of all four elements",
 108:"limbs 1 and 4", 114:"limbs 2 and 5",
 117:"the three results concatenated, as the extraction probe returns them",
}

# Which arithmetic-normalising lemmas each lane actually needs, calibrated
# against `linter.unusedSimpArgs`: a lane that forms no commuted product or
# no zero operand does not need the corresponding one.
LANE_DROPS = {0: ['Nat.mul_assoc'], 1: ['Nat.mul_assoc'], 2: ['Nat.mul_assoc'], 3: ['Nat.mul_assoc'], 4: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 5: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 6: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 7: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 8: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 9: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 10: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 11: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 12: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 13: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 14: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 15: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 16: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 17: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 18: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 19: ['Nat.mul_assoc', 'Nat.zero_div', 'Nat.zero_mul'], 20: ['Nat.mul_assoc', 'Nat.zero_div'], 21: ['Nat.mul_assoc', 'Nat.zero_div'], 22: ['Nat.mul_assoc', 'Nat.zero_div'], 23: ['Nat.mul_assoc', 'Nat.zero_div']}

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
    emit("specification still reads `quadSqrLimb … j`. Proving these separately")
    emit("keeps the last step of the derivation a rewrite rather than a")
    emit("twenty-four-fold re-normalisation of the whole result. -/")
    emit()
    for i, expr in enumerate(val[117]):
        j, k = i % 4, limb_of[i]
        emit(f"private theorem lane_{i} (a b c : Vector (BitVec 64) 8) :")
        emit(f"    {concrete(expr)}")
        emit(f"      = sqLimb (quadLimb a b c {j}) {k} := by")
        keep = [n for n in ["Nat.mul_comm", "Nat.mul_left_comm",
                            "Nat.zero_div", "Nat.zero_mul"]
                if n not in LANE_DROPS[i]]
        emit(f"  simp only [sqLimb, sqCol, ph, pl, quadLimb, vlane, {', '.join(keep)}]")
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
        unf = ["quadVal3"] + unf
    emit(f"  have h{NAME[i]} : v{i} = {NAME[i]} := by {tac} hv{i} with {', '.join(unf)}")
    emit(f"  subst h{NAME[i]}")
    # `hv<i>` is now `<name> = <denotation>`, spent; retiring it keeps the
    # context to the live values rather than one hypothesis per instruction
    emit(f"  denote_clear v {i} {i}")

TAIL = r"""
/-! ## What the kernel computes

The derivation above lands on `quadSqrVec`; combining it with the ring
correctness and width table of `Spec/fd_r43x6_quad_sqr_fast.lean` gives the
kernel's contract. Everything below is stated per QUAD lane `j < 4`, since the
kernel is four independent multiplies. -/

/-- The program's 24-lane result. -/
abbrev quadSqrResult (a b c : Vector (BitVec 64) 8) :
    Vector (PoisonOr (BitVec 64)) 24 :=
  (fd_r43x6_quad_sqr_fast.denote (quadVal3 a b c)).head

/-- The result, with the poison layer discharged. -/
theorem quadSqrResult_eq (a b c : Vector (BitVec 64) 8)
    (ha : R43x6.U47 a) (hb : R43x6.U47 b) (hc : R43x6.U47 c) :
    quadSqrResult a b c = (quadSqrVec a b c).map PoisonOr.value := by
  rw [quadSqrResult, denote_fd_r43x6_quad_sqr_fast a b c ha hb hc]
  simp only [HVector.head]

/-- Reading element `j` back out of the result recovers the specified limbs. -/
theorem quadSqr_limbs (a b c : Vector (BitVec 64) 8)
    (ha : R43x6.U47 a) (hb : R43x6.U47 b) (hc : R43x6.U47 c)
    (j : ℕ) (hj : j < 4) (k : ℕ) (hk : k < 6) :
    quadLimb (slice03 (quadSqrVec a b c)) (slice14 (quadSqrVec a b c))
        (slice25 (quadSqrVec a b c)) j k
      = quadSqrLimb a b c j k :=
  quadLimb_slice_quadVec24 _ j hj k hk
    (fun i hi k' hk' => by
      have := quadSqrLimb_lt_two_pow_63 a b c ha hb hc i hi k' hk'
      omega)

/-- **Correctness.** In each of the four QUAD lanes, the limbs the kernel
produces decode to the square of the decoded input in `GF(2^255 - 19)`. -/
theorem quadSqr_zmod (a b c : Vector (BitVec 64) 8) (j : ℕ) :
    ((pack (quadSqrLimb a b c j) : ℕ) : ZMod p)
      = ((pack (quadLimb a b c j) : ℕ) : ZMod p) ^ 2 :=
  pack_quadSqrLimb_zmod a b c j

/-! ## Output bounds

The `fd_r43x6.h` width table, transported through the denotation onto each
third of the 24-lane result. -/

private theorem quadSqr_bounds_of (a b c : Vector (BitVec 64) 8) (N : ℕ)
    (hN : N ≤ 2 ^ 63)
    (hb : ∀ j < 4, ∀ k < 6, quadSqrLimb a b c j k < N) :
    (R43x6.BoundedUpper ((N : Int) - 1) (slice03 (quadSqrVec a b c))
      ∧ R43x6.BoundedLower 0 (slice03 (quadSqrVec a b c)))
    ∧ (R43x6.BoundedUpper ((N : Int) - 1) (slice14 (quadSqrVec a b c))
      ∧ R43x6.BoundedLower 0 (slice14 (quadSqrVec a b c)))
    ∧ (R43x6.BoundedUpper ((N : Int) - 1) (slice25 (quadSqrVec a b c))
      ∧ R43x6.BoundedLower 0 (slice25 (quadSqrVec a b c))) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [quadSqrVec, quadVec24, slice03_quadCat, slice14_quadCat, slice25_quadCat] <;>
    exact quadVec_bounds _ _ _ N hN
      (fun j hj => ⟨hb j hj _ (by omega), hb j hj _ (by omega)⟩)

/-- **`u47` in, `u62` out**, on every third of the result. -/
theorem quadSqr_u47_u62 (a b c : Vector (BitVec 64) 8)
    (ha : R43x6.U47 a) (hb : R43x6.U47 b) (hc : R43x6.U47 c) :
    R43x6.U62 (slice03 (quadSqrVec a b c))
      ∧ R43x6.U62 (slice14 (quadSqrVec a b c))
      ∧ R43x6.U62 (slice25 (quadSqrVec a b c)) := by
  have := quadSqr_bounds_of a b c (2 ^ 62) (by omega)
    (fun j hj k hk => quadSqrLimb_lt_u47 a b c ha hb hc j hj k hk)
  exact_mod_cast this

/-- **`u44` in, `u61` out**, on every third of the result. -/
theorem quadSqr_u44_u61 (a b c : Vector (BitVec 64) 8)
    (ha : R43x6.U44 a) (hb : R43x6.U44 b) (hc : R43x6.U44 c) :
    R43x6.U61 (slice03 (quadSqrVec a b c))
      ∧ R43x6.U61 (slice14 (quadSqrVec a b c))
      ∧ R43x6.U61 (slice25 (quadSqrVec a b c)) := by
  have := quadSqr_bounds_of a b c (2 ^ 61) (by omega)
    (fun j hj k hk => quadSqrLimb_lt_u44 a b c ha hb hc j hj k hk)
  exact_mod_cast this

end Firedancer.Avx512
"""

# ------------------------------------------------------------------- preamble
VECS = "abc"
BOUNDS = [f"b{v}" for v in VECS] + [f"b{v}2" for v in VECS]

emit('''/-
Released under Apache 2.0 license as described in the file LICENSE.
NOTE: generated by `gen_quad_sqr_proof.py`; edit that and regenerate.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.fd_r43x6_quad_sqr_fast
import SSA.Projects.Firedancer.Avx512.Proof.Quad
import SSA.Projects.Firedancer.Avx512.Spec.fd_r43x6_quad_sqr_fast

/-!
# `fd_r43x6_quad_sqr_fast` squares four field elements at once

Denoting the lifted region and reading its 24-lane result back through the
QUAD layout gives, in each of the four lanes, the square of the decoded input
in `GF(2^255 - 19)`, within the widths `fd_r43x6.h` promises.

Every intermediate is introduced as a `let` at the point the program computes
it, under the name `fd_r43x6_inl.h` gives it, so the derivation reads against
the C line by line. Each step names in its `with` list exactly the values it
reads; `simp only` zeta-delta-unfolds those and leaves the rest folded.

The kernel packs column `k` and column `11 - k` into the two halves of one
vector, so an operand carries different limbs in its two halves. Two columns
straddle both halves and are re-joined by an extra add: column 5 out of `p55`
and column 6 out of `q66`.

## Hypotheses

`R43x6.U47` on the three input vectors. There are no zero-lane hypotheses: a
QUAD has no ignored lanes. The one zero the kernel multiplies against is its
own constant `x4z`, not a contract on the input.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
''')

emit_abbrevs()
emit_lane_lemmas()

emit('''/-! ## The derivation

The bound facts `quad_vpmadd52` needs, for the plain and the doubled operands
alike -- a `vpmadd52h` lane is `phRaw u v` only when both operands are already
below `2^52`, and `u47` inputs are, doubled or not. -/
''')
emit('local macro "quad_shuffle " h:term " with " ns:Lean.Parser.Tactic.simpLemma,* : tactic =>')
emit('  `(tactic| denote_shuffle $h with quadVal3, quadLimb, vlane, $ns,*)')
emit()
emit('local macro "quad_madd52 " h:term " with " ns:Lean.Parser.Tactic.simpLemma,* : tactic =>')
emit('  `(tactic| quad_vpmadd52 $h with quadVal3,')
emit("      " + ", ".join(f"$(Lean.mkIdent `{b}):term" for b in BOUNDS) + ", $ns,*)")
emit()
emit()

emit('set_option maxHeartbeats 40000000 in')
emit('set_option maxRecDepth 100000 in')
emit('/-- **Limb derivation**: on unreduced inputs the denotation *is* the')
emit('specified `quadSqrVec`, every one of the 118 instructions carried through at')
emit('the N level. -/')
emit('theorem denote_fd_r43x6_quad_sqr_fast (a b c : Vector (BitVec 64) 8)')
emit('    (ha : R43x6.U47 a) (hb : R43x6.U47 b) (hc : R43x6.U47 c) :')
emit('    fd_r43x6_quad_sqr_fast.denote (quadVal3 a b c) =')
emit('      ([(quadSqrVec a b c).map PoisonOr.value]ₕ :')
emit('        HVector TyDenote.toType [QTy24]) := by')
for v, hyp in zip(VECS, ("ha", "hb", "hc")):
    emit(f"  have b{v} : ∀ (i : ℕ) (h : i < 8),")
    emit(f"      ({v}[i]'h).toNat % 4503599627370496 = ({v}[i]'h).toNat := fun i h =>")
    emit(f"    Nat.mod_eq_of_lt (by have := unn_toNat {v} 47 (by omega) {hyp} i h; omega)")
    emit(f"  have b{v}2 : ∀ (i : ℕ) (h : i < 8),")
    emit(f"      2 * ({v}[i]'h).toNat % 4503599627370496 = 2 * ({v}[i]'h).toNat := fun i h =>")
    emit(f"    Nat.mod_eq_of_lt (by have := unn_toNat {v} 47 (by omega) {hyp} i h; omega)")
emit('  unfold fd_r43x6_quad_sqr_fast')
emit('  let X : ℕ → ℕ → ℕ := quadLimb a b c')
emit()
emit('  -- the constants, including the two `insertelement` chains that build a')
emit('  -- half-zero half-poison mask; the poison half is never selected')
emit('  denote_step_all v 41')

emit('  let zeroBVP : PoisonOr (BitVec 64) := .value 0')
emit('  have hz64 : v2 = zeroBVP := by')
emit('    simp only [hv2, Expr.denoteOp1, Expr.denoteOpPure]; simp_peephole')
emit('    simp only [HVector.head]; rfl')
emit('  have hpoison : v1 = PoisonOr.poison := by')
emit('    simp only [hv1]; simp_peephole; rfl')
emit('  subst hz64 hpoison')
emit('  let zero4_p4 : Vector (PoisonOr (BitVec 64)) 8 :=')
emit('    (Vector.replicate 4 (.value (BitVec.zero 64))).append (Vector.replicate 4 .poison)')
emit('  let p4_zero4 : Vector (PoisonOr (BitVec 64)) 8 :=')
emit('    (Vector.replicate 4 .poison).append (Vector.replicate 4 (.value (BitVec.zero 64)))')
emit('  have hzlo : v19 = zero4_p4 := by')
emit('    denote_eval v 3 19')
emit('    denote_expand v 3 19')
emit('    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]')
emit('    rfl')
emit('  have hzhi : v39 = p4_zero4 := by')
emit('    denote_eval v 23 39')
emit('    denote_expand v 23 39')
emit('    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]')
emit('    rfl')
emit('  subst hzlo hzhi')
emit('  denote_clear v 3 18')
emit('  denote_clear v 23 38')
emit('  let oneVec := toBitVecValue 64 (Vector.replicate 8 1)')
emit('  let zeroVec := toBitVecValue 64 (Vector.replicate 8 0)')
emit('  let nineVec := toBitVecValue 64 (Vector.replicate 8 9)')
emit('  let sevenVec := toBitVecValue 64 (Vector.replicate 8 7)')
emit('  let tf4Vec := toBitVecValue 64 (Vector.replicate 8 24)')
emit('  have h1 : v20 = oneVec := by denote_dense hv20')
emit('  have hzz : v21 = zeroVec := by denote_dense hv21')
emit('  have h9 : v22 = nineVec := by denote_dense hv22')
emit('  have h7 : v40 = sevenVec := by denote_dense hv40')
emit('  have h24 : v41 = tf4Vec := by denote_dense hv41')
emit('  subst h1 hzz h9 h7 h24')
emit()
emit('  -- x05 .. x4z and the doubled operands')
for i in (42, 43, 44, 45, 46, 47, 48):
    step(i, "quad_shuffle")
for i in (49, 50, 51, 52):
    step(i, "quad_vecbin_ring")
emit()
emit('  -- p0a .. p55 and q1b .. q66: the 21 products per element')
for i in sorted(set(list(STEPS) + list(HSTEPS) + list(SHL9))):
    step(i, "quad_madd52" if (i in STEPS or i in HSTEPS)
            else "quad_vecbin_ring" if i in SHL9 else "quad_vecbin")
emit()
emit('  -- za03 .. zb25 and the `za + 152*zb` fold')
SHUF = {81, 82, 84, 85, 87, 88, 89, 90, 91, 93, 95, 96, 98, 99}
for i in range(81, 115):
    step(i, "quad_shuffle" if i in SHUF else "quad_vecbin")
emit()
emit('  -- the concatenation the extraction probe adds')
if not stop(115):
    step(115, "quad_shuffle")
    step(116, "quad_shuffle")
    step(117, "quad_shuffle")
    emit()
    emit('  -- and that vector is the one the specification predicts. The')
    emit('  -- arithmetic is the `lane_*` lemmas above: the derivation ends with')
    emit('  -- its `let`s zeta-unfolded to lanes while the specification still')
    emit('  -- reads `quadSqrLimb ... j`, and re-deriving that correspondence')
    emit('  -- inside a twenty-four-way case split does not fit in any sensible')
    emit('  -- heartbeat budget. Here it is a rewrite.')
    emit('  simp_peephole')
    emit('  try congr 1')
    emit('  apply Vector.ext')
    emit('  intro i hi')
    emit('  interval_cases i')
    emit('  all_goals simp only [quadSqrVec, quadVec24_eq, quadSqrLimb, toBitVecValue,')
    # the `lane_*` lemmas are stated over `a[j].toNat`, so the derivation's
    # side has to be reduced to lanes too; the specification's side keeps
    # `quadLimb ... j` partially applied and is untouched by these
    emit('    z, X, quadLimb, vlane,')
    emit('    Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,')
    emit('    List.getElem_cons_zero, List.getElem_cons_succ,')
    emit('    lane_0, lane_1, lane_2, lane_3, lane_4, lane_5, lane_6, lane_7, lane_8, lane_9, lane_10, lane_11, lane_12, lane_13, lane_14, lane_15, lane_16, lane_17, lane_18, lane_19, lane_20, lane_21, lane_22, lane_23]')

emit(TAIL)

print("\n".join(out))
