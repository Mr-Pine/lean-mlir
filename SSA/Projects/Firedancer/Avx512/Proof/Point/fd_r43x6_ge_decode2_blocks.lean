/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_r43x6_ge_decode2
import SSA.Projects.Firedancer.Avx512.Proof.Common
import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic
import SSA.Projects.Firedancer.Avx512.Proof.Step.fd_r43x6_is_nonzero
import SSA.Projects.Firedancer.Avx512.Proof.Step.fd_r43x6_mul_fast
import SSA.Projects.Firedancer.Avx512.Proof.Step.fd_r43x6_diagnose
import SSA.Projects.Firedancer.Avx512.Proof.Step.fd_r43x6_unpack
import SSA.Projects.Firedancer.Avx512.Proof.Sub
import SSA.Projects.Firedancer.Avx512.Proof.Quad
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Proof.Overflow
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.MLIR.DenoteStep

/-!
# `fd_r43x6_ge_decode2`'s tail blocks

The region is six blocks. `^bb0` is the two decodes, and is derived in
`Proof/Point/fd_r43x6_ge_decode2.lean`; the other five are here, so that file
can consume them as lemmas rather than walk them inline.

* `^bb1` -- the second encoding's remaining square-root test: one
  `fd_r43x6_is_nonzero`, `and`ed with `%191` (the first test, made in `^bb0`),
  branching to `^bb2` on success and `^bb4` on failure.
* `^bb3` -- `_vsa` is not a point: zero five of the six out-vectors and return
  `-1` through `^bb5`.
* `^bb4` -- `_vsb` is not a point: the same five stores, returning `-2`.
* `^bb5` -- the shared exit: store `%309` through `%arg6`, end the two
  staging buffers' lifetimes, return `%310`.
* `^bb2` -- the success path, and the only large one: the sign fixup, the
  QUAD transpose and the six stores. Set up but not yet derived.

`^bb3` and `^bb4` are the same five stores; they differ only in the constant
they carry to `^bb5`, so they are two lemmas over one script.

## The ambient environment

Depth-1 dominance means every tail block starts from `^bb0`'s out-context, so
each of these lemmas reads the entry block's definitions out of an opaque
`fd_r43x6_ge_decode2.Γout.Valuation`. `EntryEnv` spells the indices once, for
all five blocks together -- `%k` is `Γout` variable `194 - k`, `%argN` is
`202 - N` -- and nothing below has to reduce the region to look a value up.

What a block reads that `^bb0` *computes* rather than declares is not in
there: those are data, so they are hypotheses of the block's lemma
(`bb1_run`'s `%90`/`%184`/`%191`) or, where there are eight of them, a
structure of their own (`Bb2In`).
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/- Scaffolding for the `fd_r43x6_ge_decode2` derivation. -/
namespace GeDecode2

/-! ### The four tail blocks as branch targets

`^bb1` is block 0, `^bb2` block 1, and so on: the entry block is not in the
list. Only `^bb5` takes arguments -- the vector to store through `%arg6` and
the `int` to return. -/

/-- `^bb1`, the second encoding's remaining square-root test. -/
abbrev bb1 : SuccArgs fd_r43x6_ge_decode2.sigs :=
  ⟨0, by rfl, (.nil : HVector TyDenote.toType [])⟩

/-- `^bb2`, the success path. -/
abbrev bb2 : SuccArgs fd_r43x6_ge_decode2.sigs :=
  ⟨1, by rfl, (.nil : HVector TyDenote.toType [])⟩

/-- `^bb3`, `_vsa` is not a point. -/
abbrev bb3 : SuccArgs fd_r43x6_ge_decode2.sigs :=
  ⟨2, by rfl, (.nil : HVector TyDenote.toType [])⟩

/-- `^bb4`, `_vsb` is not a point. -/
abbrev bb4 : SuccArgs fd_r43x6_ge_decode2.sigs :=
  ⟨3, by rfl, (.nil : HVector TyDenote.toType [])⟩

/-- `^bb5( %309, %310 )`, the shared exit: the last out-vector and the
returned `int`. -/
abbrev bb5 (v : Vector (BitVec 64) 8) (r : LLVM.IntW 32) :
    SuccArgs fd_r43x6_ge_decode2.sigs :=
  ⟨4, by rfl, ([v.map PoisonOr.value, r]ₕ :
    HVector TyDenote.toType [V8, SLLVM.Ty.bitvec 32])⟩

/-! ### The two multipliers

`fd_r43x6_ge_decode2` names them, so this file does too. `zeroVec` -- the
vector the failure paths store -- is the spec's. -/

/-- `%19 = fd_r43x6_one()`. -/
abbrev oneVec : Vector (BitVec 64) 8 := #v[1, 0, 0, 0, 0, 0, 0, 0]

/-- `%13 = fd_r43x6_imag()`, the `sqrt(-1)` a failed direct root is multiplied
by. -/
abbrev sqrtM1Vec : Vector (BitVec 64) 8 :=
  #v[3467281080496, 6582290652611, 5210002954932, 329084955603, 4526638806224,
     373767602335, 0, 0]

/-- The `u47` a kernel wants, from the `extractLimbs` bound `Proof/Sub.lean`'s
macros and `MulInl.u44` both hand back. `u47_take_of_unpacked`'s shape at a
`u44`-style bound. -/
theorem u47_take_of_bounds {v : Vector (BitVec 64) 8}
    (h : ∀ k, 0 ≤ R43x6.extractLimbs v k ∧ R43x6.extractLimbs v k < 2 ^ 44) :
    R43x6.U47 (v.take R43x6.limbCount) :=
  ⟨fun i => by rw [R43x6.toInts_take]; have := (h i).2; omega,
   fun i => by rw [R43x6.toInts_take]; exact (h i).1⟩

/-- **The `select` every `fd_r43x6_if` in this region compiles to.** The
condition is a `bitcast` of an `i8` that a `trunc`/`add -1` or a `sext` has
made all-ones or all-zero, so the eight `i1` lanes agree and the select is a
plain `if`. -/
theorem vselect_mask8 (c : Prop) [Decidable c] (x y : Vector (BitVec 64) 8) :
    vselect (bitcast (.bitvec (.concrete 8)) (.vector 8 (.bitvec (.concrete 1)))
        (PoisonOr.value (if c then 255#8 else 0#8)))
        (x.map PoisonOr.value) (y.map PoisonOr.value)
      = (if c then x else y).map PoisonOr.value := by
  by_cases h : c <;> simp only [h, if_true, if_false] <;>
    (apply Vector.ext; intro i hi; interval_cases i <;> rfl)

/-- Either multiplier meets `fd_r43x6_mul_fast`'s input contract, so the
`select`'s result does whichever way it went. Stated over the `if` rather than
over the two vectors, since that is the shape `ht3a`/`ht3b` hand back. -/
theorem selMul_contract (c : Prop) [Decidable c] :
    R43x6.U47 ((if c then oneVec else sqrtM1Vec).take R43x6.limbCount)
      ∧ (if c then oneVec else sqrtM1Vec)[6] = 0
      ∧ (if c then oneVec else sqrtM1Vec)[7] = 0 := by
  split <;>
    exact ⟨⟨fun i => by fin_cases i <;> decide, fun i => by fin_cases i <;> decide⟩, rfl, rfl⟩

/-- The `denote_dense` form of `oneVec`, for the entry-block walk that has to
prove `EntryEnv.c19`. -/
theorem oneVec_eq : oneVec.map PoisonOr.value = toBitVecValue 64 #v[1, 0, 0, 0, 0, 0, 0, 0] := by
  apply Vector.ext; intro i hi
  simp only [toBitVecValue, Vector.getElem_map]
  interval_cases i <;> rfl

/-- ... and of `sqrtM1Vec`, for `EntryEnv.c13`. -/
theorem sqrtM1Vec_eq : sqrtM1Vec.map PoisonOr.value
    = toBitVecValue 64 #v[3467281080496, 6582290652611, 5210002954932, 329084955603,
        4526638806224, 373767602335, 0, 0] := by
  apply Vector.ext; intro i hi
  simp only [toBitVecValue, Vector.getElem_map]
  interval_cases i <;> rfl

/-- ... and of `zeroVec`, which `%224`'s `vpermi2var` needs in the
`toBitVecValue` form `denote_negVec` is stated over. -/
theorem zeroVec_eq : zeroVec.map PoisonOr.value
    = toBitVecValue 64 #v[0, 0, 0, 0, 0, 0, 0, 0] := by
  apply Vector.ext; intro i hi
  simp only [toBitVecValue, Vector.getElem_map]
  interval_cases i <;> rfl

/-! ### The ambient environment -/

/-- What the tail blocks read out of `^bb0`'s out-context: every constant the
entry block declares that any of them uses, and the six out-parameters they
write. The `Γout` indices are spelled here once.

One structure rather than one per block. The four blocks have exactly one
caller between them -- `fd_r43x6_ge_decode2_conforms` -- and it is on `^bb2`'s
path, so it establishes the whole set whatever the split; carving off "what
`^bb1` happens to read" would buy a smaller precondition nobody is in a
position to use, and would make `bb2_run` coerce to reach `bb5_run`. The line
that *is* real is `Bb2In`'s: those are values `^bb0` computes, not constants
it declares.

`%45`/`%46`, the two staging buffers, are not listed: `^bb5` ends their
lifetimes, and a lifetime marker moves neither state nor valuation, so their
operand is never read. `%44` is an `undef`/`insertelement` chain rather than a
`llvm.mlir.constant`, but it is constant all the same. -/
structure EntryEnv (V : fd_r43x6_ge_decode2.Γout.Valuation)
    (a03 a14 a25 b03 b14 b25 : Pointer) : Prop where
  /-- `%32`, the fold's masks. -/
  c32 : V (⟨162, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = toBitVecValue 64 #v[8796093022207, 8796093022207, 8796093022207, 8796093022207,
        8796093022207, 1099511627775, 0, 0]
  /-- `%33`, the fold's shifts. -/
  c33 : V (⟨161, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = toBitVecValue 64 #v[43, 43, 43, 43, 43, 40, 0, 0]
  /-- `%34`, the `llvm.poison` the shuffles take as their dead operand. -/
  c34 : V (⟨160, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = Vector.replicate 8 PoisonOr.poison
  /-- `%27`, the fold's multipliers. -/
  c27 : V (⟨167, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = toBitVecValue 64 #v[19, 1, 1, 1, 1, 1, 0, 0]
  /-- `%25`, the signed fold's permute indices. -/
  c25 : V (⟨169, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = toBitVecValue 64 #v[5, 0, 1, 2, 3, 4, 8, 8]
  /-- `%24 = dense<0>`, the vector both failure paths store. -/
  czero : V (⟨170, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = zeroVec.map PoisonOr.value
  /-- `%23 = dense<18>`, the signed fold's multiplier. -/
  c23 : V (⟨171, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = toBitVecValue 64 #v[18, 18, 18, 18, 18, 18, 18, 18]
  /-- `%22 = [-1, 0, …]`, the signed fold's lane-0 mask. -/
  c22 : V (⟨172, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = toBitVecValue 64 #v[18446744073709551615, 0, 0, 0, 0, 0, 0, 0]
  /-- `%21`, the signed fold's bias. -/
  c21 : V (⟨173, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = toBitVecValue 64 #v[159383552, 1048576, 1048576, 1048576, 1048576, 1048576, 0, 0]
  /-- `%19 = one`, the multiplier when the direct root works, and the `Z` the
  transpose splices in. -/
  c19 : V (⟨175, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = oneVec.map PoisonOr.value
  /-- `%18 = p` with the signed fold's bias taken out, what `fd_r43x6_neg`
  subtracts from -- `Proof/Sub.lean`'s `negConst`. -/
  c18 : V (⟨176, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = toBitVecValue 64 negConst
  /-- `%17 = 0`, what `^bb1`'s `icmp eq` compares against, and `^bb2`'s
  return code. -/
  c17 : V (⟨177, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var (SLLVM.Ty.bitvec 32))
    = .value 0#32
  /-- `%16 = -1`, `^bb3`'s return code. -/
  cm1 : V (⟨178, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var (SLLVM.Ty.bitvec 32))
    = .value (-1#32)
  /-- `%15 = -2`, `^bb4`'s return code. -/
  cm2 : V (⟨179, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var (SLLVM.Ty.bitvec 32))
    = .value (-2#32)
  /-- `%14 = -1 : i8`, what turns an `i8` `0`/`1` into an all-lanes mask. -/
  c14 : V (⟨180, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var (SLLVM.Ty.bitvec 8))
    = .value 255#8
  /-- `%13 = sqrt_m1`, the multiplier when it does not. -/
  c13 : V (⟨181, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = sqrtM1Vec.map PoisonOr.value
  /-- `%12`, the transpose's first permute indices. -/
  c12 : V (⟨182, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = toBitVecValue 64 #v[0, 1, 8, 9, 4, 5, 12, 13]
  /-- `%11`, its second. -/
  c11 : V (⟨183, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = toBitVecValue 64 #v[2, 3, 10, 11, 6, 7, 12, 13]
  /-- `%10 = dense<43>`, the QUAD reduce's shift. -/
  c10 : V (⟨184, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = toBitVecValue 64 quadShift43
  /-- `%9`, its `25`-lane variant. -/
  c9 : V (⟨185, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = toBitVecValue 64 quadShift48
  /-- `%44`, the `undef`/`insertelement` chain: `19` in the top four lanes,
  poison in the bottom four, which the reduce never reads. -/
  c44 : V (⟨150, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8) = quadMul19
  /-- `%1 = dense<2^43-1>`, the QUAD reduce's mask. -/
  c1 : V (⟨193, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = toBitVecValue 64 quadMask43
  /-- `%0`, its `25`-lane variant. -/
  c0 : V (⟨194, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
    = toBitVecValue 64 quadMask48
  /-- `%arg0`, `a`'s `03` out-vector. -/
  va03 : V (⟨202, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var SLLVM.Ty.ptr) = .value a03
  /-- `%arg1`, `a`'s `14`. -/
  va14 : V (⟨201, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var SLLVM.Ty.ptr) = .value a14
  /-- `%arg2`, `a`'s `25`. -/
  va25 : V (⟨200, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var SLLVM.Ty.ptr) = .value a25
  /-- `%arg4`, `b`'s `03`. -/
  vb03 : V (⟨198, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var SLLVM.Ty.ptr) = .value b03
  /-- `%arg5`, `b`'s `14`. -/
  vb14 : V (⟨197, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var SLLVM.Ty.ptr) = .value b14
  /-- `%arg6`, `b`'s `25` -- the one `^bb5` writes. -/
  vb25 : V (⟨196, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var SLLVM.Ty.ptr) = .value b25

/-! ### Storing through an ambient pointer

Every store in these four blocks writes a whole `vector<8xi64>` through one of
the region *arguments*, which a tail block only knows from `EntryEnv`. -/

/-- `peel_store_amb x, p, hp, s with h…` -- `peel_store` for a *tail* block's
whole-vector store.

The one difference is that the operand side goal is simplified in two passes:
the base set, and then the ambient facts. In a single pass `Expr.denoteOp`
unfolds but the block's `Ctxt.Valuation.ofHVector args.reverse ++ V` is left
standing, and the `run_store` rewrite then has nothing to match -- `simp` does
not revisit the valuation applications the unfolding exposes.

Kept here rather than folded into `peel_store`, whose other callers are
mid-derivation. -/
macro "peel_store_amb " x:term ", " p:term ", " hp:term ", " st:term
    " with " l:term,+ : tactic =>
  `(tactic|
   (try simp only [bind_assoc]
    rw [BlockCom.run_bind_denote_var_of_nil
      (s' := ({ $st with mem := ($st).mem.splice $p (vecBV $x) } : GlobalState))
      (by try simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
          try simp only [$[$l:term],*]
          rw [run_liftM (run_store (t := .vector 8 (.bitvec (.concrete 64)))
            (x := ($x).map PoisonOr.value) (flatten_vecBV $x)
            (show Fits (($st).mem) $p 512 from Fits.mono $hp (by omega)))]
          rfl)]))

/-- `peel_store_amb x, p, hp, s as s' := hs' with h…` -- the same, naming the
state the store lands in, so a block that chains five of them carries `fvar`s
rather than five nested structure updates. -/
macro "peel_store_amb " x:term ", " p:term ", " hp:term ", " st:term
    " as " st':term " := " hst':term " with " l:term,+ : tactic =>
  `(tactic|
   (try simp only [bind_assoc]
    rw [BlockCom.run_bind_denote_var_of_nil (s' := $st')
      (by try simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
          try simp only [$[$l:term],*]
          rw [run_liftM (run_store (t := .vector 8 (.bitvec (.concrete 64)))
            (x := ($x).map PoisonOr.value) (flatten_vecBV $x)
            (show Fits (($st).mem) $p 512 from Fits.mono $hp (by omega)))]
          rw [$hst':term]
          rfl)]))

/-- `peel_load_vec_amb v, p, hp, hval, s with h…` -- `peel_load_vec` for a
*tail* block, `peel_store_amb`'s counterpart. The shared tactic has no `with`
clause, so the pointer operand -- which a tail block knows only from
`EntryEnv` -- is never resolved and the `run_load` rewrite finds nothing. -/
macro "peel_load_vec_amb " v:term ", " p:term ", " hp:term ", " hval:term ", " st:term
    " with " l:term,+ : tactic =>
  `(tactic|
   (try simp only [bind_assoc]
    rw [BlockCom.run_bind_denote_var_of_value (x := ($v).map PoisonOr.value) (s' := $st)
      (by try simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
          try simp only [$[$l:term],*]
          rw [run_liftM (run_load (t := .vector 8 (.bitvec (.concrete 64)))
            (($hp).1.choose_spec.1)
            (by have := ($hp).1.choose_spec.2
                show ($p).offsetInBits + 512 ≤ _
                simp only [LiveBlock.lengthInBits] at *
                omega))]
          rw [unflatten_readVec $hp (live?_of_getElem? ($hp).1.choose_spec.1), $hval:term]
          rfl)]))

/-! ### `^bb5`, the shared exit -/

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **`^bb5` runs.** One store through `%arg6`, the two lifetime ends, and the
`int` the φ carries comes back as the region's result. -/
theorem bb5_run {V : fd_r43x6_ge_decode2.Γout.Valuation}
    {a03 a14 a25 b03 b14 b25 : Pointer} (env : EntryEnv V a03 a14 a25 b03 b14 b25)
    (v : Vector (BitVec 64) 8) (r : LLVM.IntW 32)
    {s : GlobalState} (hb25 : Fits s.mem b25 512) :
    StateT.run (fd_r43x6_ge_decode2.blocks.run V (bb5 v r)) s
      = .value ([r]ₕ, ({ s with mem := s.mem.splice b25 (vecBV v) } : GlobalState)) := by
  denote_enter_block
  peel_store_amb v, b25, hb25, s with simp_spine, env.vb25
  iterate 2 peel_lifetime
  simp_return

/-! ### `^bb3` and `^bb4`, the two failure paths

The same five stores -- `%arg0`, `%arg4`, `%arg1`, `%arg5`, `%arg2` -- and the
same branch to `^bb5` carrying `%24`; they differ only in the return code the
φ takes, `%16 = -1` against `%15 = -2`.
-/

/-- The memory a failure path leaves: all six out-vectors zeroed, spliced in
the order the blocks write them -- `^bb3`/`^bb4`'s five and then `^bb5`'s.
Distinct pointers commute, but it is the caller that knows they are distinct,
so the order is kept as written. -/
def zeroOutMem (m : MemoryState) (a03 a14 a25 b03 b14 b25 : Pointer) : MemoryState :=
  (((((m.splice a03 (vecBV zeroVec)).splice b03 (vecBV zeroVec)).splice
      a14 (vecBV zeroVec)).splice b14 (vecBV zeroVec)).splice
      a25 (vecBV zeroVec)).splice b25 (vecBV zeroVec)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **`^bb3` runs**: `_vsa` is not a point. All six out-vectors come back
zeroed and the region returns `-1`. -/
theorem bb3_run {V : fd_r43x6_ge_decode2.Γout.Valuation}
    {a03 a14 a25 b03 b14 b25 : Pointer} (env : EntryEnv V a03 a14 a25 b03 b14 b25)
    {s : GlobalState}
    (ha03 : Fits s.mem a03 512) (ha14 : Fits s.mem a14 512) (ha25 : Fits s.mem a25 512)
    (hb03 : Fits s.mem b03 512) (hb14 : Fits s.mem b14 512) (hb25 : Fits s.mem b25 512) :
    StateT.run (fd_r43x6_ge_decode2.blocks.run V bb3) s
      = .value ([(.value (-1#32) : LLVM.IntW 32)]ₕ,
          ({ s with mem := zeroOutMem s.mem a03 a14 a25 b03 b14 b25 } : GlobalState)) := by
  denote_enter_block
  -- `%arg0`, `%arg4`, `%arg1`, `%arg5`, `%arg2`: five stores of `%24`
  refine name_of ({ s with mem := s.mem.splice a03 (vecBV zeroVec) } : GlobalState)
    fun m₁ hm₁ => ?_
  peel_store_amb zeroVec, a03, ha03, s as m₁ := hm₁ with
    simp_spine, env.czero, env.va03
  have hb03₁ : Fits m₁.mem b03 512 := hm₁ ▸ fits_splice hb03
  refine name_of ({ m₁ with mem := m₁.mem.splice b03 (vecBV zeroVec) } : GlobalState)
    fun m₂ hm₂ => ?_
  peel_store_amb zeroVec, b03, hb03₁, m₁ as m₂ := hm₂ with
    simp_spine, env.czero, env.vb03
  have ha14₂ : Fits m₂.mem a14 512 := hm₂ ▸ fits_splice (hm₁ ▸ fits_splice ha14)
  refine name_of ({ m₂ with mem := m₂.mem.splice a14 (vecBV zeroVec) } : GlobalState)
    fun m₃ hm₃ => ?_
  peel_store_amb zeroVec, a14, ha14₂, m₂ as m₃ := hm₃ with
    simp_spine, env.czero, env.va14
  have hb14₃ : Fits m₃.mem b14 512 :=
    hm₃ ▸ fits_splice (hm₂ ▸ fits_splice (hm₁ ▸ fits_splice hb14))
  refine name_of ({ m₃ with mem := m₃.mem.splice b14 (vecBV zeroVec) } : GlobalState)
    fun m₄ hm₄ => ?_
  peel_store_amb zeroVec, b14, hb14₃, m₃ as m₄ := hm₄ with
    simp_spine, env.czero, env.vb14
  have ha25₄ : Fits m₄.mem a25 512 :=
    hm₄ ▸ fits_splice (hm₃ ▸ fits_splice (hm₂ ▸ fits_splice (hm₁ ▸ fits_splice ha25)))
  refine name_of ({ m₄ with mem := m₄.mem.splice a25 (vecBV zeroVec) } : GlobalState)
    fun m₅ hm₅ => ?_
  peel_store_amb zeroVec, a25, ha25₄, m₄ as m₅ := hm₅ with
    simp_spine, env.czero, env.va25
  -- `br (%24, %16) -> ^bb5`
  have hb25₅ : Fits m₅.mem b25 512 :=
    hm₅ ▸ fits_splice (hm₄ ▸ fits_splice (hm₃ ▸ fits_splice
      (hm₂ ▸ fits_splice (hm₁ ▸ fits_splice hb25))))
  simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm,
    simp_spine, env.czero, env.cm1]
  rw [bb5_run env zeroVec (.value (-1#32)) hb25₅]
  simp only [hm₅, hm₄, hm₃, hm₂, hm₁, zeroOutMem]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **`^bb4` runs**: `_vsb` is not a point. `^bb3`'s script with `%15` in place
of `%16`; all six out-vectors come back zeroed and the region returns `-2`. -/
theorem bb4_run {V : fd_r43x6_ge_decode2.Γout.Valuation}
    {a03 a14 a25 b03 b14 b25 : Pointer} (env : EntryEnv V a03 a14 a25 b03 b14 b25)
    {s : GlobalState}
    (ha03 : Fits s.mem a03 512) (ha14 : Fits s.mem a14 512) (ha25 : Fits s.mem a25 512)
    (hb03 : Fits s.mem b03 512) (hb14 : Fits s.mem b14 512) (hb25 : Fits s.mem b25 512) :
    StateT.run (fd_r43x6_ge_decode2.blocks.run V bb4) s
      = .value ([(.value (-2#32) : LLVM.IntW 32)]ₕ,
          ({ s with mem := zeroOutMem s.mem a03 a14 a25 b03 b14 b25 } : GlobalState)) := by
  denote_enter_block
  refine name_of ({ s with mem := s.mem.splice a03 (vecBV zeroVec) } : GlobalState)
    fun m₁ hm₁ => ?_
  peel_store_amb zeroVec, a03, ha03, s as m₁ := hm₁ with
    simp_spine, env.czero, env.va03
  have hb03₁ : Fits m₁.mem b03 512 := hm₁ ▸ fits_splice hb03
  refine name_of ({ m₁ with mem := m₁.mem.splice b03 (vecBV zeroVec) } : GlobalState)
    fun m₂ hm₂ => ?_
  peel_store_amb zeroVec, b03, hb03₁, m₁ as m₂ := hm₂ with
    simp_spine, env.czero, env.vb03
  have ha14₂ : Fits m₂.mem a14 512 := hm₂ ▸ fits_splice (hm₁ ▸ fits_splice ha14)
  refine name_of ({ m₂ with mem := m₂.mem.splice a14 (vecBV zeroVec) } : GlobalState)
    fun m₃ hm₃ => ?_
  peel_store_amb zeroVec, a14, ha14₂, m₂ as m₃ := hm₃ with
    simp_spine, env.czero, env.va14
  have hb14₃ : Fits m₃.mem b14 512 :=
    hm₃ ▸ fits_splice (hm₂ ▸ fits_splice (hm₁ ▸ fits_splice hb14))
  refine name_of ({ m₃ with mem := m₃.mem.splice b14 (vecBV zeroVec) } : GlobalState)
    fun m₄ hm₄ => ?_
  peel_store_amb zeroVec, b14, hb14₃, m₃ as m₄ := hm₄ with
    simp_spine, env.czero, env.vb14
  have ha25₄ : Fits m₄.mem a25 512 :=
    hm₄ ▸ fits_splice (hm₃ ▸ fits_splice (hm₂ ▸ fits_splice (hm₁ ▸ fits_splice ha25)))
  refine name_of ({ m₄ with mem := m₄.mem.splice a25 (vecBV zeroVec) } : GlobalState)
    fun m₅ hm₅ => ?_
  peel_store_amb zeroVec, a25, ha25₄, m₄ as m₅ := hm₅ with
    simp_spine, env.czero, env.va25
  -- `br (%24, %15) -> ^bb5`
  have hb25₅ : Fits m₅.mem b25 512 :=
    hm₅ ▸ fits_splice (hm₄ ▸ fits_splice (hm₃ ▸ fits_splice
      (hm₂ ▸ fits_splice (hm₁ ▸ fits_splice hb25))))
  simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm,
    simp_spine, env.czero, env.cm2]
  rw [bb5_run env zeroVec (.value (-2#32)) hb25₅]
  simp only [hm₅, hm₄, hm₃, hm₂, hm₁, zeroOutMem]

/-! ### `^bb1`, the second encoding's remaining square-root test -/

/-- `%195 = llvm.add %184, %90`: lanewise, `overflow<none>`, so total. -/
def addVec (x y : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  Vector.ofFn fun i => x[i] + y[i]

/-- The `i32` `fd_r43x6_is_nonzero` returns on an `s62` vector. -/
abbrev nonzeroBit (x : Vector (BitVec 64) 8) : BitVec 32 :=
  if ((R43x6.decode' x : ℤ) : ZMod p) = 0 then 0 else 1

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **`^bb1` runs.** `fd_r43x6_is_nonzero( %184 + %90 )` `and`ed with `%191`,
the test `^bb0` already made: control reaches `^bb2` when the conjunction is
zero -- one of the two roots works -- and `^bb4` when it is not.

`%191` is left as an opaque `i32`: it is `^bb0`'s second `is_nonzero`, and
what it means is that caller's business. The call allocates nothing and writes
nothing, so the only thing that moves is the frame `runFunction` pops. -/
theorem bb1_run {V : fd_r43x6_ge_decode2.Γout.Valuation}
    {a03 a14 a25 b03 b14 b25 : Pointer} (env : EntryEnv V a03 a14 a25 b03 b14 b25)
    {x184 x90 : Vector (BitVec 64) 8} {t1nzb : BitVec 32}
    (h184 : V (⟨10, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
      = x184.map PoisonOr.value)
    (h90 : V (⟨104, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8)
      = x90.map PoisonOr.value)
    (h191 : V (⟨3, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var (SLLVM.Ty.bitvec 32))
      = .value t1nzb)
    (hs62 : R43x6.S62 ((addVec x184 x90).take R43x6.limbCount))
    (s : GlobalState) :
    StateT.run (fd_r43x6_ge_decode2.blocks.run V bb1) s
      = StateT.run (fd_r43x6_ge_decode2.blocks.run V
          (if nonzeroBit (addVec x184 x90) &&& t1nzb = 0 then bb2 else bb4))
        (s.popFrame s.mem) := by
  denote_enter_block
  denote_number_from 195
  denote_step_all v 195
  replace hv195 : v195 = (addVec x184 x90).map PoisonOr.value := by
    simp only [hv195, Expr.denoteOp1, Expr.denoteOpPure]
    simp_peephole
    simp only [HVector.head, simp_spine, h184, h90]
    apply Vector.ext
    intro i hi
    simp [InstCombine.binaryDenote, LLVM.add, LLVM.add?, addVec]
  peel_call (is_nonzero_step hs62 s _ rfl) with hv195, simp_spine
  -- `%197 = and %196, %191`, `%198 = icmp eq %197, %17`
  denote_step_all v 198
  replace hv197 : v197 = .value (nonzeroBit (addVec x184 x90) &&& t1nzb) := by
    simp only [hv197, Expr.denoteOp1, Expr.denoteOpPure]
    simp_peephole
    simp only [HVector.head, simp_spine, h191]
    simp [LLVM.and, LLVM.and?, nonzeroBit]
  replace hv198 : v198
      = .value (if nonzeroBit (addVec x184 x90) &&& t1nzb = 0 then 1 else 0) := by
    simp only [hv198, hv197, Expr.denoteOp1, Expr.denoteOpPure]
    simp_peephole
    simp only [HVector.head, simp_spine, env.c17]
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp']
    split <;> rename_i hc
    · simp [hc]
    · rw [beq_eq_false_iff_ne.mpr hc]; rfl
  subst hv198
  simp only [BlockCom.denote_term, Terminator.denote_condBr, Ctxt.Valuation.cons_zero]
  split <;> rfl

/-! ### Splice chains, as `≈` sees them

`s ≈ s'` is extensional: same counter, same globals, same `live?` at every
block. So a chain of splices is settled block by block, and the only facts
needed are that a splice is invisible at another block and that it overwrites
at its own.

-/

/-- What a splice does to `live?`, at every block at once. -/
theorem live?_splice {m : MemoryState} {p : Pointer} {w : Nat} (x : BitVec w) (c : BlockId) :
    (m.splice p x).live? c
      = if c = p.id then
          (m.live? c).map fun b =>
            { length := b.length, bytes := spliceBits b.bytes p.offsetInBits x }
        else m.live? c := by
  by_cases hc : c = p.id
  · subst hc
    rw [if_pos rfl]
    cases hm : m.live? p.id with
    | none => simp [live?_splice_eq_none hm]
    | some b => simp [splicedLive m p b hm x]
  · rw [if_neg hc, live?_splice_ne (fun h => hc h.symm)]

/-- A splice at a block is invisible under a later one at the same block, as
`live?`'s `Option.map` composes them. -/
private theorem splice_block_comp {w : Nat} (off : Nat) (x y : BitVec w) :
    (((fun b : LiveBlock => { length := b.length, bytes := spliceBits b.bytes off y })
        ∘ (fun b : LiveBlock => { length := b.length, bytes := spliceBits b.bytes off x }))
      : LiveBlock → LiveBlock)
      = fun b : LiveBlock => { length := b.length, bytes := spliceBits b.bytes off y } := by
  funext b
  simp [Function.comp, spliceBits_spliceBits_self]

/-- **The eleven splices `^bb2` makes, as the six the spec names.** Each of the
transpose's six is overwritten by the reduce -- except `f`, whose reduce store
is `^bb5`'s, so the transpose's value is what `^bb2` leaves there.

Driven by the walk's own naming hypotheses rather than by the memory terms:
given `_ ≈ _` over eleven nested splices, unification spends minutes on the
terms, and `hm₁ … hm₁₁` are what the block already has. -/
theorem quadStores_equiv {s₀ s m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ : GlobalState}
    {a b c d e f : Pointer} {A B C D E F A' B' C' D' E' : BitVec 512}
    (hba : b.id ≠ a.id) (hca : c.id ≠ a.id) (hda : d.id ≠ a.id)
    (hea : e.id ≠ a.id) (hfa : f.id ≠ a.id)
    (hcb : c.id ≠ b.id) (hdb : d.id ≠ b.id) (heb : e.id ≠ b.id) (hfb : f.id ≠ b.id)
    (hdc : d.id ≠ c.id) (hec : e.id ≠ c.id) (hfc : f.id ≠ c.id)
    (hed : e.id ≠ d.id) (hfd : f.id ≠ d.id) (hfe : f.id ≠ e.id)
    (h1 : m₁ = { s with mem := s.mem.splice a A })
    (h2 : m₂ = { m₁ with mem := m₁.mem.splice b B })
    (h3 : m₃ = { m₂ with mem := m₂.mem.splice c C })
    (h4 : m₄ = { m₃ with mem := m₃.mem.splice d D })
    (h5 : m₅ = { m₄ with mem := m₄.mem.splice e E })
    (h6 : m₆ = { m₅ with mem := m₅.mem.splice f F })
    (h7 : m₇ = { m₆ with mem := m₆.mem.splice a A' })
    (h8 : m₈ = { m₇ with mem := m₇.mem.splice b B' })
    (h9 : m₉ = { m₈ with mem := m₈.mem.splice c C' })
    (h10 : m₁₀ = { m₉ with mem := m₉.mem.splice d D' })
    (h11 : m₁₁ = { m₁₀ with mem := m₁₀.mem.splice e E' })
    (h0 : s₀ ≈ s) :
    m₁₁ ≈ ({ s₀ with mem := (((((s₀.mem.splice a A').splice b B').splice c C').splice
        d D').splice e E').splice f F } : GlobalState) := by
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  refine ⟨h0.1.symm, h0.globals.symm, fun k => ?_⟩
  simp only [live?_splice, h0.live k]
  by_cases ka : k = a.id
  · subst ka
    simp [Ne.symm hba, Ne.symm hca, Ne.symm hda, Ne.symm hea, Ne.symm hfa,
      Option.map_map, splice_block_comp]
  by_cases kb : k = b.id
  · subst kb
    simp [ka, Ne.symm hcb, Ne.symm hdb, Ne.symm heb, Ne.symm hfb,
      Option.map_map, splice_block_comp]
  by_cases kc : k = c.id
  · subst kc
    simp [ka, kb, Ne.symm hdc, Ne.symm hec, Ne.symm hfc,
      Option.map_map, splice_block_comp]
  by_cases kd : k = d.id
  · subst kd
    simp [ka, kb, kc, Ne.symm hed, Ne.symm hfd, Option.map_map, splice_block_comp]
  by_cases ke : k = e.id
  · subst ke
    simp [ka, kb, kc, kd, Ne.symm hfe, Option.map_map, splice_block_comp]
  by_cases kf : k = f.id
  · subst kf
    simp [ka, kb, kc, kd, ke]
  simp [ka, kb, kc, kd, ke, kf]

/-! ### `^bb2`, the success path

The block the other four exist to reach. Its shape, in five stages:

1. `%199`-`%206` -- the sign selects. `%190`/`%191` are `^bb0`'s two
   `is_nonzero`s, `0` exactly when the *direct* root works; each is turned
   into an all-lanes mask and selects `%19 = 1` or `%13 = sqrt(-1)` as the
   multiplier.
2. `%207`-`%216` -- two `fd_r43x6_mul_fast` and their folds: the candidate
   root times that multiplier, so `x² v = u` now holds on both sides.
3. `%217`-`%244` -- `fd_r43x6_diagnose` on each root, compared against the
   encoding's sign bit (`%54`/`%56`), and the conditional negate `p - x`
   behind a `select`. `%231`/`%244` are the final `x`s.
4. `%245`-`%254` -- `x · y` through `fd_r43x6_mul_fast`, giving `T`.
5. `%255`-`%308` -- the QUAD transpose (`vpermi2var` plus shuffles), six
   stores, then a reload-and-reduce of each. Five of the six reduced vectors
   are stored here; the sixth, `%308`, rides the φ to `^bb5`.

`bb2_run` is stated in the form that composes: it lands on `^bb5` with `%308`
as the φ, so `bb5_run` finishes the store to `%arg6`.
-/

/-- What `^bb0` *computes* and `^bb2` reads: the two candidate roots, the two
unpacked `y`s, the two encoded sign bits and the two square-root decisions.
Data rather than scaffolding, so it is separate from `EntryEnv`. -/
structure Bb2In (V : fd_r43x6_ge_decode2.Γout.Valuation)
    (xa xb ya yb : Vector (BitVec 64) 8) (sgnA sgnB t1nza t1nzb : BitVec 32) : Prop where
  /-- `%159`, the `a` candidate root, folded. -/
  x159 : V (⟨35, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8) = xa.map PoisonOr.value
  /-- `%164`, the `b` one. -/
  x164 : V (⟨30, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8) = xb.map PoisonOr.value
  /-- `%60 = fd_r43x6_unpack( wv_ld( _sa ) )`, the `a` encoding's `y`. -/
  y60 : V (⟨134, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8) = ya.map PoisonOr.value
  /-- `%62`, the `b` one. -/
  y62 : V (⟨132, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var V8) = yb.map PoisonOr.value
  /-- `%54`, the `a` encoding's sign bit, as the `i32` the `icmp` compares. -/
  s54 : V (⟨140, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var (SLLVM.Ty.bitvec 32)) = .value sgnA
  /-- `%56`, the `b` one. -/
  s56 : V (⟨138, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var (SLLVM.Ty.bitvec 32)) = .value sgnB
  /-- `%190 = fd_r43x6_is_nonzero( xa² v - u + p )`: `0` when the direct root
  works on the `a` side. -/
  n190 : V (⟨4, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var (SLLVM.Ty.bitvec 32)) = .value t1nza
  /-- `%191`, the `b` one -- the same value `bb1_run` reads. -/
  n191 : V (⟨3, by rfl⟩ : fd_r43x6_ge_decode2.Γout.Var (SLLVM.Ty.bitvec 32)) = .value t1nzb

/-- The six out-vectors are six distinct blocks. `^bb2` needs it twice: it is
what makes the reload of each read back what the transpose stored, and what
collapses its twelve splices to the six the spec names.

Fifteen fields rather than a `List.Pairwise`: the reload uses each pair by
name, and unpacking a `Pairwise` at every use costs more than writing them
out. Each is oriented as the store order needs it -- the later pointer first,
since that is the splice a reload of the earlier one reads past. -/
structure SixDistinct (a03 a14 a25 b03 b14 b25 : Pointer) : Prop where
  a14_a03 : a14.id ≠ a03.id
  a25_a03 : a25.id ≠ a03.id
  b03_a03 : b03.id ≠ a03.id
  b14_a03 : b14.id ≠ a03.id
  b25_a03 : b25.id ≠ a03.id
  a25_a14 : a25.id ≠ a14.id
  b03_a14 : b03.id ≠ a14.id
  b14_a14 : b14.id ≠ a14.id
  b25_a14 : b25.id ≠ a14.id
  b03_a25 : b03.id ≠ a25.id
  b14_a25 : b14.id ≠ a25.id
  b25_a25 : b25.id ≠ a25.id
  b14_b03 : b14.id ≠ b03.id
  b25_b03 : b25.id ≠ b03.id
  b25_b14 : b25.id ≠ b14.id

/-! ### What the block computes, in the field

The arithmetic `^bb2` is doing, with nothing about the program left: the
`sqrt(-1)` correction, the sign fixup, and the QUAD the transpose packs. -/

/-- **`fd_r43x6_diagnose` is the element's low bit.** `-1` at zero, and
otherwise the parity of the canonical representative -- which is what
`reduce` leaves and `ZMod.val` reads. -/
theorem diagnose_eq {z : Vector (BitVec 64) 8}
    (hb : ∀ k : Fin R43x6.limbCount,
      0 ≤ R43x6.extractLimbs z k ∧ R43x6.extractLimbs z k < 2 ^ 44) :
    diagnose (R43x6.extractLimbs z)
      = if vecValue z = 0 then -1#32
        else if (vecValue z).val % 2 = 0 then 0#32 else 1#32 := by
  have hs62 : R43x6.S62 (z.take R43x6.limbCount) :=
    ⟨fun i => by rw [R43x6.toInts_take]; have := (hb i).2; omega,
     fun i => by rw [R43x6.toInts_take]; have := (hb i).1; omega⟩
  have hpre : BcpPre (2 ^ 20) (R43x6.extractLimbs z) :=
    bcpPre_of_s62 (by norm_num) (by norm_num) hs62
  have hval : ((R43x6.decode' z : ℤ) : ZMod p) = vecValue z := decode'_cast_eq_vecValue z hb
  obtain ⟨h04, h5, hnn, hlt⟩ := reduceIsCanonical (R43x6.extractLimbs z) hpre
  have hpres := reducePreservesValue (R43x6.extractLimbs z) hpre
  rw [R43x6.decodeLimbs_extractLimbs, hval] at hpres
  -- the reduced value is `(vecValue z).val` on the nose
  have hvalEq : ((vecValue z).val : ℤ) = R43x6.decodeLimbs (reduce (R43x6.extractLimbs z)) := by
    rw [← hpres, ZMod.val_intCast]
    exact (Int.emod_emod_of_dvd _ (dvd_refl _)) ▸ Int.emod_eq_of_lt hnn hlt
  have hdec : isNonzero (R43x6.extractLimbs z) = 0 ↔ vecValue z = 0 := by
    rw [← hval]; exact isNonzeroDecidesVec z hs62
  -- the low limb of the canonical representative is the value's low bit
  have hpar : ((vecValue z).val : ℤ) % 2 = reduce (R43x6.extractLimbs z) 0 % 2 := by
    rw [hvalEq]; simp only [R43x6.decodeLimbs_eq]; omega
  have hr0 := h04 0 (by decide)
  simp only [diagnose]
  by_cases hz : vecValue z = 0
  · rw [if_pos (hdec.mpr hz), if_pos hz]
  · rw [if_neg (fun h => hz (hdec.mp h)), if_neg hz]
    have : ((vecValue z).val % 2 : ℕ) = ((vecValue z).val : ℤ) % 2 := by push_cast; ring
    split <;> rename_i hc
    · rw [show reduce (R43x6.extractLimbs z) 0 % 2 = 0 by omega]; rfl
    · rw [show reduce (R43x6.extractLimbs z) 0 % 2 = 1 by omega]; rfl

/-- `%19 = fd_r43x6_one()` is `1`. -/
theorem vecValue_oneVec : vecValue oneVec = 1 := by
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  have h0 : (0 : BitVec 64).toNat = 0 := rfl
  norm_num [vecValue_eq_decodeNat, decodeNat_eq, limbNat, h0, h1]

/-- `%13 = fd_r43x6_imag()` squares to `-1`. -/
theorem vecValue_sqrtM1Vec_sq : vecValue sqrtM1Vec ^ 2 = -1 := by
  have h0 : (3467281080496 : BitVec 64).toNat = 3467281080496 := rfl
  have h1 : (6582290652611 : BitVec 64).toNat = 6582290652611 := rfl
  have h2 : (5210002954932 : BitVec 64).toNat = 5210002954932 := rfl
  have h3 : (329084955603 : BitVec 64).toNat = 329084955603 := rfl
  have h4 : (4526638806224 : BitVec 64).toNat = 4526638806224 := rfl
  have h5 : (373767602335 : BitVec 64).toNat = 373767602335 := rfl
  have : vecValue sqrtM1Vec
      = (19681161376707505956807079304988542015446066515923890162744021073123829784752
        : ZMod p) := by
    norm_num [vecValue_eq_decodeNat, decodeNat_eq, limbNat, h0, h1, h2, h3, h4, h5]
  rw [this]
  decide

/-- Negation flips the parity of the representative: `p` is odd. -/
theorem val_neg_parity {w : ZMod p} (hw : w ≠ 0) :
    ((-w).val % 2 = 0) ↔ ¬(w.val % 2 = 0) := by
  have hp : p % 2 = 1 := by norm_num [p]
  have hlt : w.val < p := ZMod.val_lt w
  have hne : w.val ≠ 0 := fun h => hw ((ZMod.val_eq_zero w).mp h)
  rw [ZMod.neg_val, if_neg hw]
  omega


/-- `vecValue` of the negation. -/
theorem vecValue_negVec {x : Vector (BitVec 64) 8}
    (hx : ∀ k, 0 ≤ R43x6.extractLimbs x k ∧ R43x6.extractLimbs x k < 2 ^ 44) :
    vecValue (negVec x) = -vecValue x := by
  rw [← decode'_cast_eq_vecValue _ (extractLimbs_negVec hx),
    ← decode'_cast_eq_vecValue _ hx, decode'_negVec hx]

/-- The `extractLimbs` bound `unpacked` gives. -/
theorem extractLimbs_of_unpacked {y : Vector (BitVec 64) 8} (h : R43x6.Unpacked y)
    (k : Fin R43x6.limbCount) :
    0 ≤ R43x6.extractLimbs y k ∧ R43x6.extractLimbs y k < 2 ^ 44 := by
  obtain ⟨h04, h5⟩ := h
  by_cases hk : (k : ℕ) < 5
  · have := h04 k hk; omega
  · have hk5 : k = 5 := Fin.ext (by have := k.isLt; simp only [R43x6.limbCount] at *; omega)
    rw [hk5]; omega

/-- **What one side of `^bb2` computes, in the field.** -/
theorem decodes_side {ua : Vector (BitVec 64) 4}
    {x y t3 x' : Vector (BitVec 64) 8} {sgn t1nz : BitVec 32}
    (hy : ((R43x6.decode' y : ℤ) : ZMod p) = wvY ua) (hyU : R43x6.Unpacked y)
    (hsgn : sgn = if wvSign ua then 1 else 0)
    (ht3 : t3 = if t1nz = 0 then oneVec else sqrtM1Vec)
    (h190 : t1nz = 0 ↔ vecValue x ^ 2 * (d * wvY ua ^ 2 + 1) = wvY ua ^ 2 - 1)
    (hroot : t1nz = 0 ∨ vecValue x ^ 2 * (d * wvY ua ^ 2 + 1) = -(wvY ua ^ 2 - 1))
    (hmul : MulInl x t3 (foldVec (mulVec x t3)))
    (hb : ∀ k, 0 ≤ R43x6.extractLimbs (foldVec (mulVec x t3)) k
              ∧ R43x6.extractLimbs (foldVec (mulVec x t3)) k < 2 ^ 44)
    (hx' : x' = if diagnose (R43x6.extractLimbs (foldVec (mulVec x t3))) = sgn
            then foldVec (mulVec x t3) else negVec (foldVec (mulVec x t3)))
    (hxy : MulInl x' y (foldVec (mulVec x' y))) :
    Decodes ua (foldQuad (packQuad x' y oneVec (foldVec (mulVec x' y)))) := by
  have hyB := extractLimbs_of_unpacked hyU
  have hvy : vecValue y = wvY ua := by rw [← decode'_cast_eq_vecValue y hyB]; exact hy
  -- the candidate root, corrected by `sqrt(-1)` when the direct one failed
  have hZv : vecValue (foldVec (mulVec x t3)) ^ 2 * (d * wvY ua ^ 2 + 1) = wvY ua ^ 2 - 1 := by
    rw [hmul.value, ht3]
    by_cases hc : t1nz = 0
    · rw [if_pos hc, vecValue_oneVec, mul_one]; exact h190.mp hc
    · rw [if_neg hc, mul_pow, vecValue_sqrtM1Vec_sq]
      linear_combination -hroot.resolve_left hc
  -- the sign fixup changes only the sign, so the curve equation survives it
  have hXsq : vecValue x' ^ 2 = vecValue (foldVec (mulVec x t3)) ^ 2 := by
    rw [hx']; split
    · rfl
    · rw [vecValue_negVec hb]; ring
  have hpt : (foldQuad (packQuad x' y oneVec (foldVec (mulVec x' y)))).toPoint
      = decodedPoint (vecValue x') (wvY ua) := by
    rw [toPoint_foldQuad, toPoint_packQuad, vecValue_oneVec, hxy.value, hvy]
    rfl
  -- the sign clause: `fd_r43x6_diagnose` is the low bit of the representative
  have hsign : vecValue x' ≠ 0 → ((vecValue x').val % 2 = 0 ↔ wvSign ua = false) := by
    intro hne
    have hd := diagnose_eq hb
    by_cases hz : vecValue (foldVec (mulVec x t3)) = 0
    · exact absurd (by
        rw [hx', if_neg (by rw [hd, if_pos hz, hsgn]; split <;> decide),
          vecValue_negVec hb, hz, neg_zero]) hne
    · by_cases hdg : diagnose (R43x6.extractLimbs (foldVec (mulVec x t3))) = sgn
      · rw [hx', if_pos hdg]
        rw [hd, if_neg hz, hsgn] at hdg
        by_cases hpz : (vecValue (foldVec (mulVec x t3))).val % 2 = 0
        · rw [if_pos hpz] at hdg
          simp only [hpz, true_iff]
          revert hdg; cases wvSign ua <;> simp
        · rw [if_neg hpz] at hdg
          simp only [hpz, false_iff]
          revert hdg; cases wvSign ua <;> simp
      · rw [hx', if_neg hdg, vecValue_negVec hb, val_neg_parity hz]
        rw [hd, if_neg hz, hsgn] at hdg
        by_cases hpz : (vecValue (foldVec (mulVec x t3))).val % 2 = 0
        · rw [if_pos hpz] at hdg
          simp only [hpz, not_true_eq_false, false_iff]
          revert hdg; cases wvSign ua <;> simp
        · rw [if_neg hpz] at hdg
          simp only [hpz, not_false_eq_true, true_iff]
          revert hdg; cases wvSign ua <;> simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [hpt]
  · exact onCurve_decodedPoint (by rw [hXsq]; exact hZv)
  · exact decodedPoint_Z _ _
  · exact decodedPoint_Y _ _
  · simp
  · simpa using hsign



set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000000 in
/-- **`^bb2` runs**: both encodings name a point. The six out-vectors come
back holding the two QUAD-packed points and control reaches `^bb5` with `%308`
-- `b`'s `25` vector, the one `^bb5` stores -- on the φ and `%17 = 0` as the
return code.

The hypotheses are what `^bb0` and `^bb1` between them establish: `Bb2In` for
the eight values `^bb0` computed, and then what those values *are* -- `ya`/`yb`
decode the two encodings, `sgnA`/`sgnB` are their sign bits, and `t1nza`/`t1nzb`
say whether each direct root works. `hrootA`/`hrootB` are what `^bb0` and
`^bb1` between them tested -- one of each candidate's two roots works -- and
are what make the `sqrt(-1)` branch a root rather than a wrong answer.

Only five of the six splices appear here: `%arg6`'s second store is `^bb5`'s,
which is why `%308` leaves on the φ instead. `bb5_run` closes that gap, and
the composition is the spec's `outMem`. -/
theorem bb2_run {V : fd_r43x6_ge_decode2.Γout.Valuation}
    {a03 a14 a25 b03 b14 b25 : Pointer} (env : EntryEnv V a03 a14 a25 b03 b14 b25)
    {xa xb ya yb : Vector (BitVec 64) 8} {sgnA sgnB t1nza t1nzb : BitVec 32}
    (inp : Bb2In V xa xb ya yb sgnA sgnB t1nza t1nzb)
    -- what those eight values are, in the field
    {ua ub : Vector (BitVec 64) 4}
    (hya : (R43x6.decode' ya : ZMod p) = wvY ua)
    (hyb : (R43x6.decode' yb : ZMod p) = wvY ub)
    (hsgnA : sgnA = if wvSign ua then 1 else 0)
    (hsgnB : sgnB = if wvSign ub then 1 else 0)
    (h190 : t1nza = 0 ↔ vecValue xa ^ 2 * (d * wvY ua ^ 2 + 1) = wvY ua ^ 2 - 1)
    (h191 : t1nzb = 0 ↔ vecValue xb ^ 2 * (d * wvY ub ^ 2 + 1) = wvY ub ^ 2 - 1)
    -- reaching `^bb2` means one of each candidate's two roots worked: `^bb0`
    -- made the test for `a` and `^bb1` for `b`. The second disjunct is the
    -- `sqrt(-1)` case, and is what makes `%202`/`%206`'s select a root.
    (hrootA : t1nza = 0 ∨ vecValue xa ^ 2 * (d * wvY ua ^ 2 + 1) = -(wvY ua ^ 2 - 1))
    (hrootB : t1nzb = 0 ∨ vecValue xb ^ 2 * (d * wvY ub ^ 2 + 1) = -(wvY ub ^ 2 - 1))
    -- `fd_r43x6_is_nonzero` returns `0` or `1`, and the `nsw` on `%200`/`%204`
    -- needs to know it: the decrement poisons at `-2 ^ 7` and nowhere else
    (ht1nza : t1nza = 0 ∨ t1nza = 1) (ht1nzb : t1nzb = 0 ∨ t1nzb = 1)
    -- the kernels' input contracts on what `^bb0` folded and unpacked
    (hxaU : R43x6.U44 (xa.take R43x6.limbCount)) (hxa6 : xa[6] = 0) (hxa7 : xa[7] = 0)
    (hxbU : R43x6.U44 (xb.take R43x6.limbCount)) (hxb6 : xb[6] = 0) (hxb7 : xb[7] = 0)
    (hyaU : R43x6.Unpacked ya) (hya6 : ya[6] = 0) (hya7 : ya[7] = 0)
    (hybU : R43x6.Unpacked yb) (hyb6 : yb[6] = 0) (hyb7 : yb[7] = 0)
    -- the six out-vectors
    {s : GlobalState} (hs : s.WF)
    (pa03 : IsVecPtr s.mem a03) (pa14 : IsVecPtr s.mem a14) (pa25 : IsVecPtr s.mem a25)
    (pb03 : IsVecPtr s.mem b03) (pb14 : IsVecPtr s.mem b14) (pb25 : IsVecPtr s.mem b25)
    (hne : SixDistinct a03 a14 a25 b03 b14 b25) :
    ∃ (va03 va14 va25 vb03 vb14 vb25 vpre : Vector (BitVec 64) 8) (s' : GlobalState),
      StateT.run (fd_r43x6_ge_decode2.blocks.run V bb2) s
        = StateT.run (fd_r43x6_ge_decode2.blocks.run V (bb5 vb25 (.value 0#32))) s'
      -- `vpre` is what the transpose left at `b25`: `^bb2` does not reduce that
      -- vector, `^bb5` stores `vb25` over it, so it is invisible in the
      -- composition but has to be named here
      ∧ s' ≈ ({ s with mem :=
          (((((s.mem.splice a03 (vecBV va03)).splice a14 (vecBV va14)).splice
              a25 (vecBV va25)).splice b03 (vecBV vb03)).splice
              b14 (vecBV vb14)).splice b25 (vecBV vpre) }
          : GlobalState)
      ∧ Decodes ua ⟨va03, va14, va25⟩
      ∧ Decodes ub ⟨vb03, vb14, vb25⟩
      -- what `^bb5` needs to store through `%arg6`, carried out rather than
      -- re-derived: rebuilding it from the six splices costs minutes
      ∧ Fits s'.mem b25 512 := by
  denote_enter_block
  denote_number_from 199
  -- `%199`-`%202`: the `a` sign select. `t1nza = 0` -- the direct root works --
  -- truncates to `0`, `%14 = -1` takes that to all-ones, the bitcast makes it
  -- eight true lanes, and the select picks `one`; otherwise `sqrt_m1`.
  denote_step_all v 202
  -- `t3a = fd_r43x6_if( t1nza, sqrt_m1, one )`, named the way the C names it:
  -- the walk then carries an `fvar` and `ht3a` is what says which multiplier
  -- it is, for the `mul_fast` at `%207`.
  refine name_of (if t1nza = 0 then oneVec else sqrtM1Vec) fun t3a ht3a => ?_
  replace hv202 : v202 = t3a.map PoisonOr.value := by
    rw [ht3a]
    simp only [hv202, hv201, hv200, hv199, Expr.denoteOp1, Expr.denoteOpPure]
    simp_peephole
    simp only [HVector.head, simp_spine, inp.n190, env.c14, env.c19, env.c13]
    rcases ht1nza with rfl | rfl <;>
      (apply Vector.ext; intro i hi; interval_cases i <;> rfl)
  -- `%199`-`%201` are spent: `hv202` is the whole select
  denote_clear v 199 201

  -- `%203`-`%206`: the `b` twin, `t1nzb` and `t3b` for `t1nza` and `t3a`
  denote_step_all v 206
  refine name_of (if t1nzb = 0 then oneVec else sqrtM1Vec) fun t3b ht3b => ?_
  replace hv206 : v206 = t3b.map PoisonOr.value := by
    rw [ht3b]
    simp only [hv206, hv205, hv204, hv203, Expr.denoteOp1, Expr.denoteOpPure]
    simp_peephole
    simp only [HVector.head, simp_spine, inp.n191, env.c14, env.c19, env.c13]
    rcases ht1nzb with rfl | rfl <;>
      (apply Vector.ext; intro i hi; interval_cases i <;> rfl)
  denote_clear v 203 205

  -- the two multipliers meet `fd_r43x6_mul_fast`'s input contract
  have ht3aU : R43x6.U47 (t3a.take R43x6.limbCount) := by
    rw [ht3a]; exact (selMul_contract _).1
  have ht3a6 : t3a[6] = 0 := by rw [ht3a]; exact (selMul_contract _).2.1
  have ht3a7 : t3a[7] = 0 := by rw [ht3a]; exact (selMul_contract _).2.2
  have ht3bU : R43x6.U47 (t3b.take R43x6.limbCount) := by
    rw [ht3b]; exact (selMul_contract _).1
  have ht3b6 : t3b[6] = 0 := by rw [ht3b]; exact (selMul_contract _).2.1
  have ht3b7 : t3b[7] = 0 := by rw [ht3b]; exact (selMul_contract _).2.2
  have hxaU47 : R43x6.U47 (xa.take R43x6.limbCount) := u47_of_u44 hxaU
  have hxbU47 : R43x6.U47 (xb.take R43x6.limbCount) := u47_of_u44 hxbU

  -- `%207`-`%211`: `FD_R43X6_MUL_INL( xa, xa, t3a )` -- the call, then the
  -- four fold instructions that follow it in this block
  refine name_of (s.popFrame s.mem) fun u₁ hu₁ => ?_
  rw [BlockCom.run_bind_denote_call_cfg_of_value (argTys := [V8, V8])
    (by simp only [simp_spine, inp.x159, hv202])
    (mul_step_of_take hxaU47 hxa6 hxa7 ht3aU ht3a6 ht3a7 s u₁ hu₁)]
  denote_step_reduce v 211 only [simp_spine, env.c32, env.c33, env.c27, env.c34] fold
  fold_unsigned hv211, (mulVec xa t3a), (limbNat_mul_lt hxaU47 ht3aU)
  denote_clear v 208 210
  have hmulA : MulInl xa t3a (foldVec (mulVec xa t3a)) := mul_inl hxaU47 ht3aU

  -- `%212`-`%216`: the `b` twin, at the state the first call left
  refine name_of (u₁.popFrame u₁.mem) fun u₂ hu₂ => ?_
  rw [BlockCom.run_bind_denote_call_cfg_of_value (argTys := [V8, V8])
    (by simp only [simp_spine, inp.x164, hv206])
    (mul_step_of_take hxbU47 hxb6 hxb7 ht3bU ht3b6 ht3b7 u₁ u₂ hu₂)]
  denote_step_reduce v 216 only [simp_spine, env.c32, env.c33, env.c27, env.c34] fold
  fold_unsigned hv216, (mulVec xb t3b), (limbNat_mul_lt hxbU47 ht3bU)
  denote_clear v 213 215
  have hmulB : MulInl xb t3b (foldVec (mulVec xb t3b)) := mul_inl hxbU47 ht3bU

  -- `%217`/`%218`: `x_mod_2a = fd_r43x6_diagnose( xa )` and its `b` twin. The
  -- contract is signed and what the folds left is `u44`, which `s62_of_u44`
  -- weakens.
  refine name_of (u₂.popFrame u₂.mem) fun u₃ hu₃ => ?_
  rw [BlockCom.run_bind_denote_call_cfg_of_value (argTys := [V8])
    (by simp only [simp_spine, hv211])
    (diagnose_step (s62_of_u44 hmulA.u44) u₂ u₃ hu₃)]
  refine name_of (u₃.popFrame u₃.mem) fun u₄ hu₄ => ?_
  rw [BlockCom.run_bind_denote_call_cfg_of_value (argTys := [V8])
    (by simp only [simp_spine, hv216])
    (diagnose_step (s62_of_u44 hmulB.u44) u₃ u₄ hu₄)]


  -- `%219`/`%220`: `x_0a != x_mod_2a`, widened to the all-lanes mask `%230`
  -- turns into eight `i1`s
  denote_step_all v 220
  replace hv219 : v219 = .value (if diagnose
      (R43x6.extractLimbs (foldVec (mulVec xa t3a))) = sgnA then 1 else 0) := by
    simp only [hv219, Expr.denoteOp1, Expr.denoteOpPure]
    simp_peephole
    simp only [HVector.head, simp_spine, inp.s54]
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp']
    split <;> rename_i hc
    · simp [hc]
    · rw [beq_eq_false_iff_ne.mpr hc]; rfl
  replace hv220 : v220 = .value (if diagnose
      (R43x6.extractLimbs (foldVec (mulVec xa t3a))) = sgnA then 255#8 else 0#8) := by
    simp only [hv220, hv219, Expr.denoteOp1, Expr.denoteOpPure]
    simp_peephole
    simp only [HVector.head, simp_spine]
    split <;> rfl

  -- `%221`-`%229`: `fd_r43x6_neg( xa )` -- the subtract from `p` and the signed
  -- fold, as `Proof/Sub.lean` states the nine of them
  denote_step_reduce v 229 only [simp_spine, env.c18, hv211, env.c32, env.c33, env.c25,
    env.czero, zeroVec_eq, env.c23, env.c22, env.c21]
  refine name_of (negVec (foldVec (mulVec xa t3a))) fun nxa hnxa => ?_
  replace hv229 : v229 = nxa.map PoisonOr.value := by
    rw [hnxa]; exact denote_negVec hv221 hv222 hv223 hv224 hv225 hv226 hv227 hv228 hv229
  denote_clear v 221 228

  -- `%230`/`%231`: the sign fixup, `xa = fd_r43x6_if( x_0a != x_mod_2a,
  -- fd_r43x6_neg( xa ), xa )`. `%220` is all-ones exactly when the two agree,
  -- and then the select keeps `%211`.
  denote_step_all v 231
  refine name_of (if diagnose (R43x6.extractLimbs (foldVec (mulVec xa t3a))) = sgnA
      then foldVec (mulVec xa t3a) else nxa) fun xa' hxa' => ?_
  replace hv231 : v231 = xa'.map PoisonOr.value := by
    rw [hxa']
    simp only [hv231, hv230, hv229, hv211, Expr.denoteOp1, Expr.denoteOpPure]
    simp_peephole
    simp only [HVector.head, simp_spine, hv220]
    -- `exact`, not `simp`: the `Decidable` instance the block carries is not
    -- the one `simp` would synthesise, and `exact` unifies through it
    exact vselect_mask8 _ _ _
  denote_clear v 230 230

  -- `%232`-`%244`: the `b` twin of `%219`-`%231`, `%218`/`%56`/`%216` for
  -- `%217`/`%54`/`%211`
  denote_step_all v 233
  replace hv232 : v232 = .value (if diagnose
      (R43x6.extractLimbs (foldVec (mulVec xb t3b))) = sgnB then 1 else 0) := by
    simp only [hv232, Expr.denoteOp1, Expr.denoteOpPure]
    simp_peephole
    simp only [HVector.head, simp_spine, inp.s56]
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp']
    split <;> rename_i hc
    · simp [hc]
    · rw [beq_eq_false_iff_ne.mpr hc]; rfl
  replace hv233 : v233 = .value (if diagnose
      (R43x6.extractLimbs (foldVec (mulVec xb t3b))) = sgnB then 255#8 else 0#8) := by
    simp only [hv233, hv232, Expr.denoteOp1, Expr.denoteOpPure]
    simp_peephole
    simp only [HVector.head, simp_spine]
    split <;> rfl
  denote_step_reduce v 242 only [simp_spine, env.c18, hv216, env.c32, env.c33, env.c25,
    env.czero, zeroVec_eq, env.c23, env.c22, env.c21]
  refine name_of (negVec (foldVec (mulVec xb t3b))) fun nxb hnxb => ?_
  replace hv242 : v242 = nxb.map PoisonOr.value := by
    rw [hnxb]; exact denote_negVec hv234 hv235 hv236 hv237 hv238 hv239 hv240 hv241 hv242
  denote_clear v 234 241
  denote_step_all v 244
  refine name_of (if diagnose (R43x6.extractLimbs (foldVec (mulVec xb t3b))) = sgnB
      then foldVec (mulVec xb t3b) else nxb) fun xb' hxb' => ?_
  replace hv244 : v244 = xb'.map PoisonOr.value := by
    rw [hxb']
    simp only [hv244, hv243, hv242, hv216, Expr.denoteOp1, Expr.denoteOpPure]
    simp_peephole
    simp only [HVector.head, simp_spine, hv233]
    exact vselect_mask8 _ _ _
  denote_clear v 243 243

  -- what the sign fixup left, in the form the last two kernels take
  have hfA : ∀ k, 0 ≤ R43x6.extractLimbs (foldVec (mulVec xa t3a)) k
      ∧ R43x6.extractLimbs (foldVec (mulVec xa t3a)) k < 2 ^ 44 := by
    intro k
    have h1 := hmulA.u44.1 k; have h2 := hmulA.u44.2 k
    simp only [R43x6.toInts_take] at h1 h2
    omega
  have hfB : ∀ k, 0 ≤ R43x6.extractLimbs (foldVec (mulVec xb t3b)) k
      ∧ R43x6.extractLimbs (foldVec (mulVec xb t3b)) k < 2 ^ 44 := by
    intro k
    have h1 := hmulB.u44.1 k; have h2 := hmulB.u44.2 k
    simp only [R43x6.toInts_take] at h1 h2
    omega
  have hxa'B : ∀ k, 0 ≤ R43x6.extractLimbs xa' k ∧ R43x6.extractLimbs xa' k < 2 ^ 44 := by
    rw [hxa']; split
    · exact hfA
    · rw [hnxa]; exact extractLimbs_negVec hfA
  have hxb'B : ∀ k, 0 ≤ R43x6.extractLimbs xb' k ∧ R43x6.extractLimbs xb' k < 2 ^ 44 := by
    rw [hxb']; split
    · exact hfB
    · rw [hnxb]; exact extractLimbs_negVec hfB
  have hxa'6 : xa'[6] = 0 := by
    rw [hxa']; split
    · exact hmulA.z6
    · rw [hnxa]; exact negVec_six _
  have hxa'7 : xa'[7] = 0 := by
    rw [hxa']; split
    · exact hmulA.z7
    · rw [hnxa]; exact negVec_seven _
  have hxb'6 : xb'[6] = 0 := by
    rw [hxb']; split
    · exact hmulB.z6
    · rw [hnxb]; exact negVec_six _
  have hxb'7 : xb'[7] = 0 := by
    rw [hxb']; split
    · exact hmulB.z7
    · rw [hnxb]; exact negVec_seven _
  have hxa'U : R43x6.U47 (xa'.take R43x6.limbCount) := u47_take_of_bounds hxa'B
  have hxb'U : R43x6.U47 (xb'.take R43x6.limbCount) := u47_take_of_bounds hxb'B
  have hyaU47 : R43x6.U47 (ya.take R43x6.limbCount) := u47_take_of_unpacked hyaU
  have hybU47 : R43x6.U47 (yb.take R43x6.limbCount) := u47_take_of_unpacked hybU

  -- `%245`-`%254`: `FD_R43X6_MUL2_INL( xya, xa,ya, xyb, xb,yb )` -- the `T`
  -- coordinate, `%207`-`%216`'s shape one more time
  refine name_of (u₄.popFrame u₄.mem) fun u₅ hu₅ => ?_
  rw [BlockCom.run_bind_denote_call_cfg_of_value (argTys := [V8, V8])
    (by simp only [simp_spine, hv231, inp.y60])
    (mul_step_of_take hxa'U hxa'6 hxa'7 hyaU47 hya6 hya7 u₄ u₅ hu₅)]
  denote_step_reduce v 249 only [simp_spine, env.c32, env.c33, env.c27, env.c34] fold
  fold_unsigned hv249, (mulVec xa' ya), (limbNat_mul_lt hxa'U hyaU47)
  -- `xya`, as the C names it: the transpose reads four of its lanes and the
  -- term is large, so it goes in as an `fvar`
  refine name_of (foldVec (mulVec xa' ya)) fun xya hxya => ?_
  rw [← hxya] at hv249
  denote_clear v 246 248
  have hxyA : MulInl xa' ya (foldVec (mulVec xa' ya)) := mul_inl hxa'U hyaU47
  refine name_of (u₅.popFrame u₅.mem) fun u₆ hu₆ => ?_
  rw [BlockCom.run_bind_denote_call_cfg_of_value (argTys := [V8, V8])
    (by simp only [simp_spine, hv244, inp.y62])
    (mul_step_of_take hxb'U hxb'6 hxb'7 hybU47 hyb6 hyb7 u₅ u₆ hu₆)]
  denote_step_reduce v 254 only [simp_spine, env.c32, env.c33, env.c27, env.c34] fold
  fold_unsigned hv254, (mulVec xb' yb), (limbNat_mul_lt hxb'U hybU47)
  refine name_of (foldVec (mulVec xb' yb)) fun xyb hxyb => ?_
  rw [← hxyb] at hv254
  denote_clear v 251 253
  have hxyB : MulInl xb' yb (foldVec (mulVec xb' yb)) := mul_inl hxb'U hybU47

  -- `%255`-`%263`: `FD_R43X6_QUAD_PACK( *_Pa, xa,ya,one,xya )`
  denote_step_reduce v 263 only [simp_spine, hv231, env.c19, env.c12, inp.y60, hv249, env.c11]
  refine name_of (packQuad xa' ya oneVec xya) fun qa hqa => ?_
  replace hv263 : v263 = qa.v03.map PoisonOr.value := by
    rw [hqa]; exact denote_quadPack_v03 hv255 hv256 hv257 hv258 hv259 hv262 hv263

  -- the six calls popped six frames and wrote nothing, so the caller's
  -- out-vectors read in `u₆` as they did on entry
  have e1 : s ≈ u₁ := hu₁ ▸ hs.popFrame_equiv
  have hw1 : u₁.WF := hs.of_equiv e1
  have e2 : u₁ ≈ u₂ := hu₂ ▸ hw1.popFrame_equiv
  have hw2 : u₂.WF := hw1.of_equiv e2
  have e3 : u₂ ≈ u₃ := hu₃ ▸ hw2.popFrame_equiv
  have hw3 : u₃.WF := hw2.of_equiv e3
  have e4 : u₃ ≈ u₄ := hu₄ ▸ hw3.popFrame_equiv
  have hw4 : u₄.WF := hw3.of_equiv e4
  have e5 : u₄ ≈ u₅ := hu₅ ▸ hw4.popFrame_equiv
  have hw5 : u₅.WF := hw4.of_equiv e5
  have e6 : u₅ ≈ u₆ := hu₆ ▸ hw5.popFrame_equiv
  have e : s ≈ u₆ := e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))
  have fa03 : Fits u₆.mem a03 512 := fits_of_live?_eq (e.live a03.id).symm pa03.1
  have fa14 : Fits u₆.mem a14 512 := fits_of_live?_eq (e.live a14.id).symm pa14.1
  have fa25 : Fits u₆.mem a25 512 := fits_of_live?_eq (e.live a25.id).symm pa25.1

  -- the three `a` stores, `%264`/`%265` between them
  refine name_of ({ u₆ with mem := u₆.mem.splice a03 (vecBV qa.v03) }) fun m₁ hm₁ => ?_
  peel_store_amb qa.v03, a03, fa03, u₆ as m₁ := hm₁ with
    simp_spine, hv263, env.va03
  denote_step_all v 264
  replace hv264 : v264 = qa.v14.map PoisonOr.value := by
    rw [hqa]; exact denote_quadPack_v14 hv255 hv256 hv259 hv260 hv264
  have fa14' : Fits m₁.mem a14 512 := hm₁ ▸ fits_splice fa14
  refine name_of ({ m₁ with mem := m₁.mem.splice a14 (vecBV qa.v14) }) fun m₂ hm₂ => ?_
  peel_store_amb qa.v14, a14, fa14', m₁ as m₂ := hm₂ with
    simp_spine, hv264, env.va14
  denote_step_all v 265
  replace hv265 : v265 = qa.v25.map PoisonOr.value := by
    rw [hqa]; exact denote_quadPack_v25 hv255 hv256 hv257 hv258 hv260 hv261 hv265
  have fa25' : Fits m₂.mem a25 512 := hm₂ ▸ fits_splice (hm₁ ▸ fits_splice fa25)
  refine name_of ({ m₂ with mem := m₂.mem.splice a25 (vecBV qa.v25) }) fun m₃ hm₃ => ?_
  peel_store_amb qa.v25, a25, fa25', m₂ as m₃ := hm₃ with
    simp_spine, hv265, env.va25

  -- `%266`-`%276`: the `b` twin, `xb'`/`yb`/`xyb` for `xa'`/`ya`/`xya` and
  -- `%arg4`/`%arg5`/`%arg6` for `%arg0`/`%arg1`/`%arg2`
  denote_step_reduce v 274 only [simp_spine, hv244, env.c19, env.c12, inp.y62, hv254, env.c11]
  refine name_of (packQuad xb' yb oneVec xyb) fun qb hqb => ?_
  replace hv274 : v274 = qb.v03.map PoisonOr.value := by
    rw [hqb]; exact denote_quadPack_v03 hv266 hv267 hv268 hv269 hv270 hv273 hv274
  have fb03 : Fits m₃.mem b03 512 :=
    hm₃ ▸ fits_splice (hm₂ ▸ fits_splice (hm₁ ▸ fits_splice
      (fits_of_live?_eq (e.live b03.id).symm pb03.1)))
  have fb14 : Fits m₃.mem b14 512 :=
    hm₃ ▸ fits_splice (hm₂ ▸ fits_splice (hm₁ ▸ fits_splice
      (fits_of_live?_eq (e.live b14.id).symm pb14.1)))
  have fb25 : Fits m₃.mem b25 512 :=
    hm₃ ▸ fits_splice (hm₂ ▸ fits_splice (hm₁ ▸ fits_splice
      (fits_of_live?_eq (e.live b25.id).symm pb25.1)))
  refine name_of ({ m₃ with mem := m₃.mem.splice b03 (vecBV qb.v03) }) fun m₄ hm₄ => ?_
  peel_store_amb qb.v03, b03, fb03, m₃ as m₄ := hm₄ with
    simp_spine, hv274, env.vb03
  denote_step_all v 275
  replace hv275 : v275 = qb.v14.map PoisonOr.value := by
    rw [hqb]; exact denote_quadPack_v14 hv266 hv267 hv270 hv271 hv275
  have fb14' : Fits m₄.mem b14 512 := hm₄ ▸ fits_splice fb14
  refine name_of ({ m₄ with mem := m₄.mem.splice b14 (vecBV qb.v14) }) fun m₅ hm₅ => ?_
  peel_store_amb qb.v14, b14, fb14', m₄ as m₅ := hm₅ with
    simp_spine, hv275, env.vb14
  denote_step_all v 276
  replace hv276 : v276 = qb.v25.map PoisonOr.value := by
    rw [hqb]; exact denote_quadPack_v25 hv266 hv267 hv268 hv269 hv271 hv272 hv276
  have fb25' : Fits m₅.mem b25 512 := hm₅ ▸ fits_splice (hm₄ ▸ fits_splice fb25)
  refine name_of ({ m₅ with mem := m₅.mem.splice b25 (vecBV qb.v25) }) fun m₆ hm₆ => ?_
  peel_store_amb qb.v25, b25, fb25', m₅ as m₆ := hm₆ with
    simp_spine, hv276, env.vb25

  -- What the six reloads at `%277`-`%306` will read. Each looks past the
  -- splices that came after its own, which is what `SixDistinct` is for; the
  -- last one, `b25`, has nothing after it.
  have rv03a : readVec? a03 m₆.mem = some qa.v03 := by
    rw [hm₆, readVec?_splice_ne hne.b25_a03, hm₅, readVec?_splice_ne hne.b14_a03,
      hm₄, readVec?_splice_ne hne.b03_a03, hm₃, readVec?_splice_ne hne.a25_a03,
      hm₂, readVec?_splice_ne hne.a14_a03, hm₁]
    exact readVec?_splice_self _ ⟨fa03, pa03.2⟩
  have rv14a : readVec? a14 m₆.mem = some qa.v14 := by
    rw [hm₆, readVec?_splice_ne hne.b25_a14, hm₅, readVec?_splice_ne hne.b14_a14,
      hm₄, readVec?_splice_ne hne.b03_a14, hm₃, readVec?_splice_ne hne.a25_a14, hm₂]
    exact readVec?_splice_self _ ⟨fa14', pa14.2⟩
  have rv25a : readVec? a25 m₆.mem = some qa.v25 := by
    rw [hm₆, readVec?_splice_ne hne.b25_a25, hm₅, readVec?_splice_ne hne.b14_a25,
      hm₄, readVec?_splice_ne hne.b03_a25, hm₃]
    exact readVec?_splice_self _ ⟨fa25', pa25.2⟩
  have rv03b : readVec? b03 m₆.mem = some qb.v03 := by
    rw [hm₆, readVec?_splice_ne hne.b25_b03, hm₅, readVec?_splice_ne hne.b14_b03, hm₄]
    exact readVec?_splice_self _ ⟨fb03, pb03.2⟩
  have rv14b : readVec? b14 m₆.mem = some qb.v14 := by
    rw [hm₆, readVec?_splice_ne hne.b25_b14, hm₅]
    exact readVec?_splice_self _ ⟨fb14', pb14.2⟩
  have rv25b : readVec? b25 m₆.mem = some qb.v25 := by
    rw [hm₆]
    exact readVec?_splice_self _ ⟨fb25', pb25.2⟩

  -- the six out-vectors, still live at `m₆`
  have F03a : Fits m₆.mem a03 512 := hm₆ ▸ fits_splice (hm₅ ▸ fits_splice
    (hm₄ ▸ fits_splice (hm₃ ▸ fits_splice (hm₂ ▸ fits_splice (hm₁ ▸ fits_splice fa03)))))
  have F14a : Fits m₆.mem a14 512 := hm₆ ▸ fits_splice (hm₅ ▸ fits_splice
    (hm₄ ▸ fits_splice (hm₃ ▸ fits_splice (hm₂ ▸ fits_splice fa14'))))
  have F25a : Fits m₆.mem a25 512 := hm₆ ▸ fits_splice (hm₅ ▸ fits_splice
    (hm₄ ▸ fits_splice (hm₃ ▸ fits_splice fa25')))
  have P03a : IsVecPtr m₆.mem a03 := ⟨F03a, pa03.2⟩
  have P14a : IsVecPtr m₆.mem a14 := ⟨F14a, pa14.2⟩
  have P25a : IsVecPtr m₆.mem a25 := ⟨F25a, pa25.2⟩

  -- `%277`-`%286`: `FD_R43X6_QUAD_FOLD_UNSIGNED( *_Pa, *_Pa )`, first third
  peel_load_vec_amb qa.v03, a03, P03a, (readVec_eq_of rv03a), m₆ with
    simp_spine, env.va03
  denote_step_reduce v 278 only [simp_spine, env.c10]
  peel_load_vec_amb qa.v14, a14, P14a, (readVec_eq_of rv14a), m₆ with
    simp_spine, env.va14
  denote_step_reduce v 280 only [simp_spine, env.c10]
  peel_load_vec_amb qa.v25, a25, P25a, (readVec_eq_of rv25a), m₆ with
    simp_spine, env.va25
  denote_step_reduce v 286 only [simp_spine, env.c9, env.c44, env.c1]
  replace hv286 : v286 = (foldQuad qa).v03.map PoisonOr.value :=
    denote_quadFold_v03 hv282 hv283 hv284 hv285 hv286

  -- `%286`'s store, then `%287`-`%292`: the `14` and `25` thirds. Each
  -- reloads its own vector, which the store before it did not touch.
  refine name_of ({ m₆ with mem := m₆.mem.splice a03 (vecBV (foldQuad qa).v03) })
    fun m₇ hm₇ => ?_
  peel_store_amb (foldQuad qa).v03, a03, F03a, m₆ as m₇ := hm₇ with
    simp_spine, hv286, env.va03
  have F14a₇ : Fits m₇.mem a14 512 := hm₇ ▸ fits_splice F14a
  have P14a' : IsVecPtr m₇.mem a14 := ⟨F14a₇, pa14.2⟩
  have rv14a' : readVec? a14 m₇.mem = some qa.v14 := by
    rw [hm₇, readVec?_splice_ne hne.a14_a03.symm]; exact rv14a
  peel_load_vec_amb qa.v14, a14, P14a', (readVec_eq_of rv14a'), m₇ with
    simp_spine, env.va14
  denote_step_reduce v 289 only [simp_spine, env.c1]
  replace hv289 : v289 = (foldQuad qa).v14.map PoisonOr.value :=
    denote_quadFold_v14 hv278 hv288 hv289
  refine name_of ({ m₇ with mem := m₇.mem.splice a14 (vecBV (foldQuad qa).v14) })
    fun m₈ hm₈ => ?_
  peel_store_amb (foldQuad qa).v14, a14, F14a₇, m₇ as m₈ := hm₈ with
    simp_spine, hv289, env.va14
  have F25a₈ : Fits m₈.mem a25 512 := hm₈ ▸ fits_splice (hm₇ ▸ fits_splice F25a)
  have P25a' : IsVecPtr m₈.mem a25 := ⟨F25a₈, pa25.2⟩
  have rv25a' : readVec? a25 m₈.mem = some qa.v25 := by
    rw [hm₈, readVec?_splice_ne hne.a25_a14.symm, hm₇,
      readVec?_splice_ne hne.a25_a03.symm]
    exact rv25a
  peel_load_vec_amb qa.v25, a25, P25a', (readVec_eq_of rv25a'), m₈ with
    simp_spine, env.va25
  denote_step_reduce v 292 only [simp_spine, env.c0]
  replace hv292 : v292 = (foldQuad qa).v25.map PoisonOr.value :=
    denote_quadFold_v25 hv280 hv291 hv292
  refine name_of ({ m₈ with mem := m₈.mem.splice a25 (vecBV (foldQuad qa).v25) })
    fun m₉ hm₉ => ?_
  peel_store_amb (foldQuad qa).v25, a25, F25a₈, m₈ as m₉ := hm₉ with
    simp_spine, hv292, env.va25

  -- `%293`-`%308`: the `b` twin. Its three reloads have to look past the
  -- three `a` stores as well, which is the second place `SixDistinct` pays.
  have F03b : Fits m₆.mem b03 512 :=
    hm₆ ▸ fits_splice (hm₅ ▸ fits_splice (hm₄ ▸ fits_splice fb03))
  have F14b : Fits m₆.mem b14 512 := hm₆ ▸ fits_splice (hm₅ ▸ fits_splice fb14')
  have F25b : Fits m₆.mem b25 512 := hm₆ ▸ fits_splice fb25'
  have F03b₉ : Fits m₉.mem b03 512 :=
    hm₉ ▸ fits_splice (hm₈ ▸ fits_splice (hm₇ ▸ fits_splice F03b))
  have F14b₉ : Fits m₉.mem b14 512 :=
    hm₉ ▸ fits_splice (hm₈ ▸ fits_splice (hm₇ ▸ fits_splice F14b))
  have F25b₉ : Fits m₉.mem b25 512 :=
    hm₉ ▸ fits_splice (hm₈ ▸ fits_splice (hm₇ ▸ fits_splice F25b))
  have rv03b' : readVec? b03 m₉.mem = some qb.v03 := by
    rw [hm₉, readVec?_splice_ne hne.b03_a25.symm, hm₈,
      readVec?_splice_ne hne.b03_a14.symm, hm₇, readVec?_splice_ne hne.b03_a03.symm]
    exact rv03b
  have rv14b' : readVec? b14 m₉.mem = some qb.v14 := by
    rw [hm₉, readVec?_splice_ne hne.b14_a25.symm, hm₈,
      readVec?_splice_ne hne.b14_a14.symm, hm₇, readVec?_splice_ne hne.b14_a03.symm]
    exact rv14b
  have rv25b' : readVec? b25 m₉.mem = some qb.v25 := by
    rw [hm₉, readVec?_splice_ne hne.b25_a25.symm, hm₈,
      readVec?_splice_ne hne.b25_a14.symm, hm₇, readVec?_splice_ne hne.b25_a03.symm]
    exact rv25b
  peel_load_vec_amb qb.v03, b03, (⟨F03b₉, pb03.2⟩ : IsVecPtr m₉.mem b03),
    (readVec_eq_of rv03b'), m₉ with simp_spine, env.vb03
  denote_step_reduce v 294 only [simp_spine, env.c10]
  peel_load_vec_amb qb.v14, b14, (⟨F14b₉, pb14.2⟩ : IsVecPtr m₉.mem b14),
    (readVec_eq_of rv14b'), m₉ with simp_spine, env.vb14
  denote_step_reduce v 296 only [simp_spine, env.c10]
  peel_load_vec_amb qb.v25, b25, (⟨F25b₉, pb25.2⟩ : IsVecPtr m₉.mem b25),
    (readVec_eq_of rv25b'), m₉ with simp_spine, env.vb25
  denote_step_reduce v 302 only [simp_spine, env.c9, env.c44, env.c1]
  replace hv302 : v302 = (foldQuad qb).v03.map PoisonOr.value :=
    denote_quadFold_v03 hv298 hv299 hv300 hv301 hv302
  refine name_of ({ m₉ with mem := m₉.mem.splice b03 (vecBV (foldQuad qb).v03) })
    fun m₁₀ hm₁₀ => ?_
  peel_store_amb (foldQuad qb).v03, b03, F03b₉, m₉ as m₁₀ := hm₁₀ with
    simp_spine, hv302, env.vb03
  have F14b₁₀ : Fits m₁₀.mem b14 512 := hm₁₀ ▸ fits_splice F14b₉
  have rv14b'' : readVec? b14 m₁₀.mem = some qb.v14 := by
    rw [hm₁₀, readVec?_splice_ne hne.b14_b03.symm]; exact rv14b'
  peel_load_vec_amb qb.v14, b14, (⟨F14b₁₀, pb14.2⟩ : IsVecPtr m₁₀.mem b14),
    (readVec_eq_of rv14b''), m₁₀ with simp_spine, env.vb14
  denote_step_reduce v 305 only [simp_spine, env.c1]
  replace hv305 : v305 = (foldQuad qb).v14.map PoisonOr.value :=
    denote_quadFold_v14 hv294 hv304 hv305
  refine name_of ({ m₁₀ with mem := m₁₀.mem.splice b14 (vecBV (foldQuad qb).v14) })
    fun m₁₁ hm₁₁ => ?_
  peel_store_amb (foldQuad qb).v14, b14, F14b₁₀, m₁₀ as m₁₁ := hm₁₁ with
    simp_spine, hv305, env.vb14
  have F25b₁₁ : Fits m₁₁.mem b25 512 := hm₁₁ ▸ fits_splice (hm₁₀ ▸ fits_splice F25b₉)
  have rv25b'' : readVec? b25 m₁₁.mem = some qb.v25 := by
    rw [hm₁₁, readVec?_splice_ne hne.b25_b14.symm, hm₁₀,
      readVec?_splice_ne hne.b25_b03.symm]
    exact rv25b'
  peel_load_vec_amb qb.v25, b25, (⟨F25b₁₁, pb25.2⟩ : IsVecPtr m₁₁.mem b25),
    (readVec_eq_of rv25b''), m₁₁ with simp_spine, env.vb25
  denote_step_reduce v 308 only [simp_spine, env.c0]
  replace hv308 : v308 = (foldQuad qb).v25.map PoisonOr.value :=
    denote_quadFold_v25 hv296 hv307 hv308

  -- `br (%308, %17) -> ^bb5`: the six out-vectors are the two folded QUADs,
  -- and `%308` -- `b`'s `25`, the one this block does not store -- rides the
  -- φ to `^bb5`, where `bb5_run` writes it through `%arg6`.
  refine ⟨(foldQuad qa).v03, (foldQuad qa).v14, (foldQuad qa).v25,
          (foldQuad qb).v03, (foldQuad qb).v14, (foldQuad qb).v25, qb.v25,
          m₁₁, ?_, ?_, ?_, ?_, F25b₁₁⟩
  · -- a *narrow* set: `simp_denote`/`simp_sllvm` on a goal carrying `m₁₁`'s
    -- eleven nested splices runs out of steps
    simp only [BlockCom.denote_term, Terminator.denote_br, Target.denote_mk,
      HVector.map, simp_spine, hv308, env.c17]
    rfl
  · -- the memory: `m₁₁`'s eleven splices, as the six the statement names
    -- the chain starts at `u₆` and the statement at `s`; `e` is what says the
    -- six calls between them moved no memory
    exact quadStores_equiv hne.a14_a03 hne.a25_a03 hne.b03_a03 hne.b14_a03 hne.b25_a03
      hne.a25_a14 hne.b03_a14 hne.b14_a14 hne.b25_a14 hne.b03_a25 hne.b14_a25 hne.b25_a25
      hne.b14_b03 hne.b25_b03 hne.b25_b14
      hm₁ hm₂ hm₃ hm₄ hm₅ hm₆ hm₇ hm₈ hm₉ hm₁₀ hm₁₁ e
  · -- `Decodes ua ⟨…⟩`: that the `a` QUAD holds the decoded point, which is
    -- `decodes_side` on everything the walk named
    have hxa'' : xa' = if diagnose (R43x6.extractLimbs (foldVec (mulVec xa t3a))) = sgnA
        then foldVec (mulVec xa t3a) else negVec (foldVec (mulVec xa t3a)) := by
      rw [hxa', hnxa]
    rw [hqa, hxya]
    exact decodes_side hya hyaU hsgnA ht3a h190 hrootA hmulA hfA hxa'' hxyA
  · -- ... and its `b` twin
    have hxb'' : xb' = if diagnose (R43x6.extractLimbs (foldVec (mulVec xb t3b))) = sgnB
        then foldVec (mulVec xb t3b) else negVec (foldVec (mulVec xb t3b)) := by
      rw [hxb', hnxb]
    rw [hqb, hxyb]
    exact decodes_side hyb hybU hsgnB ht3b h191 hrootB hmulB hfB hxb'' hxyB

/-- **`^bb5`'s store, folded into `^bb2`'s six splices.** The last of the six
is written twice -- once by the transpose, once by the reduce that `^bb5`
carries -- and `spliceBits_spliceBits_self` is what makes the first invisible.

Stated over `hmem`'s components rather than composed out of `splice_equiv`:
the composition has to unify a structure update against a six-splice chain,
and the elaborator walks it. -/
private theorem lastStore_equiv {s s' : GlobalState} {m : MemoryState} {q : Pointer}
    {w : Nat} {x y : BitVec w}
    (h : s' ≈ ({ s with mem := m.splice q x } : GlobalState)) :
    ({ s' with mem := s'.mem.splice q y } : GlobalState)
      ≈ ({ s with mem := m.splice q y } : GlobalState) := by
  refine ⟨h.1, h.globals, fun k => ?_⟩
  by_cases hq : q.id = k
  · subst hq
    have hk := h.live q.id
    cases hb : m.live? q.id with
    | none =>
      rw [splicedDead hb] at hk
      rw [splicedDead hk, splicedDead hb]
    | some b =>
      rw [splicedLive m q b hb x] at hk
      rw [splicedLive _ q _ hk y, splicedLive m q b hb y, spliceBits_spliceBits_self]
  · have hk := h.live k
    simp only [live?_splice_ne hq] at hk ⊢
    exact hk

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
/-- **`^bb2` and `^bb5` together**: the success path as one run equation, in
the shape `fd_r43x6_ge_decode2_spec` asks for. `^bb5`'s store to `%arg6` is
what turns `bb2_run`'s `vpre` into the sixth out-vector.

Continuation form: the caller's valuation is pinned by the run equation, not
by the hypotheses, so the six vectors have to be handed over rather than
existentially quantified. -/
theorem bb2_full {V : fd_r43x6_ge_decode2.Γout.Valuation}
    {a03 a14 a25 b03 b14 b25 : Pointer} (env : EntryEnv V a03 a14 a25 b03 b14 b25)
    {xa xb ya yb : Vector (BitVec 64) 8} {sgnA sgnB t1nza t1nzb : BitVec 32}
    (inp : Bb2In V xa xb ya yb sgnA sgnB t1nza t1nzb)
    -- what those eight values are, in the field
    {ua ub : Vector (BitVec 64) 4}
    (hya : (R43x6.decode' ya : ZMod p) = wvY ua)
    (hyb : (R43x6.decode' yb : ZMod p) = wvY ub)
    (hsgnA : sgnA = if wvSign ua then 1 else 0)
    (hsgnB : sgnB = if wvSign ub then 1 else 0)
    (h190 : t1nza = 0 ↔ vecValue xa ^ 2 * (d * wvY ua ^ 2 + 1) = wvY ua ^ 2 - 1)
    (h191 : t1nzb = 0 ↔ vecValue xb ^ 2 * (d * wvY ub ^ 2 + 1) = wvY ub ^ 2 - 1)
    -- reaching `^bb2` means one of each candidate's two roots worked: `^bb0`
    -- made the test for `a` and `^bb1` for `b`. The second disjunct is the
    -- `sqrt(-1)` case, and is what makes `%202`/`%206`'s select a root.
    (hrootA : t1nza = 0 ∨ vecValue xa ^ 2 * (d * wvY ua ^ 2 + 1) = -(wvY ua ^ 2 - 1))
    (hrootB : t1nzb = 0 ∨ vecValue xb ^ 2 * (d * wvY ub ^ 2 + 1) = -(wvY ub ^ 2 - 1))
    -- `fd_r43x6_is_nonzero` returns `0` or `1`, and the `nsw` on `%200`/`%204`
    -- needs to know it: the decrement poisons at `-2 ^ 7` and nowhere else
    (ht1nza : t1nza = 0 ∨ t1nza = 1) (ht1nzb : t1nzb = 0 ∨ t1nzb = 1)
    -- the kernels' input contracts on what `^bb0` folded and unpacked
    (hxaU : R43x6.U44 (xa.take R43x6.limbCount)) (hxa6 : xa[6] = 0) (hxa7 : xa[7] = 0)
    (hxbU : R43x6.U44 (xb.take R43x6.limbCount)) (hxb6 : xb[6] = 0) (hxb7 : xb[7] = 0)
    (hyaU : R43x6.Unpacked ya) (hya6 : ya[6] = 0) (hya7 : ya[7] = 0)
    (hybU : R43x6.Unpacked yb) (hyb6 : yb[6] = 0) (hyb7 : yb[7] = 0)
    -- the six out-vectors
    {s : GlobalState} (hs : s.WF)
    (pa03 : IsVecPtr s.mem a03) (pa14 : IsVecPtr s.mem a14) (pa25 : IsVecPtr s.mem a25)
    (pb03 : IsVecPtr s.mem b03) (pb14 : IsVecPtr s.mem b14) (pb25 : IsVecPtr s.mem b25)
    (hne : SixDistinct a03 a14 a25 b03 b14 b25) {P : Prop}
    (k : ∀ (va03 va14 va25 vb03 vb14 vb25 : Vector (BitVec 64) 8) (s' : GlobalState),
      StateT.run (fd_r43x6_ge_decode2.blocks.run V bb2) s
          = .value ([(.value 0#32 : LLVM.IntW 32)]ₕ, s') →
      s' ≈ ({ s with mem :=
          ((((((s.mem.splice a03 (vecBV va03)).splice a14 (vecBV va14)).splice
              a25 (vecBV va25)).splice b03 (vecBV vb03)).splice
              b14 (vecBV vb14)).splice b25 (vecBV vb25)) }
          : GlobalState) →
      Decodes ua ⟨va03, va14, va25⟩ → Decodes ub ⟨vb03, vb14, vb25⟩ → P) : P := by
  obtain ⟨va03, va14, va25, vb03, vb14, vb25, vpre, s', hrun, hmem, hda, hdb, hb25'⟩ :=
    bb2_run env inp hya hyb hsgnA hsgnB h190 h191 hrootA hrootB ht1nza ht1nzb
      hxaU hxa6 hxa7 hxbU hxb6 hxb7 hyaU hya6 hya7 hybU hyb6 hyb7 hs
      pa03 pa14 pa25 pb03 pb14 pb25 hne
  refine k va03 va14 va25 vb03 vb14 vb25
    ({ s' with mem := s'.mem.splice b25 (vecBV vb25) } : GlobalState) ?_ ?_ hda hdb
  · rw [hrun]
    exact bb5_run env vb25 (.value 0#32) hb25'
  · exact lastStore_equiv hmem



/-! ### What the caller needs of the six splices

`fd_r43x6_ge_decode2_conforms` states its memory in one fixed order, and the
failure paths write in another; with the six pointers distinct the two agree
at every block. -/

/-- A splice is invisible to a `live?` equation at another block, and
transports it at its own. -/
theorem live?_splice_congr' {m₁ m₂ : MemoryState} {p : Pointer} {w : Nat} {x : BitVec w}
    {c : BlockId} (h : m₁.live? c = m₂.live? c) :
    (m₁.splice p x).live? c = (m₂.splice p x).live? c := by
  by_cases hc : p.id = c
  · subst hc; exact live?_splice_congr h
  · rw [live?_splice_ne hc, live?_splice_ne hc]; exact h

/-- **The failure paths' write order is the spec's**, up to `≈`. -/
theorem zeroOutMem_equiv {a03 a14 a25 b03 b14 b25 : Pointer}
    (hne : SixDistinct a03 a14 a25 b03 b14 b25) (s : GlobalState) :
    ({ s with mem := zeroOutMem s.mem a03 a14 a25 b03 b14 b25 } : GlobalState)
      ≈ ({ s with mem :=
          ((((((s.mem.splice a03 (vecBV zeroVec)).splice a14 (vecBV zeroVec)).splice
              a25 (vecBV zeroVec)).splice b03 (vecBV zeroVec)).splice
              b14 (vecBV zeroVec)).splice b25 (vecBV zeroVec)) } : GlobalState) := by
  refine ⟨rfl, rfl, fun k => ?_⟩
  simp only [zeroOutMem, live?_splice]
  by_cases ka : k = a03.id
  · subst ka
    simp [Ne.symm hne.a14_a03, Ne.symm hne.a25_a03, Ne.symm hne.b03_a03,
      Ne.symm hne.b14_a03, Ne.symm hne.b25_a03]
  by_cases kb : k = a14.id
  · subst kb
    simp [ka, Ne.symm hne.a25_a14, Ne.symm hne.b03_a14, Ne.symm hne.b14_a14,
      Ne.symm hne.b25_a14]
  by_cases kc : k = a25.id
  · subst kc
    simp [ka, kb, Ne.symm hne.b03_a25, Ne.symm hne.b14_a25, Ne.symm hne.b25_a25]
  by_cases kd : k = b03.id
  · subst kd
    simp [ka, kb, kc, Ne.symm hne.b14_b03, Ne.symm hne.b25_b03]
  by_cases ke : k = b14.id
  · subst ke
    simp [ka, kb, kc, kd, Ne.symm hne.b25_b14]
  by_cases kf : k = b25.id
  · subst kf
    simp [ka, kb, kc, kd, ke]
  simp [ka, kb, kc, kd, ke, kf]





/-- **The six splices as the caller sees them.** The region writes at a state
the prologue reached; the spec states the same six writes over the caller's
memory, and `popFrame` puts the frame back. `hc` is what says the six blocks
are the caller's own, which the frame left alone.

The write chain is named (`hM`) before `hmem` is projected: the projection of
a state literal against a six-splice memory is a `whnf` the elaborator walks
splice by splice, and it is superlinear -- two splices are instant, six are
minutes. -/
theorem outMem_popFrame_equiv {s st s₂ : GlobalState} {a03 a14 a25 b03 b14 b25 : Pointer}
    {va03 va14 va25 vb03 vb14 vb25 : Vector (BitVec 64) 8} (hs : s.WF)
    (hbelow : ∀ c : BlockId,
      (c = a03.id ∨ c = a14.id ∨ c = a25.id ∨ c = b03.id ∨ c = b14.id ∨ c = b25.id)
        → c.id < s.alloc.nextFreeBlock)
    (hc : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → st.mem.live? b = s.mem.live? b)
    (hmem : s₂ ≈ ({ st with mem :=
        ((((((st.mem.splice a03 (vecBV va03)).splice a14 (vecBV va14)).splice
            a25 (vecBV va25)).splice b03 (vecBV vb03)).splice
            b14 (vecBV vb14)).splice b25 (vecBV vb25)) } : GlobalState)) :
    s.popFrame s₂.mem
      ≈ ({ alloc := s.alloc,
           mem := ((((((s.mem.splice a03 (vecBV va03)).splice a14 (vecBV va14)).splice
             a25 (vecBV va25)).splice b03 (vecBV vb03)).splice
             b14 (vecBV vb14)).splice b25 (vecBV vb25)),
           globals := s.globals } : GlobalState) := by
  obtain ⟨M, hM⟩ : ∃ M : MemoryState, ((((((st.mem.splice a03 (vecBV va03)).splice
      a14 (vecBV va14)).splice a25 (vecBV va25)).splice b03 (vecBV vb03)).splice
      b14 (vecBV vb14)).splice b25 (vecBV vb25)) = M := ⟨_, rfl⟩
  rw [hM] at hmem
  have hall : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock →
      s₂.mem.live? b
        = ((((((s.mem.splice a03 (vecBV va03)).splice a14 (vecBV va14)).splice
            a25 (vecBV va25)).splice b03 (vecBV vb03)).splice
            b14 (vecBV vb14)).splice b25 (vecBV vb25)).live? b := by
    intro b hb
    have h1 := live?_splice_congr' (c := b) (p := a03) (x := vecBV va03) (hc b hb)
    have h2 := live?_splice_congr' (c := b) (p := a14) (x := vecBV va14) h1
    have h3 := live?_splice_congr' (c := b) (p := a25) (x := vecBV va25) h2
    have h4 := live?_splice_congr' (c := b) (p := b03) (x := vecBV vb03) h3
    have h5 := live?_splice_congr' (c := b) (p := b14) (x := vecBV vb14) h4
    have h6 := live?_splice_congr' (c := b) (p := b25) (x := vecBV vb25) h5
    rw [hM] at h6
    exact (hmem.live b).trans h6
  have hoff : ∀ b : BlockId,
      ¬(b = a03.id ∨ b = a14.id ∨ b = a25.id ∨ b = b03.id ∨ b = b14.id ∨ b = b25.id) →
      ((((((s.mem.splice a03 (vecBV va03)).splice a14 (vecBV va14)).splice
          a25 (vecBV va25)).splice b03 (vecBV vb03)).splice
          b14 (vecBV vb14)).splice b25 (vecBV vb25)).live? b = s.mem.live? b := by
    intro b hw
    push_neg at hw
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hw
    rw [live?_splice_ne (Ne.symm n6), live?_splice_ne (Ne.symm n5),
      live?_splice_ne (Ne.symm n4), live?_splice_ne (Ne.symm n3),
      live?_splice_ne (Ne.symm n2), live?_splice_ne (Ne.symm n1)]
  exact popFrame_equiv_written
    (fun c => c = a03.id ∨ c = a14.id ∨ c = a25.id ∨ c = b03.id ∨ c = b14.id ∨ c = b25.id)
    hs hbelow (fun b hb hw => (hall b hb).trans (hoff b hw)) hoff
    (fun b hw => hall b (hbelow b hw))


end GeDecode2

end Firedancer.Avx512
