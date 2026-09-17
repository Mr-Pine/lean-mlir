/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Mlir.fd_ed25519_verify
import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_double_scalar_mul_base
import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_point_frombytes
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_verify
import SSA.Projects.Firedancer.Common.Spec.Scalar.fd_curve25519_scalar_reduce

/-!
# `fd_ed25519_verify` (ref)

RFC 8032 §5.1.7, cofactorless, with `verify_strict`'s small-order rejection:
`FD_ED25519_SUCCESS` iff `[S]B = R + [k]A` for `k` what `scalar_reduce` makes of the digest,
else the first failing check's code -- `FD_ED25519_ERR_SIG`, `_PUBKEY` or `_MSG`.

Decoding is `IsDecoding`'s: non-canonical `y` accepted, and `x = 0` with the
sign bit set too. `S ≥ ℓ` is rejected. Neither hash nor reduction is specified: the digest is
`ed25519Digest`, built from the caller's `fInit`/`fApp`/`fFini`, and the scalar is the `w` that
`scalar_reduce` makes of it (taken mod `2²⁵⁵`, as `double_scalar_mul_base` reads it). Runs in
which one of those calls does not return are not covered: they are the `none` cases.

Only `sha` is written, and only once every check before the hash has passed.
-/

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519 Common

/-- `V` is a point `bytes` names, as `IsDecoding` reads it. -/
def Encodes (bytes : BitVec 256) (V : Edwards.Point curve) : Prop :=
  V.y = decodeBytes bytes ∧ (V.x ≠ 0 → (V.x.val % 2 = 0 ↔ bytes[255] = false))

abbrev fd_ed25519_verify_spec (msg : Pointer) (sz : BitVec 64) (sig pk sha : Pointer)
    (s : GlobalState) (hmsg : Fits s.mem msg (sz.toNat * 8)) (hr : IsByteBufPtr s.mem sig)
    (hS : IsByteBufPtr s.mem (sig.withOffset 32)) (ha : IsByteBufPtr s.mem pk)
    (f : BitVec (64 * 8) → Option (Fin 4 → BitVec 64)) (kbits : BitVec (80 * 64))
    (fInit : Option LiveBlock → BitVec 64 → Option (Option LiveBlock))
    (fApp : Option LiveBlock → BitVec 64 → List (BitVec 8) → Option (Option LiveBlock))
    (fFini : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option (BitVec 512)) :
    Prop :=
  let invocation :=
    runFunction
      (fd_ed25519_verify.denote
        (Ctxt.Valuation.ofHVector [.value sha, .value pk, .value sig, .value sz, .value msg]ₕ))
  let result := StateT.run invocation s
  let r := readBuf hr
  let S := (readBuf hS).toNat
  let a := readBuf ha
  let digest :=
    ed25519Digest fInit fApp fFini (s.mem.live? sha.id) sha.offset r a (bytesOf (readWord hmsg))
  let B := basePoint.toAffine wellFormed_basePoint
  sig.offset.toNat + 64 ≤ 2 ^ 64 →
    msg.offset.toNat + sz.toNat ≤ 2 ^ 64 →
    IsSha512Ptr s.mem sha →
    sha.offset.toNat + 256 ≤ 2 ^ 64 →
    Sha512KHolds s sha kbits →
    sha.id ≠ sig.id →
    sha.id ≠ pk.id →
    sha.id ≠ msg.id →
    s.RefWF [sha] →
    ScalarReduceBy f →
    Sha512InitBy fInit →
    Sha512AppendBy kbits fApp →
    Sha512FiniBy kbits fFini →
    ∀ Bt,
      BaseTableHolds s Bt →
        BaseVals Bt basePoint wellFormed_basePoint →
        ∀ dig,
          digest = some dig →
            ∀ w,
              f dig = some w →
                ∃ (s' : GlobalState) (ret : BitVec 32),
                  result = .value ([.value ret]ₕ, s') ∧
                    s'.alloc = s.alloc ∧
                    s'.globals = s.globals ∧
                    (∀ b : BlockId, b ≠ sha.id → s'.mem.live? b = s.mem.live? b) ∧
                    ret ∈
                      [FD_ED25519_SUCCESS, FD_ED25519_ERR_SIG, FD_ED25519_ERR_PUBKEY,
                        FD_ED25519_ERR_MSG] ∧
                    (ret = FD_ED25519_ERR_SIG ∨ ret = FD_ED25519_ERR_PUBKEY → s ≈ s') ∧
                    (groupOrder ≤ S → ret = FD_ED25519_ERR_SIG) ∧
                    (S < groupOrder → (¬∃ A, Encodes a A) → ret = FD_ED25519_ERR_PUBKEY) ∧
                    (S < groupOrder →
                      (∃ A, Encodes a A) → (¬∃ R, Encodes r R) → ret = FD_ED25519_ERR_SIG) ∧
                    (S < groupOrder →
                      ∀ A R,
                        Encodes a A →
                          Encodes r R →
                          ((A.x, A.y) ∈ lowOrder → ret = FD_ED25519_ERR_PUBKEY) ∧
                            ((A.x, A.y) ∉ lowOrder →
                              (R.x, R.y) ∈ lowOrder → ret = FD_ED25519_ERR_SIG) ∧
                            ((A.x, A.y) ∉ lowOrder →
                              (R.x, R.y) ∉ lowOrder →
                              (ret = FD_ED25519_SUCCESS ↔
                                  ((packWords w).toNat % 2 ^ 255) • -A + S • B = R) ∧
                                (ret = FD_ED25519_SUCCESS ∨ ret = FD_ED25519_ERR_MSG)))

end Firedancer.Ref
