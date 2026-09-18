/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.Scalar.fd_curve25519_scalar_validate
import SSA.Projects.Firedancer.Common.Spec.SHA
import SSA.Projects.Firedancer.Common.Spec.Group

/-!
# The return codes, encodings and digest of `fd_ed25519_verify` (common)

The digest in `k` is a function of `sha`'s block, `R`, `A` and the message, and of nothing else:
it chains the four functions `Common/Spec/SHA` assumes decide the SHA-512 calls.
-/

namespace Firedancer.Common

open LeanMLIR SLLVM

/-- `fd_ed25519.h`'s return codes. -/
def FD_ED25519_SUCCESS : BitVec 32 :=
  0

def FD_ED25519_ERR_SIG : BitVec 32 :=
  -1

def FD_ED25519_ERR_PUBKEY : BitVec 32 :=
  -2

def FD_ED25519_ERR_MSG : BitVec 32 :=
  -3

/-- The digest `fd_ed25519_verify` writes to `k`: the state at `off` in `blk` initialised, `R`, `A`
and `msg` appended, then finished into `k`, a fresh 64-byte local. `none` if any call fails to
return. -/
def ed25519Digest
    (fInit : Option LiveBlock → BitVec 64 → Option (Option LiveBlock))
    (fApp : Option LiveBlock → BitVec 64 → List (BitVec 8) → Option (Option LiveBlock))
    (fFini : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option (BitVec 512))
    (blk : Option LiveBlock) (off : BitVec 64) (r a : BitVec 256) (msg : List (BitVec 8)) :
    Option (BitVec 512) :=
  -- `bind`, not `do`: the latter desugars to a `match`, which `Option.bind_eq_some_iff` misses
  (fInit blk off).bind fun b₀ =>
    (fApp b₀ off (bytesOf (n := 32) r)).bind fun b₁ =>
      (fApp b₁ off (bytesOf (n := 32) a)).bind fun b₂ =>
        (fApp b₂ off msg).bind fun b₃ => fFini b₃ off (some { length := 64, bytes := 0#_ }) 0

/-- `V` is a point `bytes` names: `y` its low 255 bits reduced, the sign bit `x`'s parity. -/
def Encodes (bytes : BitVec 256) (V : Edwards.Point Ed25519.curve) : Prop :=
  V.y = ((bytes.extractLsb' 0 255).toNat : ZMod p) ∧
    (V.x ≠ 0 → (V.x.val % 2 = 0 ↔ bytes[255] = false))

end Firedancer.Common
