/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg
import SSA.Projects.Firedancer.Proof.Globals

/-!
# SHA-512 (common)

SHA-512 is not lifted and not specified. `fd_sha512_init`, `fd_sha512_core_ref`,
`fd_sha512_append` and `fd_sha512_fini` are constants with their signatures only, and each is
assumed to be decided by what it reads, in the shape `ScalarReduceBy` uses for
`fd_curve25519_scalar_reduce`: one function of those inputs gives both whether the call returns
and what it leaves behind. The AVX512 build's SHA-512 is assembly, so this is its assumption too.

The compression function reads its round constants from the global `fd_sha512_core_ref.K`, which
must therefore hold them.
-/

namespace Firedancer.Common

open LeanMLIR SLLVM

/-- `fd_sha512_init(sha)`. -/
axiom fd_sha512_init : Cfg (Ctxt.ofList [SLLVM.Ty.ptr]) [SLLVM.Ty.ptr]

/-- `fd_sha512_core_ref(state, block, block_cnt)`. -/
axiom fd_sha512_core_ref :
  Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) []

/-- `fd_sha512_append(sha, data, sz)`. -/
axiom fd_sha512_append :
  Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr]

/-- `fd_sha512_fini(sha, hash)`. -/
axiom fd_sha512_fini : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr]

/-- A `fd_sha512_t` at `sha`: the whole 256-byte struct is addressable. -/
abbrev IsSha512Ptr (m : MemoryState) (sha : Pointer) : Prop :=
  Fits m sha (256 * 8)

/-- The SHA-512 round constants, FIPS 180-4 §4.2.3. -/
def sha512K : List (BitVec 64) :=
  [0x428a2f98d728ae22#64, 0x7137449123ef65cd#64, 0xb5c0fbcfec4d3b2f#64, 0xe9b5dba58189dbbc#64,
    0x3956c25bf348b538#64, 0x59f111f1b605d019#64, 0x923f82a4af194f9b#64, 0xab1c5ed5da6d8118#64,
    0xd807aa98a3030242#64, 0x12835b0145706fbe#64, 0x243185be4ee4b28c#64, 0x550c7dc3d5ffb4e2#64,
    0x72be5d74f27b896f#64, 0x80deb1fe3b1696b1#64, 0x9bdc06a725c71235#64, 0xc19bf174cf692694#64,
    0xe49b69c19ef14ad2#64, 0xefbe4786384f25e3#64, 0x0fc19dc68b8cd5b5#64, 0x240ca1cc77ac9c65#64,
    0x2de92c6f592b0275#64, 0x4a7484aa6ea6e483#64, 0x5cb0a9dcbd41fbd4#64, 0x76f988da831153b5#64,
    0x983e5152ee66dfab#64, 0xa831c66d2db43210#64, 0xb00327c898fb213f#64, 0xbf597fc7beef0ee4#64,
    0xc6e00bf33da88fc2#64, 0xd5a79147930aa725#64, 0x06ca6351e003826f#64, 0x142929670a0e6e70#64,
    0x27b70a8546d22ffc#64, 0x2e1b21385c26c926#64, 0x4d2c6dfc5ac42aed#64, 0x53380d139d95b3df#64,
    0x650a73548baf63de#64, 0x766a0abb3c77b2a8#64, 0x81c2c92e47edaee6#64, 0x92722c851482353b#64,
    0xa2bfe8a14cf10364#64, 0xa81a664bbc423001#64, 0xc24b8b70d0f89791#64, 0xc76c51a30654be30#64,
    0xd192e819d6ef5218#64, 0xd69906245565a910#64, 0xf40e35855771202a#64, 0x106aa07032bbd1b8#64,
    0x19a4c116b8d2d0c8#64, 0x1e376c085141ab53#64, 0x2748774cdf8eeb99#64, 0x34b0bcb5e19b48a8#64,
    0x391c0cb3c5c95a63#64, 0x4ed8aa4ae3418acb#64, 0x5b9cca4f7763e373#64, 0x682e6ff3d6b2b8a3#64,
    0x748f82ee5defb2fc#64, 0x78a5636f43172f60#64, 0x84c87814a1f0ab72#64, 0x8cc702081a6439ec#64,
    0x90befffa23631e28#64, 0xa4506cebde82bde9#64, 0xbef9a3f7b2c67915#64, 0xc67178f2e372532b#64,
    0xca273eceea26619c#64, 0xd186b8c721c0c207#64, 0xeada7dd6cde0eb1e#64, 0xf57d4f7fee6ed178#64,
    0x06f067aa72176fba#64, 0x0a637dc5a2c898a6#64, 0x113f9804bef90dae#64, 0x1b710b35131c471b#64,
    0x28db77f523047d84#64, 0x32caab7b40c72493#64, 0x3c9ebe0a15c9bebc#64, 0x431d67c49c100d4c#64,
    0x4cc5d4becb3e42b6#64, 0x597f299cfc657e2a#64, 0x5fcb6fab3ad6faec#64, 0x6c44198c4a475817#64]

/-- `sha512K` as the 640 bits `fd_sha512_core_ref.K` holds, `K[0]` least significant. -/
def sha512KBits : BitVec (80 * 64) :=
  BitVec.ofNat _ (sha512K.foldr (fun k acc => k.toNat + 2 ^ 64 * acc) 0)

/-- `fd_sha512_core_ref.K` holds the round constants, outside `sha`'s block. -/
def Sha512KHolds (s : GlobalState) (sha : Pointer) : Prop :=
  ∃ q, HoldsGlobal s "fd_sha512_core_ref.K" q sha512KBits ∧ q.id ≠ sha.id

/-- The `n` little-endian bytes of `w`. -/
def bytesOf {n : Nat} (w : BitVec (n * 8)) : List (BitVec 8) :=
  List.ofFn fun i : Fin n => w.extractLsb' (i * 8) 8

/-- **`fd_sha512_init` is decided by what it reads.** `f` gives the block the call leaves at
`sha` -- `none` if it does not return -- from the block that was there and `sha`'s offset. -/
def Sha512InitBy (f : Option LiveBlock → BitVec 64 → Option (Option LiveBlock)) : Prop :=
  ∀ (sha : Pointer) (s : GlobalState),
    s.WF →
      IsSha512Ptr s.mem sha →
        let invocation := runFunction (fd_sha512_init.denote (Ctxt.Valuation.singleton (.value sha)))
        (∀ blk,
            f (s.mem.live? sha.id) sha.offset = some blk →
              ∃ s' : GlobalState,
                StateT.run invocation s = .value ([.value sha]ₕ, s') ∧
                  s'.WF ∧
                  s'.alloc = s.alloc ∧
                  s'.globals = s.globals ∧
                  (∀ b : BlockId, b ≠ sha.id → s'.mem.live? b = s.mem.live? b) ∧
                  s'.mem.live? sha.id = blk) ∧
          (f (s.mem.live? sha.id) sha.offset = none → StateT.run invocation s = .poison)

/-- **`fd_sha512_core_ref` is decided by what it reads.** `f` gives the block the call leaves at
`st` -- `none` if it does not return -- from the block that was there, `st`'s offset and the
`cnt * 128` bytes at `blk`. `blk` may lie in `st`'s own block, as `append` passes `sha->buf`. -/
def Sha512CoreRefBy
    (f : Option LiveBlock → BitVec 64 → List (BitVec 8) → Option (Option LiveBlock)) : Prop :=
  ∀ (st blk : Pointer) (cnt : BitVec 64) (s : GlobalState),
    s.WF →
      -- the loop is a `do … while (--block_cnt)`: at 0 it would read past the stated bytes
      cnt ≠ 0 →
      blk.offset.toNat + cnt.toNat * 128 ≤ 2 ^ 64 →
        Sha512KHolds s st →
          ∀ hblk : Fits s.mem blk (cnt.toNat * 128 * 8),
            let invocation :=
              runFunction
                (fd_sha512_core_ref.denote
                  (Ctxt.Valuation.ofHVector [.value cnt, .value blk, .value st]ₕ))
            (∀ b',
                f (s.mem.live? st.id) st.offset (bytesOf (readWord hblk)) = some b' →
                  ∃ s' : GlobalState,
                    StateT.run invocation s = .value (.nil, s') ∧
                      s'.WF ∧
                      s'.alloc = s.alloc ∧
                      s'.globals = s.globals ∧
                      (∀ b : BlockId, b ≠ st.id → s'.mem.live? b = s.mem.live? b) ∧
                      s'.mem.live? st.id = b') ∧
              (f (s.mem.live? st.id) st.offset (bytesOf (readWord hblk)) = none →
                StateT.run invocation s = .poison)

/-- **`fd_sha512_append` is decided by what it reads.** `f` gives the block the call leaves at
`sha` -- `none` if it does not return -- from the block that was there, `sha`'s offset and the
bytes at `data`. What that block is stays open; the rest is the footprint. -/
def Sha512AppendBy
    (f : Option LiveBlock → BitVec 64 → List (BitVec 8) → Option (Option LiveBlock)) : Prop :=
  ∀ (sha data : Pointer) (sz : BitVec 64) (s : GlobalState),
    s.WF →
      data.offset.toNat + sz.toNat ≤ 2 ^ 64 →
        sha.id ≠ data.id →
          Sha512KHolds s sha →
            ∀ hdata : Fits s.mem data (sz.toNat * 8),
              let invocation :=
                runFunction
                  (fd_sha512_append.denote
                    (Ctxt.Valuation.ofHVector [.value sz, .value data, .value sha]ₕ))
              (∀ blk,
                  f (s.mem.live? sha.id) sha.offset (bytesOf (readWord hdata)) = some blk →
                    ∃ s' : GlobalState,
                      StateT.run invocation s = .value ([.value sha]ₕ, s') ∧
                        s'.WF ∧
                        s'.alloc = s.alloc ∧
                        s'.globals = s.globals ∧
                        (∀ b : BlockId, b ≠ sha.id → s'.mem.live? b = s.mem.live? b) ∧
                        s'.mem.live? sha.id = blk) ∧
                (f (s.mem.live? sha.id) sha.offset (bytesOf (readWord hdata)) = none →
                  StateT.run invocation s = .poison)

/-- **`fd_sha512_fini` is decided by what it reads.** `f` gives the 64 bytes it writes at `hash`
from the two blocks and offsets, `none` if it does not return. -/
def Sha512FiniBy
    (f : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option (BitVec 512)) :
    Prop :=
  ∀ (sha hash : Pointer) (s : GlobalState),
    s.WF →
      Fits s.mem hash (64 * 8) →
        hash.offset.toNat + 64 ≤ 2 ^ 64 →
          sha.id ≠ hash.id →
            Sha512KHolds s sha →
              let invocation :=
                runFunction
                  (fd_sha512_fini.denote (Ctxt.Valuation.ofHVector [.value hash, .value sha]ₕ))
              (∀ d,
                  f (s.mem.live? sha.id) sha.offset (s.mem.live? hash.id) hash.offset = some d →
                    ∃ s' : GlobalState,
                      StateT.run invocation s = .value ([.value hash]ₕ, s') ∧
                        s'.WF ∧
                        s'.alloc = s.alloc ∧
                        s'.globals = s.globals ∧
                        (∀ b : BlockId,
                          ¬(b = sha.id ∨ b = hash.id) → s'.mem.live? b = s.mem.live? b) ∧
                        ∃ h : Fits s'.mem hash (64 * 8), readWord h = d) ∧
                (f (s.mem.live? sha.id) sha.offset (s.mem.live? hash.id) hash.offset = none →
                  StateT.run invocation s = .poison)

/-- Assumed: `fd_sha512_init` reads nothing else. -/
axiom sha512Init_determined : ∃ f, Sha512InitBy f

/-- Assumed: `fd_sha512_core_ref` reads nothing else. -/
axiom sha512CoreRef_determined : ∃ f, Sha512CoreRefBy f

/-- Assumed: `fd_sha512_append` reads nothing else. -/
axiom sha512Append_determined : ∃ f, Sha512AppendBy f

/-- Assumed: `fd_sha512_fini` reads nothing else. -/
axiom sha512Fini_determined : ∃ f, Sha512FiniBy f

end Firedancer.Common
