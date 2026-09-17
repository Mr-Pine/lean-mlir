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

The compression function reads its round constants from the global `fd_sha512_core_ref.K`. The
statements that reach it take those 640 bits as a parameter: the functions may depend on them,
and `K` must hold them whenever a call runs.
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

/-- `fd_sha512_core_ref.K`, the round-constant table, holds the 640 bits `k`, outside `sha`'s
block. Which constants they are does not matter to the statements below, only that they are the
same whenever a call runs. -/
def Sha512KHolds (s : GlobalState) (sha : Pointer) (k : BitVec (80 * 64)) : Prop :=
  ∃ q, HoldsGlobal s "fd_sha512_core_ref.K" q k ∧ q.id ≠ sha.id

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
def Sha512CoreRefBy (k : BitVec (80 * 64))
    (f : Option LiveBlock → BitVec 64 → List (BitVec 8) → Option (Option LiveBlock)) : Prop :=
  ∀ (st blk : Pointer) (cnt : BitVec 64) (s : GlobalState),
    s.WF →
      -- the loop is a `do … while (--block_cnt)`: at 0 it would read past the stated bytes
      cnt ≠ 0 →
      blk.offset.toNat + cnt.toNat * 128 ≤ 2 ^ 64 →
        Sha512KHolds s st k →
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
def Sha512AppendBy (k : BitVec (80 * 64))
    (f : Option LiveBlock → BitVec 64 → List (BitVec 8) → Option (Option LiveBlock)) : Prop :=
  ∀ (sha data : Pointer) (sz : BitVec 64) (s : GlobalState),
    s.WF →
      data.offset.toNat + sz.toNat ≤ 2 ^ 64 →
        sha.id ≠ data.id →
          Sha512KHolds s sha k →
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
def Sha512FiniBy (k : BitVec (80 * 64))
    (f : Option LiveBlock → BitVec 64 → Option LiveBlock → BitVec 64 → Option (BitVec 512)) :
    Prop :=
  ∀ (sha hash : Pointer) (s : GlobalState),
    s.WF →
      Fits s.mem hash (64 * 8) →
        hash.offset.toNat + 64 ≤ 2 ^ 64 →
          sha.id ≠ hash.id →
            Sha512KHolds s sha k →
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
axiom sha512CoreRef_determined : ∀ k, ∃ f, Sha512CoreRefBy k f

/-- Assumed: `fd_sha512_append` reads nothing else. -/
axiom sha512Append_determined : ∀ k, ∃ f, Sha512AppendBy k f

/-- Assumed: `fd_sha512_fini` reads nothing else. -/
axiom sha512Fini_determined : ∀ k, ∃ f, Sha512FiniBy k f

end Firedancer.Common
