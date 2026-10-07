module

public import SSA.Projects.SLLVM.Dialect
public import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_tobytes
public import SSA.Projects.Firedancer.Ref.Spec.F25519

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `fiat_25519_to_bytes` returning the out-buffer: `out` is the canonical
32-byte little-endian encoding of the element at `q`, per RFC 8032. -/
abbrev fd_f25519_tobytes_spec (o q : Pointer) (s : GlobalState) (ho : IsByteBufPtr s.mem o)
    (hq : IsFieldElemPtr s.mem q) : Prop :=
  let invocation :=
    runFunction (fd_f25519_tobytes.denote (Ctxt.Valuation.ofHVector [.value q, .value o]ₕ))
  let result := StateT.run invocation s
  let q_input := readFieldElem hq
  ∃ out : BitVec 256,
    let output_state : GlobalState := { s with mem := s.mem.splice o out }
    readBuf (m := output_state.mem) (isByteBufPtr_splice ho) = BitVec.ofNat 256 q_input.val ∧
      (∃ s' : GlobalState, result = .value ([.value o]ₕ, s') ∧ output_state ≈ s')

end Firedancer.Ref
