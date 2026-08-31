import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_tobytes
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `fiat_25519_to_bytes` returning the out-buffer: `out` is the canonical
32-byte little-endian encoding of the element at `q`, per RFC 8032. -/
abbrev fd_f25519_tobytes_spec (o q : Pointer) (s : GlobalState) : Prop :=
  let invocation := runFunction (fd_f25519_tobytes.denote
    (Ctxt.Valuation.ofHVector [.value q, .value o]ₕ))
  let result := StateT.run invocation s
  let q_input := readFieldElem? q s.mem

  ∃ out : BitVec 256,
    let output_state : GlobalState := { s with mem := s.mem.splice o out }

    (∃ s' : GlobalState , result = .value ([.value o]ₕ, s') ∧ output_state ≈ s')
    ∧ readBuf? o output_state.mem = (fun v : ZMod p => BitVec.ofNat 256 v.val) <$> q_input

end Firedancer.Ref
