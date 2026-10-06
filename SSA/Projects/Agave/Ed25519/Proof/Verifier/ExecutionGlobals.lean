module

public import SSA.Projects.RIR.Global

/-! Exact byte initializers extracted by MLIR/import_verifier.py. -/

namespace Agave.Ed25519.Verifier.Execution

open LeanMLIR.RIR
@[expose] public section

-- Source bytes SHA-256: b68f593141969cfeddf2011667ccdca92d2d22b414194bdf4ccbaa2833c85be2
def identityOne : ByteGlobal :=
  ⟨"alloc_d6091242425a18f93aa551ed73483e0d", 40, 0x00000000000000000000000000000000000000000000000000000000000000000000000000000001, 8, by decide⟩

-- Source bytes SHA-256: 3b721fb05904288533a0c3f44162aa4631530bcfebd22c3e57dbc4994e38f83d
def sha512InitialState : ByteGlobal :=
  ⟨"anon.2688bd6af3b9e90d4f6e608faea972d6.1", 64, 0x5be0cd19137e21791f83d9abfb41bd6b9b05688c2b3e6c1f510e527fade682d1a54ff53a5f1d36f13c6ef372fe94f82bbb67ae8584caa73b6a09e667f3bcc908, 16, by decide⟩

end
end Agave.Ed25519.Verifier.Execution
