module

public import SSA.Projects.RIR.Global

/-! Exact byte initializers extracted by MLIR/import_scalar_wide.py. -/

namespace Agave.Ed25519.Verifier.Execution.ScalarWide

open LeanMLIR.RIR
@[expose] public section

-- Source bytes SHA-256: 8b66dd610871c608b418a629c06e712c2da21cebb797c9ece45ff47eedd61205
def montgomeryR : ByteGlobal :=
  ⟨"alloc_595ed8f9b6c4f781a4a1d10db150f124", 40, 0x00000fffffffffff000fffffffffffff000fffffeb35e51b0003bab5ac67e45a000f48bd6721e6ed, 8, by decide⟩

-- Source bytes SHA-256: 1102b2862e097d020ed2fc0cad75ecddcb99b9b5c9a5263c2cc537e6af67da7a
def montgomeryRR : ByteGlobal :=
  ⟨"alloc_b0a0adc7a7ee3d20b0509962c17b23d6", 40, 0x000009411b7c309a0003dceec73d217f0005be65cb687604000d63c715bea69f0009d265e952d13b, 8, by decide⟩

end
end Agave.Ed25519.Verifier.Execution.ScalarWide
