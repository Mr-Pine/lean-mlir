#!/usr/bin/env bash
# Lifts source.c into Examples/Mlir/*.lean.
# -fwrapv defines signed overflow as wrapping, -fno-unroll-loops keeps loops
# readable (pragmas still unroll), and the phi-folding threshold keeps
# if/else as branches instead of a select.
# Usage: ./extract.sh [root-func...]   (default: every external function)
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
llvm_bin=${LLVM_BIN:-$HOME/.local/llvm-23/bin}
extractor=${EXTRACTOR:-$here/../extractor/target/release/extractor}
out=$here/build/extract

mkdir -p "$out"
cat > "$out/compile_commands.json" <<EOF
[
  {
    "directory": "$here",
    "file": "source.c",
    "arguments": ["$llvm_bin/clang", "-O2", "-fwrapv", "-fno-unroll-loops", "-mllvm", "-two-entry-phi-node-folding-threshold=0",
                  "-c", "source.c", "-o", "source.o"]
  }
]
EOF

"$extractor" --llvm-bin "$llvm_bin" compile "$out/compile_commands.json" "$out"
"$extractor" --llvm-bin "$llvm_bin" translate "$out/module.ll" "$out"

if [ $# -eq 0 ]; then
  mapfile -t funcs < <(sed -n '/^define /{/internal/d;s/.*@\([A-Za-z0-9_.]*\)(.*/\1/p}' "$out/module.ll")
else
  funcs=("$@")
fi

"$extractor" import "$out/module.mlir" "$here" Examples/Mlir Examples.Mlir \
  $(printf -- '--root-func %s ' "${funcs[@]}")
