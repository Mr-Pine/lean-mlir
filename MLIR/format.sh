#!/usr/bin/env bash
# Format Lean files with lean-fmt. lean-fmt analyzes built modules, so they are built first.
# Usage: format.sh [--check] [FILE...]   (default: every .lean file under this directory)
# Paths are relative to the current directory; the script may be run from anywhere.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)

toolchain=$(sed 's#^leanprover/lean4:##' "$root/lean-toolchain")
LEAN_FMT=${LEAN_FMT:-$HOME/.local/bin/lean-fmt-$toolchain}
if [[ ! -x $LEAN_FMT ]]; then
  echo "no lean-fmt for $toolchain at $LEAN_FMT (set LEAN_FMT)" >&2
  exit 2
fi

args=()
if [[ ${1:-} == --check ]]; then
  args+=(--check)
  shift
fi

files=()
if (($# > 0)); then
  for f in "$@"; do
    files+=("$(realpath --relative-to="$root" "$f")")
  done
else
  while IFS= read -r f; do
    files+=("$(realpath --relative-to="$root" "$f")")
  done < <(find "$here" -name '*.lean' | sort)
fi

modules=()
for f in "${files[@]}"; do
  m=${f%.lean}
  modules+=("${m//\//.}")
done

cd "$root"
lake build "${modules[@]}"
exec "$LEAN_FMT" format "${args[@]}" "${files[@]}"
