set -euo pipefail

out="${NAME}.out"
trap 'rm -f "$out"' EXIT

if lean -j0 >"$out" 2>&1; then
  echo "lean -j0 unexpectedly succeeded" >&2
  exit 1
fi

grep -Fx "error: expected positive numeric argument for option '-j'" "$out"
