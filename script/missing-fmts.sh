#!/usr/bin/env bash
# usage: missing-fmts.sh <stage dir> <outdir> [jobs] [filelist]
# Elaborates each repo-relative core file with `<stage dir>/bin/lean` and the `linter.fmt.missing`
# linter enabled, against the `.olean` files of the same stage. The stage must be stage1 or later:
# stage0 does not contain the linter. Without a file list, all core files are linted.
# Writes the output of each file to <outdir>/<file>.log, "<exit code> <linter warnings> <file>"
# lines to <outdir>/results.txt and the reported syntax kinds to <outdir>/summary.txt.
# Set IGNORE_PRIVATE=false to also report the private kinds of `local` syntax.
set -u
repo=$(realpath "$(dirname "$0")/..")
export STAGE=$(realpath "$1")
out=$(realpath -m "$2")
jobs=${3:-48}
list=${4:+$(realpath "$4")}
export OUT=$out
export LEAN_PATH=$STAGE/lib/lean
export IGNORE_PRIVATE=${IGNORE_PRIVATE:-true}
if [ -n "$list" ] && [ ! -f "$list" ]; then
  echo "error: file list '$4' does not exist" >&2
  exit 1
fi
mkdir -p "$out"
cd "$repo"
if [ -z "$list" ]; then
  list=$out/files.txt
  { ls src/*.lean src/lake/*.lean; find src/Init src/Std src/Lean src/lake/Lake -name '*.lean'; } |
    sort > "$list"
fi
while read -r f; do mkdir -p "$out/$(dirname "$f")"; done < "$list"
ulimit -s unlimited
# `--root` gives `lean` the module name. Without it, some files do not elaborate.
# `lean` does not link Lake, so Lake's builtin formatters only register when Lake is loaded as a
# plugin. Without it, all Lake syntax is reported as missing.
# `pp.fullNames` prints the kinds independently of the open namespaces, so that summary.txt
# counts each kind in one row.
xargs -a "$list" -P "$jobs" -I{} bash -c '
  case "{}" in
    src/lake/*) args="--root=src/lake --plugin=$STAGE/lib/lean/libLake_shared.so" ;;
    *) args=--root=src ;;
  esac
  timeout 1800 "$STAGE/bin/lean" $args -Dlinter.fmt.missing=true \
    -Dlinter.fmt.missing.ignorePrivate=$IGNORE_PRIVATE -Dinterpreter.prefer_native=false \
    -Dpp.fullNames=true "{}" > "$OUT/{}.log" 2>&1
  code=$?
  n=$(grep -cE ": warning: (no auto-formatter registered|Auto-formatter .*is incomplete|The auto-formatter failed)" "$OUT/{}.log")
  echo "$code $n {}"' | sort -k3 > "$out/results.txt"
{
  echo "files: $(wc -l < "$out/results.txt"), nonzero exit: $(awk '$1 != 0' "$out/results.txt" | wc -l)"
  echo "error lines: $(grep -rhE ": error(:|\()" "$out" --include=*.log | wc -l)"
  awk '{ s += $2 } $2 > 0 { f++ } END { printf "linter warnings: %d in %d files\n", s, f }' "$out/results.txt"
  echo "formatter failures: $(grep -rh ": warning: The auto-formatter failed" "$out" --include=*.log | wc -l)"
  echo "--- missing formatters (count, kind):"
  grep -rhoP ": warning: no auto-formatter registered for syntax kind \K\S+" "$out" --include=*.log |
    sort | uniq -c | sort -rn
  echo "--- incomplete formatters (count, kind):"
  grep -rhoP ": warning: Auto-formatter .*for syntax kind \K\S+(?= is incomplete)" "$out" --include=*.log |
    sort | uniq -c | sort -rn
} > "$out/summary.txt"
head -3 "$out/summary.txt"
