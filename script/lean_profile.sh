#!/usr/bin/env bash
# Profile a Lean binary with demangled names.
#
# Usage:
#   script/lean_profile.sh ./my_lean_binary [args...]
#
# Records a profile with samply, symbolicates via samply's API,
# demangles Lean symbol names, and opens the result in Firefox Profiler.
#
# Requirements: samply (cargo install samply), python3
#
# Options (via environment variables):
#   SAMPLY_RATE    — sampling rate in Hz (default: 1000)
#   SAMPLY_PORT    — port for samply symbolication server (default: 3756)
#   SERVE_PORT     — port for serving the demangled profile (default: 3757)
#   PROFILE_KEEP   — set to 1 to keep the raw profile after demangling

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROFILER_DIR="$SCRIPT_DIR/profiler"
SYMBOLICATE="$PROFILER_DIR/symbolicate_profile.py"
SERVE_PROFILE="$PROFILER_DIR/serve_profile.py"

usage() {
    cat >&2 <<EOF
Usage: $0 [options] <lean-binary> [args...]

Profile a Lean binary and view the results in Firefox Profiler
with demangled Lean names.

Requirements:
  samply    cargo install samply
  python3   (included with macOS / most Linux distros)

Environment variables:
  SAMPLY_RATE    sampling rate in Hz (default: 1000)
  SAMPLY_PORT    port for samply symbolication server (default: 3756)
  SERVE_PORT     port for serving the demangled profile (default: 3757)
  PROFILE_KEEP   set to 1 to keep the temp directory after profiling

Reading demangled names:
  Compiler suffixes are shown as modifier flags after the name:
    [arity↓]   reduced-arity specialization     (_redArg)
    [boxed]    boxed calling-convention wrapper  (_boxed)
    [λ]        lambda-lifted closure             (_lam_N, _lambda_N, _elam_N)
    [jp]       join point                        (_jp_N)
    [closed]   extracted closed subterm          (_closed_N)
    [private]  private (module-scoped) def       (_private.Module.0. prefix)
    [impl]     implementation detail             (_impl)

  Specializations appear after the flags:
    Lean.Meta.foo [λ] spec at Lean.Meta.bar[λ, arity↓]
      = foo (with lambda closure), specialized at bar (lambda, reduced arity)

  Multiple "spec at" entries indicate chained specializations.
  See script/PROFILER_README.md for full documentation.
EOF
    exit "${1:-0}"
}

if [ $# -eq 0 ]; then
    usage 1
fi

case "${1:-}" in
    -h|--help) usage 0 ;;
esac

if ! command -v samply &>/dev/null; then
    echo "error: samply not found. Install with: cargo install samply" >&2
    exit 1
fi

RATE="${SAMPLY_RATE:-1000}"
PORT="${SAMPLY_PORT:-3756}"
SERVE="${SERVE_PORT:-3757}"
TMPDIR=$(mktemp -d /tmp/lean-profile-XXXXXX)
TMPFILE="$TMPDIR/profile.json.gz"
DEMANGLED="$TMPDIR/profile-demangled.json.gz"
SAMPLY_LOG="$TMPDIR/samply.log"
SAMPLY_PID=""

cleanup() {
    if [ -n "$SAMPLY_PID" ]; then
        kill "$SAMPLY_PID" 2>/dev/null || true
        wait "$SAMPLY_PID" 2>/dev/null || true
    fi
    # Safety net: kill anything still on the symbolication port
    lsof -ti :"$PORT" 2>/dev/null | xargs kill 2>/dev/null || true
    [ "${PROFILE_KEEP:-0}" = "1" ] || rm -rf "$TMPDIR"
}
trap cleanup EXIT

# Step 1: Record
echo "Recording profile (rate=${RATE} Hz)..." >&2
samply record --save-only -o "$TMPFILE" -r "$RATE" "$@"

# Step 2: Start samply server for symbolication
echo "Starting symbolication server..." >&2
samply load --no-open -P "$PORT" "$TMPFILE" > "$SAMPLY_LOG" 2>&1 &
SAMPLY_PID=$!

# Wait for server to be ready
for i in $(seq 1 30); do
    if grep -q "Local server listening" "$SAMPLY_LOG" 2>/dev/null; then
        break
    fi
    sleep 0.2
done

# Extract the token from samply's output
TOKEN=$(grep -oE '[a-z0-9]{30,}' "$SAMPLY_LOG" | head -1)

if [ -z "$TOKEN" ]; then
    echo "error: could not get samply server token" >&2
    exit 1
fi

SERVER_URL="http://127.0.0.1:${PORT}/${TOKEN}"

# Step 3: Symbolicate + demangle
echo "Symbolicating and demangling..." >&2
python3 "$SYMBOLICATE" --server "$SERVER_URL" "$TMPFILE" -o "$DEMANGLED"

# Step 4: Kill symbolication server
kill "$SAMPLY_PID" 2>/dev/null || true
wait "$SAMPLY_PID" 2>/dev/null || true
SAMPLY_PID=""

# Step 5: Serve the demangled profile directly (without samply's re-symbolication)
echo "Opening in Firefox Profiler..." >&2
python3 "$SERVE_PROFILE" "$DEMANGLED" -P "$SERVE"
