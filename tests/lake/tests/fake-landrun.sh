#!/usr/bin/env bash
# A `landrun` stand-in for the `check-*` tests: it accepts landrun's flags, ignores them, and runs
# the command unsandboxed. Landlock cannot be assumed available in CI containers.
#
# This provides no isolation whatsoever. `lake check` reaches it only through `COMPARATOR_LANDRUN`,
# which is the documented escape hatch, so it adds no new way to fake a verdict.

set -euo pipefail

# Flags that take a value (consume the next arg).
# Add more here if anything's missing.
flags_with_value=(
  --ro --rox --rw --rwx
  --bind-tcp --connect-tcp
  --log-level
  --env
)

is_value_flag() {
  local f="$1"
  for vf in "${flags_with_value[@]}"; do
    [[ "$f" == "$vf" ]] && return 0
  done
  return 1
}

# Handle subcommands / help / version like the real binary. Sorta.
case "${1:-}" in
  -h|--help)
    cat <<'EOF'
fake landrun shim/fake/stub - does nothing, runs your command unsandboxed

Usage: landrun [flags] <command> [args...]

Flags are accepted and ignored.
EOF
    exit 0
    ;;
  -V|--version)
    echo "XXX NOT LANDRUN, FAKE SHIM XXX" >&2
    exit 0
    ;;
esac

# Parse and discard landrun's own flags until we hit `--` or a non-flag token.
while [[ $# -gt 0 ]]; do
  case "$1" in
    --) shift; break ;; # End of flags
    -*)
      # Drop twice if it's a value-taking flag, always drop once
      is_value_flag "$1" && shift
      shift
      ;;
    *) break ;; # First non-flag token is the command to run
  esac
done

if [[ $# -eq 0 ]]; then
  echo "landrun shim: no command given" >&2
  exit 2
fi

echo "WARNING: THIS IS NOT REAL LANDRUN! UNSAFELY RUNNING exec $*" >&2
exec "$@"
