#!/usr/bin/env bash
# A `bwrap` stand-in for the `challenge-*` tests: it accepts bwrap's flags, applies the ones that
# affect what the command observes, and runs the command unsandboxed. Unprivileged user namespaces
# cannot be assumed available in CI containers.
#
# Mounts and namespaces are ignored, so this provides no isolation whatsoever; `--clearenv` and
# `--setenv` are honoured, because the command's environment is what the tests exercise. `lake
# challenge` reaches this only through `COMPARATOR_BWRAP`, which is the documented escape hatch, so
# it adds no new way to fake a verdict.

set -euo pipefail

# Flags that consume one argument.
flags_with_value=(
  --chdir --tmpfs --dev --proc --dir --symlink --file
  --uid --gid --hostname --args --bind-data --ro-bind-data
)
# Flags that consume two.
flags_with_two_values=(
  --bind --bind-try --ro-bind --ro-bind-try --dev-bind --dev-bind-try
)

is_value_flag() {
  local f="$1" vf
  for vf in "${flags_with_value[@]}"; do
    [[ "$f" == "$vf" ]] && return 0
  done
  return 1
}

is_two_value_flag() {
  local f="$1" vf
  for vf in "${flags_with_two_values[@]}"; do
    [[ "$f" == "$vf" ]] && return 0
  done
  return 1
}

# Handle subcommands / help / version like the real binary. Sorta.
case "${1:-}" in
  -h|--help)
    cat <<'EOF'
fake bwrap shim/fake/stub - ignores the sandboxing, runs your command unsandboxed

Usage: bwrap [flags] <command> [args...]

Flags are accepted; only --clearenv and --setenv have any effect.
EOF
    exit 0
    ;;
  -V|--version)
    echo "XXX NOT BWRAP, FAKE SHIM XXX" >&2
    exit 0
    ;;
esac

cleared=0
env_args=()
chdir=

# Parse bwrap's own flags until we hit `--` or a non-flag token.
while [[ $# -gt 0 ]]; do
  case "$1" in
    --) shift; break ;; # End of flags
    --clearenv) cleared=1; shift ;;
    --setenv) env_args+=("$2=$3"); shift 3 ;;
    --unsetenv) env_args+=(--unset="$2"); shift 2 ;;
    --chdir) chdir="$2"; shift 2 ;;
    -*)
      # Drop one more argument per value the flag takes, then the flag itself
      is_two_value_flag "$1" && shift 2
      is_value_flag "$1" && shift
      shift
      ;;
    *) break ;; # First non-flag token is the command to run
  esac
done

if [[ $# -eq 0 ]]; then
  echo "bwrap shim: no command given" >&2
  exit 2
fi

[[ -n "$chdir" ]] && cd "$chdir"

echo "WARNING: THIS IS NOT REAL BWRAP! UNSAFELY RUNNING exec $*" >&2
if [[ "$cleared" == 1 ]]; then
  exec env -i "${env_args[@]}" "$@"
else
  exec env "${env_args[@]}" "$@"
fi
