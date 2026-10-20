set -euo pipefail

lean_bin=$(command -v lean)

# Rebuild only when a snapshot is missing or older than the `lean` binary, to
# avoid unnecessary recomputation.
for snap in "$LEAN_HEADER_SNAPSHOT_LEAN" "$LEAN_HEADER_SNAPSHOT_INIT"; do
  if [[ ! -f "$snap" || "$lean_bin" -nt "$snap" ]]; then
    needs_rebuild=1
  fi
done
[[ -z "${needs_rebuild:-}" ]] && exit 0

# These options must match those passed by the elab* runners so the saved
# `cmdState` is consistent with what tests will see.
echo 'import Lean' | lean --stdin --incr-header-save="$LEAN_HEADER_SNAPSHOT_LEAN" -DprintMessageEndPos=true -Dlinter.all=false -DElab.inServer=true
echo -n '' | lean --stdin --incr-header-save="$LEAN_HEADER_SNAPSHOT_INIT" -DprintMessageEndPos=true -Dlinter.all=false -DElab.inServer=true
