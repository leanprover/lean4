#!/usr/bin/env bash
# Trivial passthrough wrapper for `$LAKE_WRAPPED_EXEC`:
# read the manifest at argv[1], exec exactly what Lake would have run.
# A build under this wrapper must be byte-for-byte identical to a build
# without `$LAKE_WRAPPED_EXEC` set at all.
set -euo pipefail

m="$1"
cmd=$(jq -r '.cmd' "$m")
mapfile -t args < <(jq -r '.args[]' "$m")
mapfile -t env_kvs < <(jq -r '.env | to_entries[] | "\(.key)=\(.value)"' "$m")
cwd=$(jq -r '.cwd // ""' "$m")

if [[ -n "$cwd" ]]; then
  cd "$cwd"
fi
exec env "${env_kvs[@]}" "$cmd" "${args[@]}"
