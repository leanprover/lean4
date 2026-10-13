#!/usr/bin/env bash
# Capture each manifest Lake hands us into $CAPTURE_DIR (keyed by job_id),
# then act as a passthrough — exec exactly what Lake would have run — so
# the build proceeds to downstream modules and we capture one manifest
# per lean job.
set -euo pipefail

m="$1"
job_id=$(jq -r '.job_id' "$m")
cp "$m" "$CAPTURE_DIR/$job_id.json"

cmd=$(jq -r '.cmd' "$m")
mapfile -t args < <(jq -r '.args[]' "$m")
mapfile -t env_kvs < <(jq -r '.env | to_entries[] | "\(.key)=\(.value)"' "$m")
cwd=$(jq -r '.cwd // ""' "$m")

if [[ -n "$cwd" ]]; then
  cd "$cwd"
fi
exec env "${env_kvs[@]}" "$cmd" "${args[@]}"
