#!/usr/bin/env bash
# Create the snapshot the bench reads. Runs outside the measured binary so the
# save cost isn't conflated with the load cost.
set -euo pipefail
echo "import Lean" > _tmp_incr_header_load_src.lean
lean --incr-header-save=_tmp_incr_header_load.snap _tmp_incr_header_load_src.lean
