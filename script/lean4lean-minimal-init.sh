#!/usr/bin/env bash
set -euo pipefail

# Adds the internal `-linitialize_minimal` flag to the `lean4lean` executable's link arguments

if ! grep -q initialize_minimal lakefile.toml; then
  awk '{ print }
    /^\[\[lean_exe\]\]$/ && !done { print "moreLinkArgs = [\"-linitialize_minimal\"]"; done = 1 }
  ' lakefile.toml > lakefile.toml.new
  mv lakefile.toml.new lakefile.toml
fi

grep -q initialize_minimal lakefile.toml ||
  { echo "lean4lean-minimal-init.sh: could not add -linitialize_minimal to lakefile.toml" >&2; exit 1; }
