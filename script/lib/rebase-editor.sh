#!/usr/bin/env bash


# Script internal to `./script/rebase-stage0.sh`

# Determine OS type for sed in-place editing
SED_CMD=("sed" "-i")
if [[ "$OSTYPE" == "darwin"* ]]
then
    # macOS requires an empty string argument with -i for in-place editing
    SED_CMD=("sed" "-i" "")
fi

if [ "$STAGE0_WITH_NIX" = true ]
then
  "${SED_CMD[@]}" '/chore: update stage0/ s,.*,x nix run .#update-stage0-commit,' "$1"
else
  "${SED_CMD[@]}" '/chore: update stage0/ s,.*,x make -j32 -C build/release update-stage0 \&\& git commit -m "chore: update stage0",' "$1"
fi
