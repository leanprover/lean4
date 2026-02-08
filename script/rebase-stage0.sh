#!/usr/bin/env bash

# This script rebases onto the given branch/commit, and updates
# all `chore: update stage0` commits along the way.

# Whether to use nix or make to update stage0
if [ "$1" = "-nix" ]
then
   export STAGE0_WITH_NIX=true
   shift
fi

# Check if an argument is provided
if [ "$#" -eq 0 ]; then
    echo "Usage: $0 [-nix] <options to git rebase -i>"
    exit 1
fi

REPO_ROOT=$(git rev-parse --show-toplevel)

# Run git rebase in interactive mode, but automatically edit the todo list
# using the defined GIT_SEQUENCE_EDITOR command
GIT_SEQUENCE_EDITOR="$REPO_ROOT/script/lib/rebase-editor.sh" git rebase -i "$@"

