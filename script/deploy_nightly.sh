#!/bin/bash

set -eu

[ -n $LEAN_VERSION_STRING ] && gothub upload -s $GH_TOKEN -u leanprover -r lean-nightly -t $LEAN_VERSION_STRING -n "$(basename $1)" -f "$1"
