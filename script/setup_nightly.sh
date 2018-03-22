#!/bin/bash

set -exu

git remote add nightly "https://$GH_TOKEN@github.com/leanprover/lean-nightly.git"
git fetch nightly --tags

# do nothing if commit is already tagged
if [ ! git describe --exact-match --tags HEAD >& /dev/null ]
then
    LEAN_VERSION_STRING="nightly-$(date -uI)"
    OPTIONS+=" -DLEAN_SPECIAL_VERSION_DESC=$LEAN_VERSION_STRING"
fi
