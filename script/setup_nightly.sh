#!/bin/bash

set -eu

git remote add nightly "https://$GH_TOKEN@github.com/leanprover/lean-nightly.git"
git fetch nightly

# exit if commit is already tagged
git describe --exact-match --tags HEAD >& /dev/null && return

# Travis can't publish releases to other repos (or stop mucking with the markdown description), so push releases directly
go get github.com/itchio/gothub

if git tag $LEAN_VERSION_STRING
then
    # technically a race condition...
    git push nightly $LEAN_VERSION_STRING
    last_tag=$(git describe @^ --abbrev=0 --tags)
    echo -e "Changes since ${last_tag}:\n\n" > diff.md
    ./script/diff_changelogs.py <(git show $last_tag:doc/changes.md) doc/changes.md >> diff.md
    gothub release -s $GH_TOKEN -u leanprover -r lean-nightly -t $LEAN_VERSION_STRING -d - --pre-release < diff.md
else
    # make sure every runner is building the same commit
    git checkout $LEAN_VERSION_STRING
fi

LEAN_VERSION_STRING="nightly-$(date -uI)"
OPTIONS+="-DLEAN_SPECIAL_VERSION_DESC=$LEAN_VERSION_STRING"
