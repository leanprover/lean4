#!/bin/bash

set -exu

[ -z $LEAN_VERSION_STRING] && exit 0

# Travis can't publish releases to other repos (or stop mucking with the markdown description), so push releases directly
GO_PATH=$(realpath go)
PATH=$PATH:$GO_PATH/bin
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
    [ $(git parse-rev HEAD) == $(git parse-rev $LEAN_VERSION_STRING) ] || exit 1
fi

gothub upload -s $GH_TOKEN -u leanprover -r lean-nightly -t $LEAN_VERSION_STRING -n "$(basename $1)" -f "$1"
