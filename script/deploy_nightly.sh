#!/bin/bash

set -exu

[ -z ${LEAN_VERSION_STRING+x} ] && exit 0

if command -v greadlink >/dev/null 2>&1; then
    # macOS readlink doesn't support -f option
    READLINK=greadlink
else
    READLINK=readlink
fi

# Travis can't publish releases to other repos (or stop mucking with the markdown description), so push releases directly
export GOPATH=$($READLINK -f go)
PATH=$PATH:$GOPATH/bin
go get github.com/itchio/gothub

# technically a race condition...
git fetch nightly --tags
if git tag $LEAN_VERSION_STRING
then
    last_tag=$(git describe @^ --abbrev=0 --tags)
    echo -e "Changes since ${last_tag}:\n\n" > diff.md
    git show $last_tag:doc/changes.md > old.md
    ./script/diff_changelogs.py old.md doc/changes.md >> diff.md
    echo -e "*Full commit log*\n" >> diff.md
    git log --oneline $last_tag..HEAD | sed 's/^/* /' >> diff.md
    git push nightly $LEAN_VERSION_STRING
    gothub release -s $GH_TOKEN -u leanprover -r lean-nightly -t $LEAN_VERSION_STRING -d - --pre-release < diff.md
else
    # make sure every runner is building the same commit
    [ $(git rev-parse HEAD) == $(git rev-parse $LEAN_VERSION_STRING) ] || exit 1
fi

gothub upload -s $GH_TOKEN -u leanprover -r lean-nightly -t $LEAN_VERSION_STRING -n "$(basename $1)" -f "$1"
