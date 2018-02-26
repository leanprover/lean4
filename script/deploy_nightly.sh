#!/bin/bash

set -eu

# stable build?
if [ -z $LEAN_VERSION_STRING ]; then exit; fi

rev=$(git rev-parse --short HEAD)

git config user.name "Bot Botson"
git config user.email "bot@bot.bot"

git remote add nightly "https://$GH_TOKEN@github.com/leanprover/lean-nightly.git"
git fetch nightly

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
fi

if [ $rev = $(git rev-parse --short $LEAN_VERSION_STRING) ]
then
    gothub upload -s $GH_TOKEN -u leanprover -r lean-nightly -t $LEAN_VERSION_STRING -n "$(basename $1)" -f "$1"
fi

# LEGACY binary in gh-pages branch. Remove when test scripts are changed to use versioned nightlies.
# inspired by https://github.com/steveklabnik/automatically_update_github_pages_with_travis_example

git checkout -b gh-pages nightly/gh-pages
cd gh-pages

mkdir -p build
ln -f ../build/lean-* build/

git add -A .
git commit --amend --reset-author -m "nightly build at ${rev}"
git push -fq
