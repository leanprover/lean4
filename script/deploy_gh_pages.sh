#!/bin/bash
# inspired by https://github.com/steveklabnik/automatically_update_github_pages_with_travis_example

set -eu

rev=$(git rev-parse --short HEAD)


git clone -b gh-pages "https://$GH_TOKEN@github.com/$TRAVIS_REPO_SLUG.git" gh-pages
cd gh-pages

# "build/lean-3.2.0-linux.tar.gz" ~> "build/lean-nightly-linux.tar.gz"
NIGHTLY_TARGET=${TARGET/-*-/-nightly-}
mkdir -p build
ln -f ../$NIGHTLY_TARGET $NIGHTLY_TARGET

git config user.name "Bot Botson"
git config user.email "bot@bot.bot"

git add -A .
git commit --amend -m "nightly build at ${rev}"
git push -fq
