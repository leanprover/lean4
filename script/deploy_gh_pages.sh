#!/bin/bash
# LEGACY binary in gh-pages branch. Remove when test scripts are changed to use versioned nightlies.
# inspired by https://github.com/steveklabnik/automatically_update_github_pages_with_travis_example

set -eu

rev=$(git rev-parse --short HEAD)

git clone -b gh-pages "https://$GH_TOKEN@github.com/leanprover/lean-nightly.git" gh-pages
cd gh-pages

mkdir -p build
ln -f ../build/lean-* build/

git config user.name "Bot Botson"
git config user.email "bot@bot.bot"

git add -A .
git commit --amend --reset-author -m "nightly build at ${rev}"
git push -fq
