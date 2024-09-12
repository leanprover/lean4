#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

unamestr=`uname`
if [ "$unamestr" = Darwin ] || [ "$unamestr" = FreeBSD ]; then
  sed_i() { sed -i '' "$@"; }
else
  sed_i() { sed -i "$@"; }
fi

./clean.sh

# Test that changing `moreLean/Leanc/LinkArgs` triggers a rebuild
# Test that changing `weakLean/Leanc/LinkArgs` does not

${LAKE} build +Hello -R
# see https://github.com/leanprover/lake/issues/50
${LAKE} build +Hello -R -KleanArgs=-DwarningAsError=true -v | grep --color warningAsError

${LAKE} build +Hello -R
# see https://github.com/leanprover/lake/issues/172
${LAKE} build +Hello -R -KweakLeanArgs=-DwarningAsError=true --no-build

${LAKE} build +Hello:o -R
${LAKE} build +Hello:o -R -KleancArgs=-DBAR -v | grep --color leanc

${LAKE} build +Hello:o -R
${LAKE} build +Hello:o -R -KweakLeancArgs=-DBAR --no-build

${LAKE} build +Hello:dynlib Hello:shared hello -R
${LAKE} build +Hello:dynlib -R -KlinkArgs=-L.lake/build/lib -v | grep --color leanc
${LAKE} build Hello:shared -R -KlinkArgs=-L.lake/build/lib -v | grep --color leanc
${LAKE} build hello -R -KlinkArgs=-L.lake/build/lib -v | grep --color leanc

${LAKE} build +Hello:dynlib Hello:shared hello  -R
${LAKE} build +Hello:dynlib -R -KweakLinkArgs=-L.lake/build/lib  --no-build
${LAKE} build Hello:shared -R -KweakLinkArgs=-L.lake/build/lib  --no-build
${LAKE} build hello -R -KweakLinkArgs=-L.lake/build/lib  --no-build

