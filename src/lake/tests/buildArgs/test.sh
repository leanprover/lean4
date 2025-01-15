#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Test that changing `moreLean/Leanc/LinkArgs` triggers a rebuild
# Test that changing `weakLean/Leanc/LinkArgs` does not

# Test `leanArgs`
${LAKE} build +Hello -R
# see https://github.com/leanprover/lake/issues/50
${LAKE} build +Hello -R -KleanArgs=-DwarningAsError=true -v | grep --color warningAsError

# Test `weakLeanArgs`
${LAKE} build +Hello -R
# see https://github.com/leanprover/lake/issues/172
${LAKE} build +Hello -R -KweakLeanArgs=-DwarningAsError=true --no-build

# Test `leancArgs`
${LAKE} build +Hello:o -R
${LAKE} build +Hello:o -R -KleancArgs=-DBAR -v | grep --color "Built Hello:c.o"

# Test `weakLeancArgs`
${LAKE} build +Hello:o -R
${LAKE} build +Hello:o -R -KweakLeancArgs=-DBAR --no-build

# Test `linkArgs`
${LAKE} build +Hello:dynlib Hello:shared hello -R
${LAKE} build +Hello:dynlib -R -KlinkArgs=-L.lake/build/lib -v | grep --color "Built Hello:dynlib"
${LAKE} build Hello:shared -R -KlinkArgs=-L.lake/build/lib -v | grep --color "Built Hello:shared"
${LAKE} build hello -R -KlinkArgs=-L.lake/build/lib -v | grep --color "Built hello"

# Test `weakLinkArgs`
${LAKE} build +Hello:dynlib Hello:shared hello  -R
${LAKE} build +Hello:dynlib -R -KweakLinkArgs=-L.lake/build/lib  --no-build
${LAKE} build Hello:shared -R -KweakLinkArgs=-L.lake/build/lib  --no-build
${LAKE} build hello -R -KweakLinkArgs=-L.lake/build/lib  --no-build
