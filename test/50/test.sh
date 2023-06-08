#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../../build/bin/lake}

cd foo

${LAKE} build
echo "# issue 50" | tee ../produced.out
${LAKE} build -KleanArgs=-DwarningAsError=true |& tee -a ../produced.out

${LAKE} build
echo "# issue 172" | tee -a ../produced.out
${LAKE} build -KweakLeanArgs=-DwarningAsError=true |& tee -a ../produced.out

${LAKE} build
echo "# compile args" | tee -a ../produced.out
${LAKE} build -KleancArgs=-DBAR |& tee -a ../produced.out

${LAKE} build
echo "# link args" | tee -a ../produced.out
${LAKE} build -KlinkArgs=-Lbuild/lib |& tee -a ../produced.out

# test
diff --strip-trailing-cr ../expected.out ../produced.out
