#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../../build/bin/lake}

cd foo

${LAKE} build
echo "# issue 50" | tee ../produced.out
${LAKE} build -KleanArgs=-DwarningAsError=true | tee -a ../produced.out

${LAKE} build
echo "# issue 172" | tee -a ../produced.out
${LAKE} build -KweakLeanArgs=-DwarningAsError=true | tee -a ../produced.out

${LAKE} build
echo "# compile args" | tee -a ../produced.out
# Use `head -n1` to avoid extranous warnings on Windows with current Lean (8/1/23)
${LAKE} build -KleancArgs=-DBAR | head -n1 | tee -a ../produced.out

${LAKE} build
echo "# link args" | tee -a ../produced.out
# Use `head -n1` to avoid extranous warnings on MacOS with current Lean (6/8/23)
${LAKE} build -KlinkArgs=-Lbuild/lib | head -n1 | tee -a ../produced.out

# test
if [ "$OS" = Windows_NT ]; then
  sed -i 's/.exe//g' ../produced.out
  diff --strip-trailing-cr ../expected.out ../produced.out
else
  diff ../expected.out ../produced.out
fi
