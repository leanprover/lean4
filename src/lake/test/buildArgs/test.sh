#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../build/bin/lake}

./clean.sh

${LAKE} build
echo "# issue 50" > produced.out
${LAKE} build -R -KleanArgs=-DwarningAsError=true | tee -a produced.out

${LAKE} build -R
echo "# issue 172" >> produced.out
${LAKE} build -R -KweakLeanArgs=-DwarningAsError=true | tee -a produced.out

${LAKE} build -R
echo "# compile args" >> produced.out
# Use `head -n1` to avoid extranous warnings on Windows with current Lean (8/1/23)
${LAKE} build -R -KleancArgs=-DBAR | head -n1 | tee -a produced.out

${LAKE} build -R
echo "# link args" >> produced.out
# Use `head -n1` to avoid extranous warnings on MacOS with current Lean (6/8/23)
${LAKE} build -R -KlinkArgs=-Lbuild/lib | head -n1 | tee -a produced.out

# test
if [ "$OS" = Windows_NT ]; then
  sed -i 's/.exe//g' produced.out
  diff --strip-trailing-cr expected.out produced.out
else
  diff expected.out produced.out
fi
