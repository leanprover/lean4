#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../build/bin/lake}

if [ "`uname`" = Darwin ]; then
  sed_i() { sed -i '' "$@"; }
else
  sed_i() { sed -i "$@"; }
fi

./clean.sh

# Test that changing `moreLean/Leanc/LinkArgs` triggers a rebuild
# Test that changing `weakLean/Leanc/LinkArgs` does not

${LAKE} build +Hello -R
# see https://github.com/leanprover/lake/issues/50
echo "# lean args" > produced.out
${LAKE} build +Hello -R -KleanArgs=-DwarningAsError=true | tee -a produced.out

${LAKE} build +Hello -R
# see https://github.com/leanprover/lake/issues/172
echo "# weak lean args" >> produced.out
${LAKE} build +Hello -R -KweakLeanArgs=-DwarningAsError=true | tee -a produced.out

${LAKE} build +Hello:o -R
echo "# compile args" >> produced.out
# Use `head -n1` to avoid extraneous warnings on Windows with current Lean (8/1/23)
${LAKE} build +Hello:o -R -KleancArgs=-DBAR | head -n1 | tee -a produced.out

${LAKE} build +Hello:o -R
echo "# weak compile args" >> produced.out
${LAKE} build +Hello:o -R -KweakLeancArgs=-DBAR | tee -a produced.out

${LAKE} build +Hello:dynlib Hello:shared hello -R
echo "# link args" >> produced.out
# Use `head -n1` to avoid extraneous warnings on MacOS with current Lean (6/8/23)
${LAKE} build +Hello:dynlib -R -KlinkArgs=-Lbuild/lib | head -n1 | tee -a produced.out
${LAKE} build Hello:shared -R -KlinkArgs=-Lbuild/lib | head -n1 | tee -a produced.out
${LAKE} build hello -R -KlinkArgs=-Lbuild/lib | head -n1 | tee -a produced.out

${LAKE} build +Hello:dynlib Hello:shared hello  -R
echo "# weak link args" >> produced.out
${LAKE} build +Hello:dynlib -R -KweakLinkArgs=-Lbuild/lib | tee -a produced.out
${LAKE} build Hello:shared -R -KweakLinkArgs=-Lbuild/lib | tee -a produced.out
${LAKE} build hello -R -KweakLinkArgs=-Lbuild/lib | tee -a produced.out

# check output against the expected output
sed_i 's/lib//g' produced.out # remove lib prefixes
sed_i 's/\..*//g' produced.out # remove extensions
diff --strip-trailing-cr expected.out produced.out

