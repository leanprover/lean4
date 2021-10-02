set -ex

# TODO: flip and fix example (deep deps are currently broken)

cd foo
${LAKE:-../../../build/bin/lake} build-bin
cd ..

cd bar
${LAKE:-../../../build/bin/lake} build-bin
cd ..
