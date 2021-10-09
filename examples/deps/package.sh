set -ex

cd bar
${LAKE:-../../../build/bin/lake} build
cd ..


cd foo
${LAKE:-../../../build/bin/lake} build
cd ..
