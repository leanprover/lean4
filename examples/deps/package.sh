set -ex

cd bar
${LAKE:-../../../build/bin/lake} build-bin
cd ..


cd foo
${LAKE:-../../../build/bin/lake} build-bin
cd ..
