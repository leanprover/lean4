set -ex

cd app
${LAKE:-../../../build/bin/lake} build
cd ..


cd lib
${LAKE:-../../../build/bin/lake} build
cd ..
