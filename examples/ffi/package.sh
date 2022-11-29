set -ex

cd app
${LAKE:-../../../build/bin/lake} build -v -U
cd ..


cd lib
${LAKE:-../../../build/bin/lake} build -v
cd ..
