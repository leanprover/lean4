set -ex

cd app
${LAKE:-../../../.lake/build/bin/lake} build -v -U
cd ..


cd lib
${LAKE:-../../../.lake/build/bin/lake} build -v
cd ..
