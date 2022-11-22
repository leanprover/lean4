set -ex

cd app
${LAKE:-../../../build/bin/lake} update -v
${LAKE:-../../../build/bin/lake} build -v
cd ..


cd lib
${LAKE:-../../../build/bin/lake} build -v
cd ..
