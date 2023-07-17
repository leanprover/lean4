set -ex

cd bar
${LAKE:-../../../build/bin/lake} build --update
cd ..


cd foo
${LAKE:-../../../build/bin/lake} build --update
cd ..
