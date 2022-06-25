set -e

./clean.sh
./package.sh
./app/build/bin/app
./lib/build/bin/test

cd app # Library loading needs this; TODO: fix this
${LAKE:-../../../build/bin/lake} build Test
