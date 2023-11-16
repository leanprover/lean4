set -ex

./clean.sh
./package.sh
./app/.lake/build/bin/app
./lib/.lake/build/bin/test

${LAKE:-../../.lake/build/bin/lake} -d app build -v Test
