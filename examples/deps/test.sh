set -ex

./clean.sh
./package.sh
./foo/build/bin/foo
./bar/build/bin/bar

cd ./foo
${LAKE:-../../../build/bin/lake} print-paths A B
cd ..
