set -e

./clean.sh
./package.sh
./foo/build/bin/foo
./bar/build/bin/bar
