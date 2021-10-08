set -e

./clean.sh
./package.sh
./build/bin/ffi
