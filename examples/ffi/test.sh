set -e

./clean.sh
./package.sh
./app/build/bin/app
./lib/build/bin/ffi
