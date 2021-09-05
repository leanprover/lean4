set -e

./clean.sh
./package.sh
./build/bin/lake --version
