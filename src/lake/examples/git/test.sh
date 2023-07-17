set -e

./clean.sh
./package.sh
./build/bin/git_hello
