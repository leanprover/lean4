set -ex

./clean.sh
${LAKE:-../../build/bin/lake} build
