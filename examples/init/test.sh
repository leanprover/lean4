set -ex

./clean.sh

# Test `new`

${LAKE:-../../build/bin/lake} new hello.world

cd hello-world
test -f lean-toolchain
${LAKE:-../../../build/bin/lake} build-bin
./build/bin/hello-world
cd ..

# Test `init`

mkdir hello_world

cd hello_world
${LAKE:-../../../build/bin/lake} init hello_world
${LAKE:-../../../build/bin/lake} build-bin
./build/bin/hello_world

# Test `init` on existing package (should error)

${LAKE:-../../../build/bin/lake} init hello_world && exit 1 || true
