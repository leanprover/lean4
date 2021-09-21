set -ex

./clean.sh

# Test `new`

${LAKE:-../../build/bin/lake} new helloNew

cd helloNew
test -f lean-toolchain
${LAKE:-../../../build/bin/lake} build-bin
./build/bin/helloNew
cd ..

# Test `init`

mkdir helloInit

cd helloInit
${LAKE:-../../../build/bin/lake} init helloInit
${LAKE:-../../../build/bin/lake} build-bin
./build/bin/helloInit

# Test `init` on existing package (should error)

${LAKE:-../../../build/bin/lake} init helloInit && exit 1 || true
