set -ex

./clean.sh

# Test `new`

../../build/bin/lake new helloNew

cd helloNew
test -f lean-toolchain
../../../build/bin/lake build-bin
./build/bin/helloNew
cd ..

# Test `init`

mkdir helloInit

cd helloInit
../../../build/bin/lake init helloInit
../../../build/bin/lake build-bin
./build/bin/helloInit

# Test `init` on existing package (should error)

../../../build/bin/lake init helloInit && exit 1 || true
