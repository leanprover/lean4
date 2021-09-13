set -ex

./clean.sh

# Test `new`

../../build/bin/Lake new helloNew

cd helloNew
../../../build/bin/Lake build-bin
./build/bin/helloNew
cd ..

# Test `init`

mkdir helloInit
cd helloInit
../../../build/bin/Lake init helloInit

../../../build/bin/Lake build-bin
./build/bin/helloInit
