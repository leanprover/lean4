./clean.sh

# Test `new`

../../build/bin/lake new helloNew

cd helloNew
../../../build/bin/lake build-bin
./build/bin/helloNew
cd ..

# Test `init`

mkdir helloInit
cd helloInit
../../../build/bin/lake init helloInit

../../../build/bin/lake build-bin
./build/bin/helloInit
cd ..
