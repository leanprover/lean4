echo 'testing init'
cd init
./test.sh
cd ..

echo 'testing hello'
cd hello
./test.sh
cd ..

echo 'testing io'
cd io
./test.sh
cd ..

echo 'testing deps'
cd deps
./test.sh
cd ..

echo 'testing git'
cd git
./test.sh
cd ..

echo 'testing ffi'
cd ffi
./test.sh
cd ..

echo "testing bootstrap"
cd bootstrap
./test.sh
cd ..
cd hello
./bootstrap-test.sh
cd ..
