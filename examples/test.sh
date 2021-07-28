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

echo 'testing ext'
cd ext
./test.sh
cd ..
