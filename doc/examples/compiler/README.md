In this example, we use the Lean C++ code generator to construct a simple program.

1- Generate `test.cpp`. Remark: we must have the file `leanpkg.path` in the current directory.
```
../../../bin/lean --cpp=test.cpp test.lean
```

2- Generate `test` program using `g++` or `clang++`
```
g++ -o test --std=c++11 -I ../../../src test.cpp ../../../bin/libleanstatic.a -lgmp -pthread
```
Remark: if you built `libleanstatic.a` using jemalloc, you also need to include option `-ljemalloc` in the previous step.

3- Execute test program
```
./test hello world
```
It should produce `Result: [hello, world]`
