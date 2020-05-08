In this example, we use the Lean C code generator to construct a simple program.

1- Generate `build/bin/test` program using `leanmake` (assuming `bin` from e.g. the stage1 build directory is in your `PATH`)
```
leanmake bin PKG=test
```

2- Execute test program
```
./build/bin/test hello world
```
It should produce `Result: [hello, world]`
