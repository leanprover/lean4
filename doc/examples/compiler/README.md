In this example, we use the Lean C code generator to construct a simple program.

1- Generate `build/bin/test` program using `leanmake bin` (assuming `bin/` from e.g. the stage 0.5 build directory is in your `PATH`)

2- Execute test program
```
./build/bin/test hello world
```
It should produce `Result: [hello, world]`
