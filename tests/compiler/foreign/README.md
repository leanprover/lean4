Small project implemented using Lean and C++.
The C++ file `myfuns.cpp` wraps a C++ object using an `lean_external_object`.
The file `myfuns.cpp` exposes pure and effectful primitives.
The file `Main.lean` contains a small Lean program that uses the exported primitives.

Build instructions
=====

Assuming the Lean `bin/` directory (e.g. from `build/release/stage1`) is in your `PATH`,
executing `leanmake build/bin/test` will create the executable `build/bin/test`; see the
`Makefile` for further variants.

The executable `build/bin/test` should produce the output
```
30
hello
foobla
world
```
