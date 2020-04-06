Small project implemented using Lean and C++.
The C++ file `myfuns.cpp` wraps a C++ object using an `lean_external_object`.
The file `myfuns.cpp` exposes pure and effectful primitives.
The file `main.lean` contains a small Lean program that uses the exported primitives.

Build instructions
=====

The command
```
LEAN_ROOT=<your lean4 directory> make
```
creates the executable `out/test`.

Example:
```
LEAN_ROOT=/Users/leonardodemoura/projects/lean4 make
```

The executable `out/test` should produce the output
```
30
hello
foobla
world
```
