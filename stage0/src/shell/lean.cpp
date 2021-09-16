/*
Copyright (c) 2021 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/

// The actual main function is in `util/shell.cpp` and compiled into `libleanshared` to avoid issues with cross-lib C++.
// It will eventually be replaced by Lean code anyway.
// We put `main` in this separate file included only in `lean` so linking against `libleanshared` does not accidentally use it.

extern "C" int lean_main(int argc, char ** argv);

int main(int argc, char ** argv) {
    return lean_main(argc, argv);
}
