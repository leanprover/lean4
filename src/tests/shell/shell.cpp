/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/test.h"
#include "shell/emscripten.h"
using namespace lean;

int main() {
    save_stack_info();
    initialize_emscripten();
    emscripten_import_module("standard");
    int r = emscripten_process_file("file1.lean");
    if (r != 0)
        return r;
    r = emscripten_process_file("file2.lean");
    if (r != 0)
        return r;
    r = has_violations() ? 1 : 0;
    finalize_emscripten();
    return r;
}
