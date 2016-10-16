/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "shell/lean_js.h"

#if defined(LEAN_EMSCRIPTEN)

#include <emscripten/bind.h>
EMSCRIPTEN_BINDINGS(LEAN_JS) {
        emscripten::function("lean_init", &initialize_emscripten);
        emscripten::function("lean_import_module", &emscripten_import_module);
        emscripten::function("lean_process_file", &emscripten_process_file);
}

int main() { return 0; }

#else

int main(int, char **) {
    initialize_emscripten();
    emscripten_import_module("standard");
}

#endif
