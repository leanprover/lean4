/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <string>
#include "shell/lean_js.h"

#if defined(LEAN_EMSCRIPTEN)

#include <emscripten/bind.h>
EMSCRIPTEN_BINDINGS(LEAN_JS) {
        emscripten::function("lean_init", &initialize_emscripten);
        emscripten::function("lean_process_request", &emscripten_process_request, emscripten::allow_raw_pointers());
}

int main() { return 0; }

#else

int main() {
    initialize_emscripten();
    while (true) {
        std::string req_string;
        std::getline(std::cin, req_string);
        if (std::cin.eof()) return 0;
        emscripten_process_request(reinterpret_cast<uintptr_t>(req_string.c_str()));
    }
}

#endif
