/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "shell/lean_js.h"
#include <iostream>
#include <string>
#include <emscripten.h>

extern "C" {
EMSCRIPTEN_KEEPALIVE
void lean_init() {
    initialize_emscripten();
}

EMSCRIPTEN_KEEPALIVE
int lean_process_request(uintptr_t msg) {
    return emscripten_process_request(msg);
}
}

int main() {
    return 0;
}

