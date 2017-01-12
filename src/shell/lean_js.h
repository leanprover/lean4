/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
void initialize_emscripten();
void finalize_emscripten();
int emscripten_process_request(uintptr_t msg);
