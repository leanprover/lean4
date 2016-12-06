/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include "library/native_compiler/native_compiler.h"
#include "library/native_compiler/extern.h"

namespace lean {
void initialize_native_compiler_module() {
    initialize_native_compiler();
    initialize_extern_attribute();
}

void finalize_native_compiler_module() {
    finalize_extern_attribute();
    finalize_native_compiler();
}
}
