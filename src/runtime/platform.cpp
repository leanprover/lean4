/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/object.h"

namespace lean {
extern "C" obj_res lean_system_platform_nbits(obj_arg) {
    if (sizeof(void*) == 8) {
        return box(64);
    } else {
        return box(32);
    }
}

extern "C" uint8 lean_system_platform_windows(obj_arg) {
#if defined(LEAN_WINDOWS)
    return 1;
#else
    return 0;
#endif
}

void initialize_platform() {}
void finalize_platform() {}
}
