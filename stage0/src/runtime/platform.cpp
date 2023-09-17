/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/object.h"
#include "githash.h"

namespace lean {
extern "C" LEAN_EXPORT obj_res lean_system_platform_nbits(obj_arg) {
    if (sizeof(void*) == 8) {
        return box(64);
    } else {
        return box(32);
    }
}

extern "C" LEAN_EXPORT uint8 lean_system_platform_windows(obj_arg) {
#if defined(LEAN_WINDOWS)
    return 1;
#else
    return 0;
#endif
}

extern "C" LEAN_EXPORT uint8 lean_system_platform_osx(obj_arg) {
#if defined(__APPLE__)
    return 1;
#else
    return 0;
#endif
}

extern "C" LEAN_EXPORT uint8 lean_system_platform_emscripten(obj_arg) {
#if defined(LEAN_EMSCRIPTEN)
    return 1;
#else
    return 0;
#endif
}

extern "C" object * lean_get_githash(obj_arg) { return lean_mk_string(LEAN_GITHASH); }
}
