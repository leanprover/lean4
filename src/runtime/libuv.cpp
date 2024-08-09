/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Markus Himmel
*/
#include "runtime/libuv.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>

extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg o) {
    return lean_unsigned_to_nat(uv_version());
}

#else

extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg o) {
    return lean_box(0);
}

#endif
