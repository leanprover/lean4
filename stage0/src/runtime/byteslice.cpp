/*
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#include <lean/lean.h>
#include "runtime/byteslice.h"
#include "runtime/io.h"
#include "runtime/object.h"
#include "runtime/thread.h"

namespace lean {

extern "C" LEAN_EXPORT uint8_t lean_byteslice_beq(b_obj_arg a, b_obj_arg b) {
    if (a == b) { return true; }

    lean_object* bytearray_a = lean_ctor_get(a, 0);
    size_t start_a = lean_unbox(lean_ctor_get(a, 1));
    size_t end_a = lean_unbox(lean_ctor_get(a, 2));

    lean_object* bytearray_b = lean_ctor_get(b, 0);
    size_t start_b = lean_unbox(lean_ctor_get(b, 1));
    size_t end_b = lean_unbox(lean_ctor_get(b, 2));

    size_t size_a = end_a - start_a;
    size_t size_b = end_b - start_b;

    if (size_a != size_b) { return false; }

    if (size_a == 0) { return true; }

    const uint8_t* ptr_a = lean_sarray_cptr(bytearray_a) + start_a;
    const uint8_t* ptr_b = lean_sarray_cptr(bytearray_b) + start_b;

    return memcmp(ptr_a, ptr_b, size_a) == 0;
}
}
