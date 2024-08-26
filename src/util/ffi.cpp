/*
Copyright (c) 2021 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/

#include <lean/lean.h>
#include "runtime/string_ref.h"

namespace lean {
LEAN_EXPORT extern "C" object * lean_get_leanc_extra_flags(object *) {
    return lean_mk_string("@LEANC_EXTRA_FLAGS@");
}

LEAN_EXPORT extern "C" object * lean_get_leanc_internal_flags(object *) {
    return lean_mk_string("@LEANC_INTERNAL_FLAGS@");
}

LEAN_EXPORT extern "C" object * lean_get_linker_flags(uint8 link_static) {
    return lean_mk_string(link_static ? "@LEANC_STATIC_LINKER_FLAGS@ @LEAN_EXTRA_LINKER_FLAGS@" : "@LEANC_SHARED_LINKER_FLAGS@ @LEAN_EXTRA_LINKER_FLAGS@");
}

LEAN_EXPORT extern "C" object * lean_get_internal_linker_flags(object *) {
    return lean_mk_string("@LEANC_INTERNAL_LINKER_FLAGS@");
}
}
