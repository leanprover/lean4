/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <lean/version.h>
#include "library/util.h"
#include "library/constants.h"

namespace lean {
expr mk_unit(level const & l) {
    return mk_constant(get_punit_name(), {l});
}

expr mk_unit_mk(level const & l) {
    return mk_constant(get_punit_unit_name(), {l});
}

static expr * g_bool_true = nullptr;
static expr * g_bool_false = nullptr;

void initialize_bool() {
    g_bool_false = new expr(mk_constant(get_bool_false_name()));
    mark_persistent(g_bool_false->raw());
    g_bool_true = new expr(mk_constant(get_bool_true_name()));
    mark_persistent(g_bool_true->raw());
}

void finalize_bool() {
    delete g_bool_false;
    delete g_bool_true;
}

expr mk_bool_true() { return *g_bool_true; }
expr mk_bool_false() { return *g_bool_false; }

static std::string * g_short_version_string = nullptr;
std::string const & get_short_version_string() { return *g_short_version_string; }

void initialize_library_util() {
    initialize_bool();

    g_short_version_string = new std::string(LEAN_VERSION_STRING);
}

void finalize_library_util() {
    finalize_bool();
}
}
