/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/sstream.h"
#include "library/annotation.h"
#include "library/explicit.h"
#include "library/pos_info_provider.h"

namespace lean {
static name * g_explicit_name = nullptr;
static name * g_partial_explicit_name = nullptr;
static name * g_as_atomic_name = nullptr;
static name * g_as_is_name    = nullptr;

expr mk_explicit(expr const & e) { return mk_annotation(*g_explicit_name, e); }
bool is_explicit(expr const & e) { return is_annotation(e, *g_explicit_name); }
bool is_nested_explicit(expr const & e) { return is_nested_annotation(e, *g_explicit_name); }
expr const & get_explicit_arg(expr const & e) { lean_assert(is_explicit(e)); return get_annotation_arg(e); }

expr mk_partial_explicit(expr const & e) { return mk_annotation(*g_partial_explicit_name, e); }
bool is_partial_explicit(expr const & e) { return is_annotation(e, *g_partial_explicit_name); }
bool is_nested_partial_explicit(expr const & e) { return is_nested_annotation(e, *g_partial_explicit_name); }
expr const & get_partial_explicit_arg(expr const & e) { lean_assert(is_partial_explicit(e)); return get_annotation_arg(e); }

bool is_explicit_or_partial_explicit(expr const & e) { return is_explicit(e) || is_partial_explicit(e); }
expr get_explicit_or_partial_explicit_arg(expr const & e) { lean_assert(is_explicit_or_partial_explicit(e)); return get_annotation_arg(e); }

expr mk_as_is(expr const & e) { lean_assert(!contains_pos(e)); return mk_annotation(*g_as_is_name, e); }
bool is_as_is(expr const & e) { return is_annotation(e, *g_as_is_name); }
expr const & get_as_is_arg(expr const & e) { lean_assert(is_as_is(e)); return get_annotation_arg(e); }

expr mk_as_atomic(expr const & e) { return mk_annotation(*g_as_atomic_name, e); }
bool is_as_atomic(expr const & e) { return is_annotation(e, *g_as_atomic_name); }
expr const & get_as_atomic_arg(expr const & e) { lean_assert(is_as_atomic(e)); return get_annotation_arg(e); }

void initialize_explicit() {
    g_explicit_name         = new name("@");
    g_partial_explicit_name = new name("@@");
    g_as_atomic_name        = new name("as_atomic");
    g_as_is_name            = new name("as_is");

    register_annotation(*g_explicit_name);
    register_annotation(*g_partial_explicit_name);
    register_annotation(*g_as_atomic_name);
    register_annotation(*g_as_is_name);
}

void finalize_explicit() {
    delete g_as_is_name;
    delete g_as_atomic_name;
    delete g_partial_explicit_name;
    delete g_explicit_name;
}
}
