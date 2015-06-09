/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "library/idx_metavar.h"

#ifndef LEAN_INSTANTIATE_METAIDX_CACHE_CAPACITY
#define LEAN_INSTANTIATE_METAIDX_CACHE_CAPACITY 1024*8
#endif

namespace lean {
static name * g_tmp_prefix = nullptr;

void initialize_idx_metavar() {
    g_tmp_prefix = new name(name::mk_internal_unique_name());
}

void finalize_idx_metavar() {
    delete g_tmp_prefix;
}

level mk_idx_metauniv(unsigned i) {
    return mk_meta_univ(name(*g_tmp_prefix, i));
}

expr mk_idx_metavar(unsigned i, expr const & type) {
    return mk_metavar(name(*g_tmp_prefix, i), type);
}

bool is_idx_metauniv(level const & l) {
    if (!is_meta(l))
        return false;
    name const & n = meta_id(l);
    return !n.is_atomic() && n.is_numeral() && n.get_prefix() == *g_tmp_prefix;
}

unsigned to_meta_idx(level const & l) {
    lean_assert(is_idx_metauniv(l));
    return meta_id(l).get_numeral();
}

bool is_idx_metavar(expr const & e) {
    if (!is_metavar(e))
        return false;
    name const & n = mlocal_name(e);
    return !n.is_atomic() && n.is_numeral() && n.get_prefix() == *g_tmp_prefix;
}

unsigned to_meta_idx(expr const & e) {
    lean_assert(is_idx_metavar(e));
    return mlocal_name(e).get_numeral();
}
}
