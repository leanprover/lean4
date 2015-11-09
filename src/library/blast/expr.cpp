/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <unordered_set>
#include "util/interrupt.h"
#include "kernel/expr_eq_fn.h"
#include "kernel/replace_cache.h"
#include "kernel/cache_stack.h"
#include "kernel/instantiate_univ_cache.h"
#include "library/blast/expr.h"

namespace lean {
namespace blast {
static name * g_prefix = nullptr;
static expr * g_dummy_type = nullptr; // dummy type for href/mref

level mk_uref(unsigned idx) {
    return lean::mk_meta_univ(name(*g_prefix, idx));
}

bool is_uref(level const & l) {
    return is_meta(l) && meta_id(l).is_numeral();
}

unsigned uref_index(level const & l) {
    lean_assert(is_uref(l));
    return meta_id(l).get_numeral();
}

expr mk_href(unsigned idx) {
    return lean::mk_local(name(*g_prefix, idx), *g_dummy_type);
}

bool is_href(expr const & e) {
    return lean::is_local(e) && mlocal_type(e) == *g_dummy_type;
}

expr mk_mref(unsigned idx) {
    return mk_metavar(name(*g_prefix, idx), *g_dummy_type);
}

bool is_mref(expr const & e) {
    return is_metavar(e) && mlocal_type(e) == *g_dummy_type;
}

unsigned mref_index(expr const & e) {
    lean_assert(is_mref(e));
    return mlocal_name(e).get_numeral();
}

unsigned href_index(expr const & e) {
    lean_assert(is_href(e));
    return mlocal_name(e).get_numeral();
}

bool has_href(expr const & e) {
    return lean::has_local(e);
}

bool has_mref(expr const & e) {
    return lean::has_expr_metavar(e);
}

LEAN_THREAD_VALUE(unsigned, m_next_uref_idx, 0);
LEAN_THREAD_VALUE(unsigned, m_next_mref_idx, 0);
LEAN_THREAD_VALUE(unsigned, m_next_href_idx, 0);

unsigned mk_uref_idx() {
    unsigned r = m_next_uref_idx;
    m_next_uref_idx++;
    return r;
}

unsigned mk_mref_idx() {
    unsigned r = m_next_mref_idx;
    m_next_mref_idx++;
    return r;
}

unsigned mk_href_idx() {
    unsigned r = m_next_href_idx;
    m_next_href_idx++;
    return r;
}

void init_uref_mref_href_idxs() {
    m_next_uref_idx = 0;
    m_next_mref_idx = 0;
    m_next_href_idx = 0;
}

void initialize_expr() {
    g_prefix     = new name(name::mk_internal_unique_name());
    g_dummy_type = new expr(mk_constant(*g_prefix));
}

void finalize_expr() {
    delete g_prefix;
    delete g_dummy_type;
}
}}
