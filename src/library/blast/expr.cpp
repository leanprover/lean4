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

#ifndef LEAN_BLAST_INST_UNIV_CACHE_SIZE
#define LEAN_BLAST_INST_UNIV_CACHE_SIZE 1023
#endif

namespace lean {
namespace blast {
static name * g_prefix = nullptr;
static expr * g_dummy_type = nullptr; // dummy type for href/mref

typedef typename std::vector<expr> expr_array;
LEAN_THREAD_PTR(expr_array,  g_mref_array);
LEAN_THREAD_PTR(expr_array,  g_href_array);

scope_hash_consing::scope_hash_consing():
    scoped_expr_caching(true) {
    lean_assert(g_mref_array  == nullptr);
    lean_assert(g_href_array  == nullptr);
    g_mref_array  = new expr_array();
    g_href_array  = new expr_array();
}

scope_hash_consing::~scope_hash_consing() {
    delete g_mref_array;
    delete g_href_array;
    g_mref_array  = nullptr;
    g_href_array  = nullptr;
}

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

static expr mk_href_core(unsigned idx) {
    return lean::mk_local(name(*g_prefix, idx), *g_dummy_type);
}

expr mk_href(unsigned idx) {
    lean_assert(g_href_array);
    while (g_href_array->size() <= idx) {
        unsigned j   = g_href_array->size();
        expr new_ref = mk_href_core(j);
        g_href_array->push_back(new_ref);
    }
    lean_assert(idx < g_href_array->size());
    return (*g_href_array)[idx];
}

bool is_href(expr const & e) {
    return lean::is_local(e) && mlocal_type(e) == *g_dummy_type;
}

static expr mk_mref_core(unsigned idx) {
    return mk_metavar(name(*g_prefix, idx), *g_dummy_type);
}

expr mk_mref(unsigned idx) {
    lean_assert(g_mref_array);
    while (g_mref_array->size() <= idx) {
        unsigned j   = g_mref_array->size();
        expr new_ref = mk_mref_core(j);
        g_mref_array->push_back(new_ref);
    }
    lean_assert(idx < g_mref_array->size());
    return (*g_mref_array)[idx];
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

void initialize_expr() {
    g_prefix     = new name(name::mk_internal_unique_name());
    g_dummy_type = new expr(mk_constant(*g_prefix));
}

void finalize_expr() {
    delete g_prefix;
    delete g_dummy_type;
}
}}
