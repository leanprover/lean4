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
LEAN_THREAD_PTR(expr_array,  g_var_array);
LEAN_THREAD_PTR(expr_array,  g_mref_array);
LEAN_THREAD_PTR(expr_array,  g_href_array);

scope_hash_consing::scope_hash_consing():
    scoped_expr_caching(true) {
    lean_assert(g_var_array   == nullptr);
    lean_assert(g_mref_array  == nullptr);
    lean_assert(g_href_array  == nullptr);
    g_var_array   = new expr_array();
    g_mref_array  = new expr_array();
    g_href_array  = new expr_array();
}

scope_hash_consing::~scope_hash_consing() {
    delete g_var_array;
    delete g_mref_array;
    delete g_href_array;
    g_var_array   = nullptr;
    g_mref_array  = nullptr;
    g_href_array  = nullptr;
}

level mk_level_zero() {
    return lean::mk_level_zero();
}

level mk_level_one() {
    return lean::mk_level_one();
}

level mk_max(level const & l1, level const & l2) {
    lean_assert(is_cached(l1));
    lean_assert(is_cached(l2));
    return lean::mk_max(l1, l2);
}

level mk_imax(level const & l1, level const & l2) {
    lean_assert(is_cached(l1));
    lean_assert(is_cached(l2));
    return lean::mk_max(l1, l2);
}

level mk_succ(level const & l) {
    lean_assert(is_cached(l));
    return lean::mk_succ(l);
}

level mk_param_univ(name const & n) {
    return lean::mk_param_univ(n);
}

level mk_global_univ(name const & n) {
    return lean::mk_global_univ(n);
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

level update_succ(level const & l, level const & new_arg) {
    if (is_eqp(succ_of(l), new_arg))
        return l;
    else
        return blast::mk_succ(new_arg);
}

level update_max(level const & l, level const & new_lhs, level const & new_rhs) {
    if (is_max(l)) {
        if (is_eqp(max_lhs(l), new_lhs) && is_eqp(max_rhs(l), new_rhs))
            return l;
        else
            return blast::mk_max(new_lhs, new_rhs);
    } else {
        if (is_eqp(imax_lhs(l), new_lhs) && is_eqp(imax_rhs(l), new_rhs))
            return l;
        else
            return blast::mk_imax(new_lhs, new_rhs);
    }
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

expr mk_local(name const & n, name const & pp_n, expr const & t, binder_info const & bi) {
    lean_assert(is_cached(t));
    return lean::mk_local(n, pp_n, t, bi);
}

bool is_local(expr const & e) {
    return lean::is_local(e) && mlocal_type(e) != *g_dummy_type;
}

bool has_local(expr const & e) {
    return lean::has_local(e);
}

unsigned local_index(expr const & e) {
    lean_assert(blast::is_local(e));
    return mlocal_name(e).get_numeral();
}

expr const & local_type(expr const & e) {
    lean_assert(blast::is_local(e));
    return mlocal_type(e);
}

expr mk_var(unsigned idx) {
    lean_assert(g_var_array);
    while (g_var_array->size() <= idx) {
        unsigned j   = g_var_array->size();
        expr new_var = lean::mk_var(j);
        g_var_array->push_back(new_var);
    }
    lean_assert(idx < g_var_array->size());
    return (*g_var_array)[idx];
}

expr mk_app(expr const & f, expr const & a) {
    lean_assert(is_cached(f) && is_cached(a));
    return lean::mk_app(f, a);
}

bool is_cached(unsigned num, expr const * args) {
    return std::all_of(args, args+num, [](expr const & e) { return is_cached(e); });
}

expr mk_app(expr const & f, unsigned num_args, expr const * args) {
    lean_assert(is_cached(f) && is_cached(num_args, args));
    return lean::mk_app(f, num_args, args);
}

expr mk_app(unsigned num_args, expr const * args) {
    lean_assert(num_args >= 2);
    return blast::mk_app(blast::mk_app(args[0], args[1]), num_args - 2, args+2);
}

expr mk_rev_app(expr const & f, unsigned num_args, expr const * args) {
    lean_assert(is_cached(f) && is_cached(num_args, args));
    return lean::mk_rev_app(f, num_args, args);
}

expr mk_rev_app(unsigned num_args, expr const * args) {
    lean_assert(num_args >= 2);
    return blast::mk_rev_app(blast::mk_app(args[num_args-1], args[num_args-2]), num_args-2, args);
}

expr mk_sort(level const & l) {
    lean_assert(is_cached(l));
    return lean::mk_sort(l);
}

expr mk_constant(name const & n, levels const & ls) {
    lean_assert(std::all_of(ls.begin(), ls.end(), [](level const & l) { return is_cached(l); }));
    return lean::mk_constant(n, ls);
}

expr mk_binding(expr_kind k, name const & n, expr const & t, expr const & e, binder_info const & bi) {
    lean_assert(is_cached(t) && is_cached(e));
    return lean::mk_binding(k, n, t, e, bi);
}

expr mk_macro(macro_definition const & m, unsigned num, expr const * args) {
    lean_assert(is_cached(num, args));
    return lean::mk_macro(m, num, args);
}

expr update_app(expr const & e, expr const & new_fn, expr const & new_arg) {
    if (!is_eqp(app_fn(e), new_fn) || !is_eqp(app_arg(e), new_arg))
        return blast::mk_app(new_fn, new_arg);
    else
        return e;
}

expr update_binding(expr const & e, expr const & new_domain, expr const & new_body) {
    if (!is_eqp(binding_domain(e), new_domain) || !is_eqp(binding_body(e), new_body))
        return blast::mk_binding(e.kind(), binding_name(e), new_domain, new_body, binding_info(e));
    else
        return e;
}

expr update_sort(expr const & e, level const & new_level) {
    if (!is_eqp(sort_level(e), new_level))
        return blast::mk_sort(new_level);
    else
        return e;
}

expr update_constant(expr const & e, levels const & new_levels) {
    if (!is_eqp(const_levels(e), new_levels))
        return blast::mk_constant(const_name(e), new_levels);
    else
        return e;
}

expr update_local(expr const & e, expr const & new_type) {
    if (!is_eqp(mlocal_type(e), new_type))
        return blast::mk_local(mlocal_name(e), local_pp_name(e), new_type, local_info(e));
    else
        return e;
}

expr update_macro(expr const & e, unsigned num, expr const * args) {
    if (num == macro_num_args(e)) {
        unsigned i = 0;
        for (i = 0; i < num; i++) {
            if (!is_eqp(macro_arg(e, i), args[i]))
                break;
        }
        if (i == num)
            return e;
    }
    return blast::mk_macro(to_macro(e)->get_def(), num, args);
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
