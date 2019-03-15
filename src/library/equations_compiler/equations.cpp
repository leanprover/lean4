/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "runtime/sstream.h"
#include "util/list_fn.h"
#include "util/fresh_name.h"
#include "kernel/expr.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"
#include "kernel/replace_fn.h"
#include "library/error_msgs.h"
#include "library/exception.h"
#include "library/io_state_stream.h"
#include "library/annotation.h"
#include "library/util.h"
#include "library/locals.h"
#include "library/constants.h"
#include "library/pp_options.h"
#include "library/equations_compiler/equations.h"

namespace lean {
static name * g_equations_name                 = nullptr;
static name * g_equation_name                  = nullptr;
static name * g_no_equation_name               = nullptr;
static name * g_inaccessible_name              = nullptr;
static name * g_equations_result_name          = nullptr;
static name * g_as_pattern_name                = nullptr;

bool operator==(equations_header const & h1, equations_header const & h2) {
    return
        h1.m_num_fns == h2.m_num_fns &&
        h1.m_fn_names == h2.m_fn_names &&
        h1.m_fn_actual_names == h2.m_fn_actual_names &&
        h1.m_is_private == h2.m_is_private &&
        h1.m_is_lemma == h2.m_is_lemma &&
        h1.m_is_unsafe == h2.m_is_unsafe &&
        h1.m_is_noncomputable == h2.m_is_noncomputable &&
        h1.m_aux_lemmas == h2.m_aux_lemmas &&
        h1.m_prev_errors == h2.m_prev_errors &&
        h1.m_gen_code == h2.m_gen_code;
}

static kvmap * g_as_pattern = nullptr;
static kvmap * g_equation                  = nullptr;
static kvmap * g_equation_ignore_if_unused = nullptr;
static kvmap * g_no_equation               = nullptr;

expr mk_equation(expr const & lhs, expr const & rhs, bool ignore_if_unused) {
    if (ignore_if_unused)
        return mk_mdata(*g_equation_ignore_if_unused, mk_app(lhs, rhs));
    else
        return mk_mdata(*g_equation, mk_app(lhs, rhs));
}
expr mk_no_equation() { return mk_mdata(*g_no_equation, mk_Prop()); }

bool is_equation(expr const & e) {
    expr e2 = unwrap_pos(e);
    return is_mdata(e2) && get_bool(mdata_data(e2), *g_equation_name);
}

bool ignore_equation_if_unused(expr const & e) {
    lean_assert(is_equation(e));
    return *get_bool(mdata_data(unwrap_pos(e)), *g_equation_name);
}

bool is_lambda_equation(expr const & e) {
    if (is_lambda(e))
        return is_lambda_equation(binding_body(e));
    else
        return is_equation(e);
}

expr const & equation_lhs(expr const & e) { lean_assert(is_equation(e)); return app_fn(mdata_expr(unwrap_pos(e))); }
expr const & equation_rhs(expr const & e) { lean_assert(is_equation(e)); return app_arg(mdata_expr(unwrap_pos(e))); }
bool is_no_equation(expr const & e) {
    expr e2 = unwrap_pos(e);
    return is_mdata(e2) && get_bool(mdata_data(e2), *g_no_equation_name); }

bool is_lambda_no_equation(expr const & e) {
    if (is_lambda(e))
        return is_lambda_no_equation(binding_body(e));
    else
        return is_no_equation(e);
}

expr mk_inaccessible(expr const & e) { return mk_annotation(*g_inaccessible_name, e); }
bool is_inaccessible(expr const & e) { return is_annotation(e, *g_inaccessible_name); }

expr mk_as_pattern(expr const & lhs, expr const & rhs) {
    return mk_mdata(*g_as_pattern, mk_app(lhs, rhs));
}
bool is_as_pattern(expr const & e) {
    return is_mdata(e) && get_bool(mdata_data(e), *g_as_pattern_name);
}
expr get_as_pattern_lhs(expr const & e) {
    lean_assert(is_as_pattern(e));
    return app_fn(mdata_expr(e));
}
expr get_as_pattern_rhs(expr const & e) {
    lean_assert(is_as_pattern(e));
    return app_arg(mdata_expr(e));
}

bool is_equations(expr const & e) { return is_mdata(e) && get_nat(mdata_data(e), *g_equations_name); }

static void get_equations_args(expr const & e, buffer<expr> & r) {
    lean_assert(is_equations(e));
    expr it    = mdata_expr(e);
    unsigned i = get_nat(mdata_data(e), *g_equations_name)->get_small_value();
    while (i > 1) {
        --i;
        lean_assert(is_app(it));
        r.push_back(app_fn(it));
        it = app_arg(it);
    }
    r.push_back(it);
}

bool is_wf_equations_core(expr const & e) {
    lean_assert(is_equations(e));
    unsigned n = get_nat(mdata_data(e), *g_equations_name)->get_small_value();
    if (n >= 2) {
        buffer<expr> args;
        get_equations_args(e, args);
        return !is_lambda_equation(args[n - 1]);
    } else {
        return false;
    }
}

bool is_wf_equations(expr const & e) {
    return is_equations(e) && is_wf_equations_core(e);
}

unsigned equations_size(expr const & e) {
    lean_assert(is_equations(e));
    if (is_wf_equations_core(e))
        return get_nat(mdata_data(e), *g_equations_name)->get_small_value() - 1;
    else
        return get_nat(mdata_data(e), *g_equations_name)->get_small_value();
}

equations_header get_equations_header(expr const & e) {
    lean_assert(is_equations(e));
    equations_header h;
    kvmap const & m = mdata_data(e);
    h.m_num_fns          = get_nat(m, name(*g_equations_name, "num_fns"))->get_small_value();
    h.m_is_private       = *get_bool(m, name(*g_equations_name, "is_private"));
    h.m_is_lemma         = *get_bool(m, name(*g_equations_name, "is_lemma"));
    h.m_is_unsafe          = *get_bool(m, name(*g_equations_name, "is_unsafe"));
    h.m_is_noncomputable = *get_bool(m, name(*g_equations_name, "is_noncomputable"));
    h.m_aux_lemmas       = *get_bool(m, name(*g_equations_name, "aux_lemmas"));
    h.m_prev_errors      = *get_bool(m, name(*g_equations_name, "prev_errors"));
    h.m_gen_code         = *get_bool(m, name(*g_equations_name, "gen_code"));
    buffer<name> ns;
    buffer<name> as;
    for (unsigned i = 0; i < h.m_num_fns; i++) {
        ns.push_back(*get_name(m, name(name(*g_equations_name, "name"), i)));
        as.push_back(*get_name(m, name(name(*g_equations_name, "actual"), i)));
    }
    h.m_fn_names        = names(ns);
    h.m_fn_actual_names = names(as);
    return h;
}

unsigned equations_num_fns(expr const & e) {
    lean_assert(is_equations(e));
    return get_nat(mdata_data(e), name(*g_equations_name, "num_fns"))->get_small_value();
}

expr const & equations_wf_tactics(expr const & e) {
    lean_assert(is_wf_equations(e));
    buffer<expr> args;
    get_equations_args(e, args);
    return args.back();
}

void to_equations(expr const & e, buffer<expr> & eqns) {
    lean_assert(is_equations(e));
    unsigned n = get_nat(mdata_data(e), *g_equations_name)->get_small_value();
    get_equations_args(e, eqns);
    if (n >= 2 && !is_lambda_equation(eqns.back()))
        eqns.pop_back();
}

expr mk_equations(equations_header const & h, unsigned num_eqs, expr const * eqs) {
    kvmap m;
    m = set_nat(m, *g_equations_name, num_eqs);
    m = set_nat(m, name(*g_equations_name, "num_fns"), h.m_num_fns);
    m = set_bool(m, name(*g_equations_name, "is_private"), h.m_is_private);
    m = set_bool(m, name(*g_equations_name, "is_lemma"), h.m_is_lemma);
    m = set_bool(m, name(*g_equations_name, "is_unsafe"), h.m_is_unsafe);
    m = set_bool(m, name(*g_equations_name, "is_noncomputable"), h.m_is_noncomputable);
    m = set_bool(m, name(*g_equations_name, "aux_lemmas"), h.m_aux_lemmas);
    m = set_bool(m, name(*g_equations_name, "prev_errors"), h.m_prev_errors);
    m = set_bool(m, name(*g_equations_name, "gen_code"), h.m_gen_code);
    lean_assert(length(h.m_fn_names) == h.m_num_fns);
    lean_assert(length(h.m_fn_actual_names) == h.m_num_fns);
    names it1 = h.m_fn_names;
    names it2 = h.m_fn_actual_names;
    for (unsigned i = 0; i < h.m_num_fns; i++) {
        m = set_name(m, name(name(*g_equations_name, "name"), i), head(it1));
        m = set_name(m, name(name(*g_equations_name, "actual"), i), head(it2));
        it1 = tail(it1);
        it2 = tail(it2);
    }
    lean_assert(h.m_num_fns > 0);
    lean_assert(num_eqs > 0);
    lean_assert(std::all_of(eqs, eqs+num_eqs, [](expr const & e) {
                return is_lambda_equation(e) || is_lambda_no_equation(e);
            }));
    expr r     = eqs[num_eqs - 1];
    unsigned i = num_eqs - 1;
    while (i > 0) {
        --i;
        r = mk_app(eqs[i], r);
    }
    r = mk_mdata(m, r);
    lean_assert(get_equations_header(r) == h);
    return r;
}

expr mk_equations(equations_header const & h, unsigned num_eqs, expr const * eqs, expr const & tacs) {
    lean_assert(h.m_num_fns > 0);
    lean_assert(num_eqs > 0);
    lean_assert(std::all_of(eqs, eqs+num_eqs, is_lambda_equation));
    buffer<expr> args;
    args.append(num_eqs, eqs);
    args.push_back(tacs);
    return mk_equations(h, args.size(), args.data());
}

expr update_equations(expr const & eqns, buffer<expr> const & new_eqs) {
    lean_assert(is_equations(eqns));
    lean_assert(!new_eqs.empty());
    if (is_wf_equations(eqns)) {
        return copy_pos(eqns, mk_equations(get_equations_header(eqns), new_eqs.size(), new_eqs.data(),
                                           equations_wf_tactics(eqns)));
    } else {
        return copy_pos(eqns, mk_equations(get_equations_header(eqns), new_eqs.size(), new_eqs.data()));
    }
}

expr update_equations(expr const & eqns, equations_header const & header) {
    buffer<expr> eqs;
    to_equations(eqns, eqs);
    if (is_wf_equations(eqns)) {
        return copy_pos(eqns, mk_equations(header, eqs.size(), eqs.data(),
                                           equations_wf_tactics(eqns)));
    } else {
        return copy_pos(eqns, mk_equations(header, eqs.size(), eqs.data()));
    }
}

expr remove_wf_annotation_from_equations(expr const & eqns) {
    if (is_wf_equations(eqns)) {
        buffer<expr> eqs;
        to_equations(eqns, eqs);
        return copy_pos(eqns, mk_equations(get_equations_header(eqns), eqs.size(), eqs.data()));
    } else {
        return eqns;
    }
}

expr mk_equations_result(unsigned n, expr const * rs) {
    lean_assert(n > 0);
    expr r     = rs[n - 1];
    unsigned i = n - 1;
    while (i > 0) {
        --i;
        r = mk_app(rs[i], r);
    }
    kvmap m = set_nat(kvmap(), *g_equations_result_name, nat(n));
    r = mk_mdata(m, r);
    lean_assert(get_equations_result_size(r) == n);
    return r;
}

bool is_equations_result(expr const & e) { return is_mdata(e) && get_nat(mdata_data(e), *g_equations_result_name); }

unsigned get_equations_result_size(expr const & e) { return get_nat(mdata_data(e), *g_equations_result_name)->get_small_value(); }

static void get_equations_result(expr const & e, buffer<expr> & r) {
    lean_assert(is_equations_result(e));
    expr it    = mdata_expr(e);
    unsigned i = get_nat(mdata_data(e), *g_equations_result_name)->get_small_value();
    while (i > 1) {
        --i;
        lean_assert(is_app(it));
        r.push_back(app_fn(it));
        it = app_arg(it);
    }
    r.push_back(it);
}

expr get_equations_result(expr const & e, unsigned i) {
    buffer<expr> tmp;
    get_equations_result(e, tmp);
    return tmp[i];
}

void initialize_equations() {
    g_equations_name            = new name("equations");
    g_equation_name             = new name("equation");
    g_no_equation_name          = new name("no_equation");
    g_inaccessible_name         = new name("innaccessible");
    g_equations_result_name     = new name("equations_result");
    g_as_pattern_name           = new name("as_pattern");
    g_equation                  = new kvmap(set_bool(kvmap(), *g_equation_name, false));
    g_equation_ignore_if_unused = new kvmap(set_bool(kvmap(), *g_equation_name, true));
    g_no_equation               = new kvmap(set_bool(kvmap(), *g_no_equation_name, false));
    g_as_pattern                = new kvmap(set_bool(kvmap(), *g_as_pattern_name, true));
    register_annotation(*g_inaccessible_name);
}

void finalize_equations() {
    delete g_as_pattern;
    delete g_equation;
    delete g_equation_ignore_if_unused;
    delete g_no_equation;
    delete g_as_pattern_name;
    delete g_equations_result_name;
    delete g_equations_name;
    delete g_equation_name;
    delete g_no_equation_name;
    delete g_inaccessible_name;
}
}
