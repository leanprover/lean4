/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "kernel/instantiate.h"
#include "library/blast/infer_type.h"
#include "library/blast/blast_context.h"

namespace lean {
namespace blast {
static optional<expr> expand_macro(expr const & m) {
    lean_assert(is_macro(m));
    return macro_def(m).expand(m, ext_ctx());
}

static optional<expr> reduce_projection(expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return none_expr();
    projection_info const * info = get_projection_info(const_name(f));
    if (!info)
        return none_expr();
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() <= info->m_nparams)
        return none_expr();
    unsigned mkidx  = info->m_nparams;
    expr const & mk = args[mkidx];
    expr new_mk     = whnf(mk);
    expr const & new_mk_fn = get_app_fn(new_mk);
    if (!is_constant(new_mk_fn) || const_name(new_mk_fn) != info->m_constructor)
        return none_expr();
    buffer<expr> mk_args;
    get_app_args(new_mk, mk_args);
    unsigned i = info->m_nparams + info->m_i;
    if (i >= mk_args.size())
        none_expr();
    expr r = mk_args[i];
    r = blast::mk_app(r, args.size() - mkidx - 1, args.data() + mkidx + 1);
    return some_expr(r);
}

static optional<expr> norm_ext(expr const & e) {
    if (auto r = reduce_projection(e)) {
        return r;
    } else if (auto r = env().norm_ext()(e, ext_ctx())) {
        return some_expr(r->first);
    } else {
        return none_expr();
    }
}

static expr whnf_core(expr const & e) {
    check_system("whnf");

    switch (e.kind()) {
    case expr_kind::Var:  case expr_kind::Sort: case expr_kind::Meta: case expr_kind::Local:
    case expr_kind::Pi:   case expr_kind::Lambda:
        return e;
    case expr_kind::Constant:
        if (blast::is_reducible(const_name(e)))
            return whnf_core(instantiate_value_univ_params(env().get(const_name(e)), const_levels(e)));
        else
            return e;
    case expr_kind::Macro:
        if (auto m = expand_macro(e))
            return whnf_core(*m);
        else
            return e;
    case expr_kind::App: {
        buffer<expr> args;
        expr f0 = get_app_rev_args(e, args);
        expr f = whnf_core(f0);
        if (is_lambda(f)) {
            unsigned m = 1;
            unsigned num_args = args.size();
            while (is_lambda(binding_body(f)) && m < num_args) {
                f = binding_body(f);
                m++;
            }
            lean_assert(m <= num_args);
            return whnf_core(blast::mk_rev_app(instantiate(binding_body(f), m, args.data() + (num_args - m)),
                                               num_args - m, args.data()));
        } else {
            return f == f0 ? e : whnf_core(blast::mk_rev_app(f, args.size(), args.data()));
        }
    }}
    lean_unreachable();
}

expr whnf(expr const & e) {
    expr t = e;
    while (true) {
        expr t1 = whnf_core(t);
        if (auto new_t = norm_ext(t1)) {
            t  = *new_t;
        } else {
            return t1;
        }
    }
}

bool is_def_eq(expr const & e1, expr const & e2) {
    // TODO(Leo)
    return e1 == e2;
}

expr infer_type(expr const & e) {
    // TODO(Leo)
    return e;
}
}}
