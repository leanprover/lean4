/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Quotient types.
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
class quot_consts {
    static name * g_quot;
    static name * g_quot_lift;
    static name * g_quot_ind;
    static name * g_quot_mk;

    friend bool quot_is_decl(name const & n);
    friend bool quot_is_rec(name const & n);
    template<typename WHNF> friend optional<expr> quot_reduce_rec(expr const & e, WHNF const & whnf);
    template<typename WHNF, typename IS_STUCK> friend optional<expr> quot_is_stuck(expr const & e, WHNF const & whnf, IS_STUCK const & is_stuck);
    friend class environment;
    friend void initialize_quot();
    friend void finalize_quot();
};

inline bool quot_is_decl(name const & n) {
    return n == *quot_consts::g_quot || n == *quot_consts::g_quot_lift || n == *quot_consts::g_quot_ind || n == *quot_consts::g_quot_mk;
}

inline bool quot_is_rec(name const & n) {
    return n == *quot_consts::g_quot_lift || n == *quot_consts::g_quot_ind;
}

/** \brief Try to reduce a `quot` recursor application (i.e., `quot.lift` or `quot.ind` application).

    `whnf : expr -> expr` */
template<typename WHNF> optional<expr> quot_reduce_rec(expr const & e, WHNF const & whnf) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn))
        return none_expr();
    unsigned mk_pos;
    unsigned arg_pos;
    if (const_name(fn) == *quot_consts::g_quot_lift) {
        mk_pos  = 5;
        arg_pos = 3;
    } else if (const_name(fn) == *quot_consts::g_quot_ind) {
        mk_pos  = 4;
        arg_pos = 3;
    } else {
        return none_expr();
    }
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() <= mk_pos)
        return none_expr();

    expr mk = whnf(args[mk_pos]);
    expr const & mk_fn = get_app_fn(mk);
    if (!is_constant(mk_fn) || const_name(mk_fn) != *quot_consts::g_quot_mk || get_app_num_args(mk) != 3)
        return none_expr();

    expr const & f = args[arg_pos];
    expr r = mk_app(f, app_arg(mk));
    unsigned elim_arity = mk_pos+1;
    if (args.size() > elim_arity)
        r = mk_app(r, args.size() - elim_arity, args.begin() + elim_arity);
    return some_expr(r);
}

/** \brief Return a non-none expression that is preventing the `quot` recursor application from being reduced.

    `whnf : expr -> expr`
    `is_stuck : expr -> optional<expr> */
template<typename WHNF, typename IS_STUCK> optional<expr> quot_is_stuck(expr const & e, WHNF const & whnf, IS_STUCK const & is_stuck) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn))
        return none_expr();
    unsigned mk_pos;
    if (const_name(fn) == *quot_consts::g_quot_lift) {
        mk_pos = 5;
    } else if (const_name(fn) == *quot_consts::g_quot_ind) {
        mk_pos = 4;
    } else {
        return none_expr();
    }

    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() <= mk_pos)
        return none_expr();

    return is_stuck(whnf(args[mk_pos]));
}

void initialize_quot();
void finalize_quot();
}
