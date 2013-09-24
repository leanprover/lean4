/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Soonho Kong
*/
#include "util/trace.h"
#include "kernel/abstract.h"
#include "kernel/builtin.h"
#include "kernel/context.h"
#include "kernel/environment.h"
#include "kernel/replace.h"
#include "library/basic_thms.h"
#include "library/printer.h"
#include "library/rewrite/fo_match.h"
#include "library/rewrite/rewrite.h"
#include "library/light_checker.h"

using std::cout;
using std::endl;
using std::pair;
using std::make_pair;

namespace lean {

theorem_rewrite::theorem_rewrite(expr const & type, expr const & body)
    : thm_type(type), thm_body(body), num_args(0) {
    lean_trace("rewrite", tout << "Type = " << thm_type << endl;);
    lean_trace("rewrite", tout << "Body = " << thm_body << endl;);

    // We expect the theorem is in the form of
    // Pi (x_1 : t_1 ... x_n : t_n), pattern = rhs
    pattern = type;
    while (is_pi(pattern)) {
        pattern = abst_body(pattern);
        num_args++;
    }
    if (!is_eq(pattern)) {
        lean_trace("rewrite", tout << "Theorem " << thm_type << " is not in the form of "
                   << "Pi (x_1 : t_1 ... x_n : t_n), pattern = rhs" << endl;);
    }
    rhs = eq_rhs(pattern);
    pattern = eq_lhs(pattern);

    lean_trace("rewrite", tout << "Number of Arg = " << num_args << endl;);
}

pair<expr, expr> theorem_rewrite::operator()(context & ctx, expr const & v, environment const & ) const throw(rewrite_exception) {
    lean_trace("rewrite", tout << "Context = " << ctx << endl;);
    lean_trace("rewrite", tout << "Term = " << v << endl;);
    lean_trace("rewrite", tout << "Pattern = " << pattern << endl;);
    lean_trace("rewrite", tout << "Num Args = " << num_args << endl;);

    fo_match fm;
    subst_map s;
    if (!fm.match(pattern, v, 0, s)) {
        throw rewrite_exception();
    }

    // apply s to rhs
    auto f = [&s](expr const & e, unsigned offset) -> expr {
        if (is_var(e)) {
            lean_trace("rewrite", tout << "Inside of apply : offset = " << offset
                       << ", e = " << e
                       << ", idx = " << var_idx(e)  << endl;);
            unsigned idx = var_idx(e);
            auto it = s.find(idx);
            if (it != s.end()) {
                lean_trace("rewrite", tout << "Inside of apply : s[" << idx << "] = " << s[idx] << endl;);
                return s[idx];
            }
        }
        return e;
    };

    expr new_rhs = replace_fn<decltype(f)>(f)(rhs);
    lean_trace("rewrite", tout << "New RHS = " << new_rhs << endl;);

    expr proof = thm_body;
    for (int i = num_args -1 ; i >= 0; i--) {
        proof = mk_app(proof, s[i]);
        lean_trace("rewrite", tout << "proof: " << i << "\t" << s[i] << "\t" << proof << endl;);
    }
    lean_trace("rewrite", tout << "Proof   = " << proof << endl;);
    return make_pair(new_rhs, proof);
}

pair<expr, expr> orelse_rewrite::operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception) {
    try {
        return rw1(ctx, v, env);
    } catch (rewrite_exception & ) {
        return rw2(ctx, v, env);
    }
}

pair<expr, expr> then_rewrite::operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception) {
    pair<expr, expr> result1 = rw1(ctx, v, env);
    pair<expr, expr> result2 = rw2(ctx, result1.first, env);
    expr const & t = light_checker(env)(v, ctx);
    return make_pair(result2.first,
                     Trans(t, v, result1.first, result2.first, result1.second, result2.second));
}

pair<expr, expr> app_rewrite::operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception) {
    if (!is_app(v))
        throw rewrite_exception();

    unsigned n = num_args(v);
    for (unsigned i = 0; i < n; i++) {
        auto result = rw(ctx, arg(v, i), env);
    }

    // TODO(soonhok)
    throw rewrite_exception();
}

pair<expr, expr> lambda_rewrite::operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception) {
    if (!is_lambda(v))
        throw rewrite_exception();
    expr const & domain = abst_domain(v);
    expr const & body   = abst_body(v);

    auto result_domain = rw(ctx, domain, env);
    auto result_body   = rw(ctx, body,   env); // TODO(soonhok): add to context!

    // TODO(soonhok)
    throw rewrite_exception();
}

pair<expr, expr> pi_rewrite::operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception) {
    if (!is_pi(v))
        throw rewrite_exception();

    expr const & domain = abst_domain(v);
    expr const & body   = abst_body(v);

    auto result_domain = rw(ctx, domain, env);
    auto result_body   = rw(ctx, body,   env); // TODO(soonhok): add to context!

    // TODO(soonhok)
    throw rewrite_exception();
}

pair<expr, expr> let_rewrite::operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception) {
    if (!is_let(v))
        throw rewrite_exception();

    expr const & ty    = let_type(v);
    expr const & value = let_value(v);
    expr const & body  = let_body(v);

    auto result_ty    = rw(ctx, ty,    env);
    auto result_value = rw(ctx, value, env);
    auto result_body  = rw(ctx, body,  env); // TODO(soonhok): add to context!

    // TODO(soonhok)
    throw rewrite_exception();
}
}
