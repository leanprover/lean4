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

void rewrite_cell::dealloc() {
    delete this;
}
rewrite_cell::rewrite_cell(rewrite_kind k):m_kind(k), m_rc(1) { }
rewrite_cell::~rewrite_cell() {
}

// Theorem Rewrite
theorem_rewrite_cell::theorem_rewrite_cell(expr const & type, expr const & body)
    : rewrite_cell(rewrite_kind::Theorem), m_type(type), m_body(body), m_num_args(0) {
    lean_trace("rewrite", tout << "Type = " << m_type << endl;);
    lean_trace("rewrite", tout << "Body = " << m_body << endl;);

    // We expect the theorem is in the form of
    // Pi (x_1 : t_1 ... x_n : t_n), pattern = rhs
    m_pattern = m_type;
    while (is_pi(m_pattern)) {
        m_pattern = abst_body(m_pattern);
        m_num_args++;
    }
    if (!is_eq(m_pattern)) {
        lean_trace("rewrite", tout << "Theorem " << m_type << " is not in the form of "
                   << "Pi (x_1 : t_1 ... x_n : t_n), pattern = rhs" << endl;);
    }
    m_rhs = eq_rhs(m_pattern);
    m_pattern = eq_lhs(m_pattern);

    lean_trace("rewrite", tout << "Number of Arg = " << m_num_args << endl;);
}
theorem_rewrite_cell::~theorem_rewrite_cell() { }
pair<expr, expr> theorem_rewrite_cell::operator()(context &, expr const & v, environment const & ) const throw(rewrite_exception) {
    // lean_trace("rewrite", tout << "Context = " << ctx << endl;);
    lean_trace("rewrite", tout << "Term = " << v << endl;);
    lean_trace("rewrite", tout << "Pattern = " << m_pattern << endl;);
    lean_trace("rewrite", tout << "Num Args = " << m_num_args << endl;);

    fo_match fm;
    subst_map s;
    if (!fm.match(m_pattern, v, 0, s)) {
        throw rewrite_exception();
    }

    // apply s to rhs
    auto f = [&s](expr const & e, unsigned offset) -> expr {
        if (!is_var(e)) {
            return e;
        }
        unsigned idx = var_idx(e);
        if (idx < offset) {
            return e;
        }

        lean_trace("rewrite", tout << "Inside of apply : offset = " << offset
                   << ", e = " << e
                   << ", idx = " << var_idx(e)  << endl;);
        auto it = s.find(idx);
        if (it != s.end()) {
            lean_trace("rewrite", tout << "Inside of apply : s[" << idx << "] = " << s[idx] << endl;);
            return s[idx];
        }
        return e;
    };

    expr new_rhs = replace_fn<decltype(f)>(f)(m_rhs);
    lean_trace("rewrite", tout << "New RHS = " << new_rhs << endl;);

    expr proof = m_body;
    for (int i = m_num_args -1 ; i >= 0; i--) {
        proof = mk_app(proof, s[i]);
        lean_trace("rewrite", tout << "proof: " << i << "\t" << s[i] << "\t" << proof << endl;);
    }
    lean_trace("rewrite", tout << "Proof   = " << proof << endl;);
    return make_pair(new_rhs, proof);
}

// OrElse Rewrite
orelse_rewrite_cell::orelse_rewrite_cell(rewrite const & rw1, rewrite const & rw2)
    :rewrite_cell(rewrite_kind::OrElse), m_rw1(rw1), m_rw2(rw2) { }
orelse_rewrite_cell::~orelse_rewrite_cell() { }
pair<expr, expr> orelse_rewrite_cell::operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception) {
    try {
        return m_rw1(ctx, v, env);
    } catch (rewrite_exception & ) {
        return m_rw2(ctx, v, env);
    }
}

// Then Rewrite
then_rewrite_cell::then_rewrite_cell(rewrite const & rw1, rewrite const & rw2)
    :rewrite_cell(rewrite_kind::Then), m_rw1(rw1), m_rw2(rw2) { }
then_rewrite_cell::~then_rewrite_cell() { }
pair<expr, expr> then_rewrite_cell::operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception) {
    pair<expr, expr> result1 = m_rw1(ctx, v, env);
    pair<expr, expr> result2 = m_rw2(ctx, result1.first, env);
    light_checker lc(env);
    expr const & t = lc(v, ctx);
    return make_pair(result2.first,
                     Trans(t, v, result1.first, result2.first, result1.second, result2.second));
}

// App Rewrite
app_rewrite_cell::app_rewrite_cell(rewrite const & rw)
    :rewrite_cell(rewrite_kind::App), m_rw(rw) { }
app_rewrite_cell::~app_rewrite_cell() { }
pair<expr, expr> app_rewrite_cell::operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception) {
    if (!is_app(v))
        throw rewrite_exception();

    unsigned n = num_args(v);
    for (unsigned i = 0; i < n; i++) {
        auto result = m_rw(ctx, arg(v, i), env);
    }

    // TODO(soonhok)
    throw rewrite_exception();
}

// Lambda Rewrite
lambda_rewrite_cell::lambda_rewrite_cell(rewrite const & rw)
    :rewrite_cell(rewrite_kind::Lambda), m_rw(rw) { }
lambda_rewrite_cell::~lambda_rewrite_cell() { }

pair<expr, expr> lambda_rewrite_cell::operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception) {
    if (!is_lambda(v))
        throw rewrite_exception();
    expr const & domain = abst_domain(v);
    expr const & body   = abst_body(v);

    auto result_domain = m_rw(ctx, domain, env);
    auto result_body   = m_rw(ctx, body,   env); // TODO(soonhok): add to context!

    // TODO(soonhok)
    throw rewrite_exception();
}

// Pi Rewrite
pi_rewrite_cell::pi_rewrite_cell(rewrite const & rw)
    :rewrite_cell(rewrite_kind::Pi), m_rw(rw) { }
pi_rewrite_cell::~pi_rewrite_cell() { }
pair<expr, expr> pi_rewrite_cell::operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception) {
    if (!is_pi(v))
        throw rewrite_exception();

    expr const & domain = abst_domain(v);
    expr const & body   = abst_body(v);

    auto result_domain = m_rw(ctx, domain, env);
    auto result_body   = m_rw(ctx, body,   env); // TODO(soonhok): add to context!

    // TODO(soonhok)
    throw rewrite_exception();
}

// Let rewrite
let_rewrite_cell::let_rewrite_cell(rewrite const & rw)
    :rewrite_cell(rewrite_kind::Let), m_rw(rw) { }
let_rewrite_cell::~let_rewrite_cell() { }
pair<expr, expr> let_rewrite_cell::operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception) {
    if (!is_let(v))
        throw rewrite_exception();

    expr const & ty    = let_type(v);
    expr const & value = let_value(v);
    expr const & body  = let_body(v);

    auto result_ty    = m_rw(ctx, ty,    env);
    auto result_value = m_rw(ctx, value, env);
    auto result_body  = m_rw(ctx, body,  env); // TODO(soonhok): add to context!

    // TODO(soonhok)
    throw rewrite_exception();
}

// Fail rewrite
fail_rewrite_cell::fail_rewrite_cell():rewrite_cell(rewrite_kind::Fail) { }
fail_rewrite_cell::~fail_rewrite_cell() { }
pair<expr, expr> fail_rewrite_cell::operator()(context &, expr const &, environment const &) const throw(rewrite_exception) {
    throw rewrite_exception();
}

// Success rewrite (trivial)
success_rewrite_cell::success_rewrite_cell():rewrite_cell(rewrite_kind::Success) { }
success_rewrite_cell::~success_rewrite_cell() { }
pair<expr, expr> success_rewrite_cell::operator()(context &, expr const & v, environment const &) const throw(rewrite_exception) {
    return make_pair(v, mk_app(Const("Refl"), v));
}

// Repeat rewrite
repeat_rewrite_cell::repeat_rewrite_cell(rewrite const & rw):rewrite_cell(rewrite_kind::Repeat), m_rw(rw) { }
repeat_rewrite_cell::~repeat_rewrite_cell() { }
pair<expr, expr> repeat_rewrite_cell::operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception) {
    pair<expr, expr> result = mk_success_rewrite()(ctx, v, env);
    // TODO(soonhok) fix
    try {
        while (true) {
            result = m_rw(ctx, result.first, env);
        }
    }
    catch (rewrite_exception & ) {
        return result;
    }
}

rewrite mk_theorem_rewrite(expr const & type, expr const & body) {
    return rewrite(new theorem_rewrite_cell(type, body));
}
rewrite mk_then_rewrite(rewrite const & rw1, rewrite const & rw2) {
    return rewrite(new then_rewrite_cell(rw1, rw2));
}
rewrite mk_orelse_rewrite(rewrite const & rw1, rewrite const & rw2) {
    return rewrite(new orelse_rewrite_cell(rw1, rw2));
}
rewrite mk_app_rewrite(rewrite const & rw) {
    return rewrite(new app_rewrite_cell(rw));
}
rewrite mk_lambda_rewrite(rewrite const & rw) {
    return rewrite(new lambda_rewrite_cell(rw));
}
rewrite mk_pi_rewrite(rewrite const & rw) {
    return rewrite(new pi_rewrite_cell(rw));
}
rewrite mk_let_rewrite(rewrite const & rw) {
    return rewrite(new let_rewrite_cell(rw));
}
rewrite mk_fail_rewrite() {
    return rewrite(new fail_rewrite_cell());
}
rewrite mk_success_rewrite() {
    return rewrite(new success_rewrite_cell());
}
rewrite mk_repeat_rewrite(rewrite const & rw) {
    return rewrite(new repeat_rewrite_cell(rw));
}
}
