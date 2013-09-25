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
#include "library/rewriter/fo_match.h"
#include "library/rewriter/rewriter.h"
#include "library/light_checker.h"

using std::cout;
using std::endl;
using std::pair;
using std::make_pair;

namespace lean {

void rewriter_cell::dealloc() {
    delete this;
}
rewriter_cell::rewriter_cell(rewriter_kind k):m_kind(k), m_rc(1) { }
rewriter_cell::~rewriter_cell() {
}

// Theorem Rewriter
theorem_rewriter_cell::theorem_rewriter_cell(expr const & type, expr const & body)
    : rewriter_cell(rewriter_kind::Theorem), m_type(type), m_body(body), m_num_args(0) {
    lean_trace("rewriter", tout << "Type = " << m_type << endl;);
    lean_trace("rewriter", tout << "Body = " << m_body << endl;);

    // We expect the theorem is in the form of
    // Pi (x_1 : t_1 ... x_n : t_n), pattern = rhs
    m_pattern = m_type;
    while (is_pi(m_pattern)) {
        m_pattern = abst_body(m_pattern);
        m_num_args++;
    }
    if (!is_eq(m_pattern)) {
        lean_trace("rewriter", tout << "Theorem " << m_type << " is not in the form of "
                   << "Pi (x_1 : t_1 ... x_n : t_n), pattern = rhs" << endl;);
    }
    m_rhs = eq_rhs(m_pattern);
    m_pattern = eq_lhs(m_pattern);

    lean_trace("rewriter", tout << "Number of Arg = " << m_num_args << endl;);
}
theorem_rewriter_cell::~theorem_rewriter_cell() { }
pair<expr, expr> theorem_rewriter_cell::operator()(environment const &, context &, expr const & v) const throw(rewriter_exception) {
    // lean_trace("rewriter", tout << "Context = " << ctx << endl;);
    lean_trace("rewriter", tout << "Term = " << v << endl;);
    lean_trace("rewriter", tout << "Pattern = " << m_pattern << endl;);
    lean_trace("rewriter", tout << "Num Args = " << m_num_args << endl;);

    fo_match fm;
    subst_map s;
    if (!fm.match(m_pattern, v, 0, s)) {
        throw rewriter_exception();
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

        lean_trace("rewriter", tout << "Inside of apply : offset = " << offset
                   << ", e = " << e
                   << ", idx = " << var_idx(e)  << endl;);
        auto it = s.find(idx);
        if (it != s.end()) {
            lean_trace("rewriter", tout << "Inside of apply : s[" << idx << "] = " << s[idx] << endl;);
            return s[idx];
        }
        return e;
    };

    expr new_rhs = replace_fn<decltype(f)>(f)(m_rhs);
    lean_trace("rewriter", tout << "New RHS = " << new_rhs << endl;);

    expr proof = m_body;
    for (int i = m_num_args -1 ; i >= 0; i--) {
        proof = mk_app(proof, s[i]);
        lean_trace("rewriter", tout << "proof: " << i << "\t" << s[i] << "\t" << proof << endl;);
    }
    lean_trace("rewriter", tout << "Proof   = " << proof << endl;);
    return make_pair(new_rhs, proof);
}

// OrElse Rewriter
orelse_rewriter_cell::orelse_rewriter_cell(rewriter const & rw1, rewriter const & rw2)
    :rewriter_cell(rewriter_kind::OrElse), m_rw1(rw1), m_rw2(rw2) { }
orelse_rewriter_cell::~orelse_rewriter_cell() { }
pair<expr, expr> orelse_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    try {
        return m_rw1(env, ctx, v);
    } catch (rewriter_exception & ) {
        return m_rw2(env, ctx, v);
    }
}

// Then Rewriter
then_rewriter_cell::then_rewriter_cell(rewriter const & rw1, rewriter const & rw2)
    :rewriter_cell(rewriter_kind::Then), m_rw1(rw1), m_rw2(rw2) { }
then_rewriter_cell::~then_rewriter_cell() { }
pair<expr, expr> then_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    pair<expr, expr> result1 = m_rw1(env, ctx, v);
    pair<expr, expr> result2 = m_rw2(env, ctx, result1.first);
    light_checker lc(env);
    expr const & t = lc(v, ctx);
    return make_pair(result2.first,
                     Trans(t, v, result1.first, result2.first, result1.second, result2.second));
}

// App Rewriter
app_rewriter_cell::app_rewriter_cell(rewriter const & rw)
    :rewriter_cell(rewriter_kind::App), m_rw(rw) { }
app_rewriter_cell::~app_rewriter_cell() { }
pair<expr, expr> app_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    if (!is_app(v))
        throw rewriter_exception();

    unsigned n = num_args(v);
    for (unsigned i = 0; i < n; i++) {
        auto result = m_rw(env, ctx, arg(v, i));
    }

    // TODO(soonhok)
    throw rewriter_exception();
}

// Lambda Rewriter
lambda_rewriter_cell::lambda_rewriter_cell(rewriter const & rw)
    :rewriter_cell(rewriter_kind::Lambda), m_rw(rw) { }
lambda_rewriter_cell::~lambda_rewriter_cell() { }

pair<expr, expr> lambda_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    if (!is_lambda(v))
        throw rewriter_exception();
    expr const & domain = abst_domain(v);
    expr const & body   = abst_body(v);

    auto result_domain = m_rw(env, ctx, domain);
    auto result_body   = m_rw(env, ctx, body); // TODO(soonhok): add to context!

    // TODO(soonhok)
    throw rewriter_exception();
}

// Pi Rewriter
pi_rewriter_cell::pi_rewriter_cell(rewriter const & rw)
    :rewriter_cell(rewriter_kind::Pi), m_rw(rw) { }
pi_rewriter_cell::~pi_rewriter_cell() { }
pair<expr, expr> pi_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    if (!is_pi(v))
        throw rewriter_exception();

    expr const & domain = abst_domain(v);
    expr const & body   = abst_body(v);

    auto result_domain = m_rw(env, ctx, domain);
    auto result_body   = m_rw(env, ctx, body); // TODO(soonhok): add to context!

    // TODO(soonhok)
    throw rewriter_exception();
}

// Let rewriter
let_rewriter_cell::let_rewriter_cell(rewriter const & rw)
    :rewriter_cell(rewriter_kind::Let), m_rw(rw) { }
let_rewriter_cell::~let_rewriter_cell() { }
pair<expr, expr> let_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    if (!is_let(v))
        throw rewriter_exception();

    expr const & ty    = let_type(v);
    expr const & value = let_value(v);
    expr const & body  = let_body(v);

    auto result_ty    = m_rw(env, ctx, ty);
    auto result_value = m_rw(env, ctx, value);
    auto result_body  = m_rw(env, ctx, body); // TODO(soonhok): add to context!

    // TODO(soonhok)
    throw rewriter_exception();
}

// Fail rewriter
fail_rewriter_cell::fail_rewriter_cell():rewriter_cell(rewriter_kind::Fail) { }
fail_rewriter_cell::~fail_rewriter_cell() { }
pair<expr, expr> fail_rewriter_cell::operator()(environment const &, context &, expr const &) const throw(rewriter_exception) {
    throw rewriter_exception();
}

// Success rewriter (trivial)
success_rewriter_cell::success_rewriter_cell():rewriter_cell(rewriter_kind::Success) { }
success_rewriter_cell::~success_rewriter_cell() { }
pair<expr, expr> success_rewriter_cell::operator()(environment const &, context &, expr const & v) const throw(rewriter_exception) {
    return make_pair(v, mk_app(Const("Refl"), v));
}

// Repeat rewriter
repeat_rewriter_cell::repeat_rewriter_cell(rewriter const & rw):rewriter_cell(rewriter_kind::Repeat), m_rw(rw) { }
repeat_rewriter_cell::~repeat_rewriter_cell() { }
pair<expr, expr> repeat_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    pair<expr, expr> result = mk_success_rewriter()(env, ctx, v);
    // TODO(soonhok) fix
    try {
        while (true) {
            result = m_rw(env, ctx, result.first);
        }
    }
    catch (rewriter_exception & ) {
        return result;
    }
}

rewriter mk_theorem_rewriter(expr const & type, expr const & body) {
    return rewriter(new theorem_rewriter_cell(type, body));
}
rewriter mk_then_rewriter(rewriter const & rw1, rewriter const & rw2) {
    return rewriter(new then_rewriter_cell(rw1, rw2));
}
rewriter mk_orelse_rewriter(rewriter const & rw1, rewriter const & rw2) {
    return rewriter(new orelse_rewriter_cell(rw1, rw2));
}
rewriter mk_app_rewriter(rewriter const & rw) {
    return rewriter(new app_rewriter_cell(rw));
}
rewriter mk_lambda_rewriter(rewriter const & rw) {
    return rewriter(new lambda_rewriter_cell(rw));
}
rewriter mk_pi_rewriter(rewriter const & rw) {
    return rewriter(new pi_rewriter_cell(rw));
}
rewriter mk_let_rewriter(rewriter const & rw) {
    return rewriter(new let_rewriter_cell(rw));
}
rewriter mk_fail_rewriter() {
    return rewriter(new fail_rewriter_cell());
}
rewriter mk_success_rewriter() {
    return rewriter(new success_rewriter_cell());
}
rewriter mk_repeat_rewriter(rewriter const & rw) {
    return rewriter(new repeat_rewriter_cell(rw));
}
}
