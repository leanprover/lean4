/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Soonho Kong
*/
#include "kernel/abstract.h"
#include "kernel/builtin.h"
#include "kernel/context.h"
#include "kernel/environment.h"
#include "kernel/expr.h"
#include "kernel/replace.h"
#include "library/basic_thms.h"
#include "library/light_checker.h"
#include "library/printer.h"
#include "library/rewriter/fo_match.h"
#include "library/rewriter/rewriter.h"
#include "util/buffer.h"
#include "util/trace.h"

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
    lean_trace("rewriter", tout << "Subst = " << s << endl;);

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
            lean_trace("rewriter", tout << "Inside of apply : s[" << idx << "] = " << it->second << endl;);
            return it->second;
        }
        return e;
    };

    expr new_rhs = replace_fn<decltype(f)>(f)(m_rhs);
    lean_trace("rewriter", tout << "New RHS = " << new_rhs << endl;);

    expr proof = m_body;
    for (int i = m_num_args -1 ; i >= 0; i--) {
        auto it = s.find(i);
        lean_assert(it != s.end());
        proof = proof(it->second);
        lean_trace("rewriter", tout << "proof: " << i << "\t" << it->second << "\t" << proof << endl;);
    }
    lean_trace("rewriter", tout << "Proof   = " << proof << endl;);
    return make_pair(new_rhs, proof);
}
std::ostream & theorem_rewriter_cell::display(std::ostream & out) const {
    out << "Thm_RW("
        << m_type << ", "
        << m_body << ")";
    return out;
}

// OrElse Rewriter
orelse_rewriter_cell::orelse_rewriter_cell(rewriter const & rw1, rewriter const & rw2)
    :rewriter_cell(rewriter_kind::OrElse), m_rwlist({rw1, rw2}) { }
orelse_rewriter_cell::orelse_rewriter_cell(std::initializer_list<rewriter> const & l)
    :rewriter_cell(rewriter_kind::OrElse), m_rwlist(l) {
    lean_assert(l.size() >= 2);
}
orelse_rewriter_cell::~orelse_rewriter_cell() { }
pair<expr, expr> orelse_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    for (rewriter const & rw : m_rwlist) {
        try {
            return rw(env, ctx, v);
        } catch (rewriter_exception & ) {
            // Do nothing
        }
    }
    // If the execution reaches here, it means every rewriter failed.
    throw rewriter_exception();
}
std::ostream & orelse_rewriter_cell::display(std::ostream & out) const {
    out << "Or_RW({";
    iter(m_rwlist, [&out](rewriter const & rw) {
            out << rw << "; ";
        });
    out << "})";
    return out;
}

// Then Rewriter
then_rewriter_cell::then_rewriter_cell(rewriter const & rw1, rewriter const & rw2)
    :rewriter_cell(rewriter_kind::Then), m_rwlist({rw1, rw2}) { }
then_rewriter_cell::then_rewriter_cell(std::initializer_list<rewriter> const & l)
    :rewriter_cell(rewriter_kind::Then), m_rwlist(l) {
    lean_assert(l.size() >= 2);
}
then_rewriter_cell::~then_rewriter_cell() { }
pair<expr, expr> then_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    pair<expr, expr> result = car(m_rwlist)(env, ctx, v);
    pair<expr, expr> new_result = result;
    for (rewriter const & rw : cdr(m_rwlist)) {
        new_result = rw(env, ctx, result.first);
        expr const & ty = light_checker(env)(v, ctx);
        if (v != new_result.first) {
            result = make_pair(new_result.first,
                               Trans(ty, v, result.first, new_result.first, result.second, new_result.second));
        }
    }
    return result;
}
std::ostream & then_rewriter_cell::display(std::ostream & out) const {
    out << "Then_RW({";
    iter(m_rwlist, [&out](rewriter const & rw) {
            out << rw << "; ";
        });
    out << "})";
    return out;
}

// Try Rewriter
try_rewriter_cell::try_rewriter_cell(rewriter const & rw1, rewriter const & rw2)
    :rewriter_cell(rewriter_kind::Try), m_rwlist({rw1, rw2}) { }
try_rewriter_cell::try_rewriter_cell(std::initializer_list<rewriter> const & l)
    :rewriter_cell(rewriter_kind::Try), m_rwlist(l) {
    lean_assert(l.size() >= 1);
}
try_rewriter_cell::~try_rewriter_cell() { }
pair<expr, expr> try_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    for (rewriter const & rw : m_rwlist) {
        try {
            return rw(env, ctx, v);
        } catch (rewriter_exception & ) {
            // Do nothing
        }
    }
    // If the execution reaches here, it means every rewriter failed.
    expr const & t = light_checker(env)(v, ctx);
    return make_pair(v, Refl(t, v));
}
std::ostream & try_rewriter_cell::display(std::ostream & out) const {
    out << "Try_RW({";
    iter(m_rwlist, [&out](rewriter const & rw) {
            out << rw << "; ";
        });
    out << "})";
    return out;
}

// App Rewriter
app_rewriter_cell::app_rewriter_cell(rewriter const & rw)
    :rewriter_cell(rewriter_kind::App), m_rw(rw) { }
app_rewriter_cell::~app_rewriter_cell() { }
pair<expr, expr> app_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    if (!is_app(v))
        throw rewriter_exception();

    unsigned n = num_args(v);
    lean_assert_ge(n, 2);
    expr f = arg(v, 0);
    pair<expr, expr> result = m_rw(env, ctx, f);
    expr new_f = result.first;
    bool f_changed = (f != new_f);

    for (unsigned i = 1; i < n; i++) {
        // Information about f
        new_f = result.first;
        expr proof_f = result.second;
        light_checker lc(env);
        expr const & f_ty = lc(f, ctx);
        lean_assert(is_pi(f_ty));
        expr f_ty_domain = abst_domain(f_ty); // A
        expr f_ty_body = mk_lambda(abst_name(f_ty), f_ty_domain, abst_body(f_ty)); // B

        // Information about arg_i
        expr arg_i = arg(v, i);
        pair<expr, expr> new_result = m_rw(env, ctx, arg_i);
        expr new_arg_i = new_result.first;
        expr proof_arg_i = new_result.second;
        bool arg_changed = (arg_i != new_arg_i);

        if (f_changed) {
            if (arg_changed) {
                // Congr : Pi (A : Type u) (B : A -> Type u) (f g : Pi (x : A) B x) (a b : A) (H1 : f = g) (H2 : a = b), f a = g b
                expr new_v = new_f(new_arg_i);
                expr new_proof = Congr(f_ty_domain,
                                       f_ty_body,
                                       f,
                                       new_f,
                                       arg_i,
                                       new_arg_i,
                                       proof_f,
                                       proof_arg_i);
                result = make_pair(new_v, new_proof);
            } else {
                // Congr1 : Pi (A : Type u) (B : A -> Type u) (f g: Pi (x : A) B x) (a : A) (H : f = g), f a = g a
                expr new_v = new_f(new_arg_i);
                expr new_proof = Congr1(f_ty_domain,
                                        f_ty_body,
                                        f,
                                        new_f,
                                        arg_i,
                                        proof_f);
                result = make_pair(new_v, new_proof);
            }
        } else {
            if (arg_changed) {
                // Congr2 : Pi (A : Type u) (B : A -> Type u)  (a b : A) (f : Pi (x : A) B x) (H : a = b), f a = f b
                expr new_v = new_f(new_arg_i);
                expr new_proof = Congr2(f_ty_domain,
                                        f_ty_body,
                                        arg_i,
                                        new_arg_i,
                                        f,
                                        proof_arg_i);
                result = make_pair(new_v, new_proof);
                f_changed = true;
            } else {
                // Refl
                expr new_v = new_f(new_arg_i);
                expr new_proof = Refl(lc(new_f, ctx), new_f);
                result = make_pair(new_v, new_proof);
            }
        }
        f = f(arg_i);
    }
    return result;
}

std::ostream & app_rewriter_cell::display(std::ostream & out) const {
    out << "App_RW(" << m_rw << ")";
    return out;
}

// Lambda Type Rewriter
lambda_type_rewriter_cell::lambda_type_rewriter_cell(rewriter const & rw)
    :rewriter_cell(rewriter_kind::LambdaType), m_rw(rw) { }
lambda_type_rewriter_cell::~lambda_type_rewriter_cell() { }

pair<expr, expr> lambda_type_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    if (!is_lambda(v))
        throw rewriter_exception();
    expr const & ty = abst_domain(v);
    pair<expr, expr> result = m_rw(env, ctx, ty);
    expr const & new_ty = result.first;
    light_checker lc(env);
    expr const & ty_of_v = lc(v, ctx);
    if (ty != new_ty) {
        expr const & new_v = mk_lambda(abst_name(v), new_ty, abst_body(v));
        expr const & ty_of_ty = lc(ty, ctx);
        expr proof = Subst(ty_of_ty, ty, new_ty,
                           Fun({Const("x"), ty_of_ty},
                               Eq(mk_lambda(abst_name(v), ty, abst_body(v)),
                                  mk_lambda(abst_name(v), Const("x"), abst_body(v)))),
                           Refl(ty_of_v, v),
                           result.second);
        return make_pair(new_v, proof);
    } else {
        return make_pair(v, Refl(ty_of_v, v));
    }
}
std::ostream & lambda_type_rewriter_cell::display(std::ostream & out) const {
    out << "Lambda_Type_RW(" << m_rw << ")";
    return out;
}

// Lambda Body Rewriter
lambda_body_rewriter_cell::lambda_body_rewriter_cell(rewriter const & rw)
    :rewriter_cell(rewriter_kind::LambdaBody), m_rw(rw) { }
lambda_body_rewriter_cell::~lambda_body_rewriter_cell() { }

pair<expr, expr> lambda_body_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    if (!is_lambda(v))
        throw rewriter_exception();
    expr const & body = abst_body(v);
    name const & n = abst_name(v);
    expr const & ty = abst_domain(v);
    context new_ctx = extend(ctx, n, ty);
    pair<expr, expr> result = m_rw(env, new_ctx, body);
    light_checker lc(env);
    expr const & ty_of_v = lc(v, ctx);
    expr const & new_body = result.first;
    if (body != new_body) {
        expr const & new_v = mk_lambda(n, ty, new_body);
        expr const & ty_of_body = lc(body, new_ctx);
        expr proof = Subst(ty_of_body, body, new_body,
                           Fun({Const("x"), ty_of_body},
                               Eq(mk_lambda(abst_name(v), ty, abst_body(v)),
                                  mk_lambda(abst_name(v), ty, Const("x")))),
                           Refl(ty_of_v, v),
                           result.second);
        return make_pair(new_v, proof);
    } else {
        return make_pair(v, Refl(ty_of_v, v));
    }
}
std::ostream & lambda_body_rewriter_cell::display(std::ostream & out) const {
    out << "Lambda_Body_RW(" << m_rw << ")";
    return out;
}

// Lambda Rewriter
lambda_rewriter_cell::lambda_rewriter_cell(rewriter const & rw)
    :rewriter_cell(rewriter_kind::Lambda), m_rw(rw) { }
lambda_rewriter_cell::~lambda_rewriter_cell() { }

pair<expr, expr> lambda_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    if (!is_lambda(v))
        throw rewriter_exception();
    rewriter rw = mk_then_rewriter(mk_lambda_type_rewriter(m_rw),
                                   mk_lambda_body_rewriter(m_rw));
    return rw(env, ctx, v);
}
std::ostream & lambda_rewriter_cell::display(std::ostream & out) const {
    out << "Lambda_RW(" << m_rw << ")";
    return out;
}

// Pi Type Rewriter
pi_type_rewriter_cell::pi_type_rewriter_cell(rewriter const & rw)
    :rewriter_cell(rewriter_kind::PiType), m_rw(rw) { }
pi_type_rewriter_cell::~pi_type_rewriter_cell() { }

pair<expr, expr> pi_type_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    if (!is_pi(v))
        throw rewriter_exception();
    expr const & ty = abst_domain(v);
    pair<expr, expr> result = m_rw(env, ctx, ty);
    expr const & new_ty = result.first;
    light_checker lc(env);
    expr const & ty_of_v = lc(v, ctx);
    if (ty != new_ty) {
        expr const & new_v = mk_pi(abst_name(v), new_ty, abst_body(v));
        expr const & ty_of_ty = lc(ty, ctx);
        expr proof = Subst(ty_of_ty, ty, new_ty,
                           Fun({Const("x"), ty_of_ty},
                               Eq(mk_pi(abst_name(v), ty, abst_body(v)),
                                  mk_pi(abst_name(v), Const("x"), abst_body(v)))),
                           Refl(ty_of_v, v),
                           result.second);
        return make_pair(new_v, proof);
    } else {
        return make_pair(v, Refl(ty_of_v, v));
    }
}
std::ostream & pi_type_rewriter_cell::display(std::ostream & out) const {
    out << "Pi_Type_RW(" << m_rw << ")";
    return out;
}

// Pi Body Rewriter
pi_body_rewriter_cell::pi_body_rewriter_cell(rewriter const & rw)
    :rewriter_cell(rewriter_kind::PiBody), m_rw(rw) { }
pi_body_rewriter_cell::~pi_body_rewriter_cell() { }

pair<expr, expr> pi_body_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    if (!is_pi(v))
        throw rewriter_exception();
    expr const & body = abst_body(v);
    name const & n = abst_name(v);
    expr const & ty = abst_domain(v);
    context new_ctx = extend(ctx, n, ty);
    pair<expr, expr> result = m_rw(env, new_ctx, body);
    light_checker lc(env);
    expr const & ty_of_v = lc(v, ctx);
    expr const & new_body = result.first;
    if (body != new_body) {
        expr const & new_v = mk_pi(n, ty, new_body);
        expr const & ty_of_body = lc(body, new_ctx);
        expr proof = Subst(ty_of_body, body, new_body,
                           Fun({Const("x"), ty_of_body},
                               Eq(mk_pi(abst_name(v), ty, abst_body(v)),
                                  mk_pi(abst_name(v), ty, Const("x")))),
                           Refl(ty_of_v, v),
                           result.second);
        return make_pair(new_v, proof);
    } else {
        return make_pair(v, Refl(ty_of_v, v));
    }
}
std::ostream & pi_body_rewriter_cell::display(std::ostream & out) const {
    out << "Pi_Body_RW(" << m_rw << ")";
    return out;
}

// Pi Rewriter
pi_rewriter_cell::pi_rewriter_cell(rewriter const & rw)
    :rewriter_cell(rewriter_kind::Pi), m_rw(rw) { }
pi_rewriter_cell::~pi_rewriter_cell() { }
pair<expr, expr> pi_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    if (!is_pi(v))
        throw rewriter_exception();
    rewriter rw = mk_then_rewriter(mk_pi_type_rewriter(m_rw),
                                   mk_pi_body_rewriter(m_rw));
    return rw(env, ctx, v);
}
std::ostream & pi_rewriter_cell::display(std::ostream & out) const {
    out << "Pi_RW(" << m_rw << ")";
    return out;
}

// Let Type rewriter
let_type_rewriter_cell::let_type_rewriter_cell(rewriter const & rw)
    :rewriter_cell(rewriter_kind::LetType), m_rw(rw) { }
let_type_rewriter_cell::~let_type_rewriter_cell() { }
pair<expr, expr> let_type_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    if (!is_let(v))
        throw rewriter_exception();
    expr const & ty = let_type(v);
    pair<expr, expr> result = m_rw(env, ctx, ty);
    expr const & new_ty = result.first;
    light_checker lc(env);
    expr const & ty_of_v = lc(v, ctx);
    if (ty != new_ty) {
        expr const & new_v = mk_let(let_name(v), new_ty, let_value(v), let_body(v));
        expr const & ty_of_ty = lc(ty, ctx);
        expr proof = Subst(ty_of_ty, ty, new_ty,
                           Fun({Const("x"), ty_of_ty},
                               Eq(mk_let(let_name(v), ty, let_value(v), let_body(v)),
                                  mk_let(let_name(v), Const("x"), let_value(v), let_body(v)))),
                           Refl(ty_of_v, v),
                           result.second);
        return make_pair(new_v, proof);
    } else {
        return make_pair(v, Refl(ty_of_v, v));
    }
}
std::ostream & let_type_rewriter_cell::display(std::ostream & out) const {
    out << "Let_Type_RW(" << m_rw << ")";
    return out;
}

// Let Value rewriter
let_value_rewriter_cell::let_value_rewriter_cell(rewriter const & rw)
    :rewriter_cell(rewriter_kind::LetValue), m_rw(rw) { }
let_value_rewriter_cell::~let_value_rewriter_cell() { }
pair<expr, expr> let_value_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    if (!is_let(v))
        throw rewriter_exception();
    expr const & val = let_value(v);
    pair<expr, expr> result = m_rw(env, ctx, val);
    expr const & new_val = result.first;
    light_checker lc(env);
    expr const & ty_of_v = lc(v, ctx);
    if (val != new_val) {
        expr const & new_v = mk_let(let_name(v), let_type(v), new_val, let_body(v));
        expr const & ty_of_val = lc(val, ctx);
        expr proof = Subst(ty_of_val, val, new_val,
                           Fun({Const("x"), ty_of_val},
                               Eq(mk_let(let_name(v), let_type(v), let_value(v), let_body(v)),
                                  mk_let(let_name(v), let_type(v), Const("x"), let_body(v)))),
                           Refl(ty_of_v, v),
                           result.second);
        return make_pair(new_v, proof);
    } else {
        return make_pair(v, Refl(ty_of_v, v));
    }
}
std::ostream & let_value_rewriter_cell::display(std::ostream & out) const {
    out << "Let_Value_RW(" << m_rw << ")";
    return out;
}

// Let Body rewriter
let_body_rewriter_cell::let_body_rewriter_cell(rewriter const & rw)
    :rewriter_cell(rewriter_kind::LetBody), m_rw(rw) { }
let_body_rewriter_cell::~let_body_rewriter_cell() { }
pair<expr, expr> let_body_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    if (!is_let(v))
        throw rewriter_exception();

    expr const & body = let_body(v);
    name const & n = let_name(v);
    expr const & ty = let_type(v);
    expr const & val = let_value(v);
    context new_ctx = extend(ctx, n, ty);
    pair<expr, expr> result = m_rw(env, new_ctx, body);
    light_checker lc(env);
    expr const & ty_of_v = lc(v, ctx);
    expr const & new_body = result.first;
    if (body != new_body) {
        expr const & new_v = mk_let(n, ty, val, new_body);
        expr const & ty_of_body = lc(body, new_ctx);
        expr proof = Subst(ty_of_body, body, new_body,
                           Fun({Const("x"), ty_of_body},
                               Eq(mk_let(let_name(v), let_type(v), let_value(v), let_body(v)),
                                  mk_let(let_name(v), let_type(v), let_value(v), Const("x")))),
                           Refl(ty_of_v, v),
                           result.second);
        return make_pair(new_v, proof);
    } else {
        return make_pair(v, Refl(ty_of_v, v));
    }
}
std::ostream & let_body_rewriter_cell::display(std::ostream & out) const {
    out << "Let_Body_RW(" << m_rw << ")";
    return out;
}

// Let rewriter
let_rewriter_cell::let_rewriter_cell(rewriter const & rw)
    :rewriter_cell(rewriter_kind::Let), m_rw(rw) { }
let_rewriter_cell::~let_rewriter_cell() { }
pair<expr, expr> let_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    if (!is_let(v))
        throw rewriter_exception();
    rewriter rw = mk_then_rewriter({mk_let_type_rewriter(m_rw),
                                    mk_let_value_rewriter(m_rw),
                                    mk_let_body_rewriter(m_rw)});
    return rw(env, ctx, v);
}
std::ostream & let_rewriter_cell::display(std::ostream & out) const {
    out << "Let_RW(" << m_rw << ")";
    return out;
}

// Fail rewriter
fail_rewriter_cell::fail_rewriter_cell():rewriter_cell(rewriter_kind::Fail) { }
fail_rewriter_cell::~fail_rewriter_cell() { }
pair<expr, expr> fail_rewriter_cell::operator()(environment const &, context &, expr const &) const throw(rewriter_exception) {
    throw rewriter_exception();
}
std::ostream & fail_rewriter_cell::display(std::ostream & out) const {
    out << "Fail_RW()";
    return out;
}

// Success rewriter (trivial)
success_rewriter_cell::success_rewriter_cell():rewriter_cell(rewriter_kind::Success) { }
success_rewriter_cell::~success_rewriter_cell() { }
pair<expr, expr> success_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    expr const & t = light_checker(env)(v, ctx);
    return make_pair(v, Refl(t, v));
}
std::ostream & success_rewriter_cell::display(std::ostream & out) const {
    out << "Success_RW()";
    return out;
}

// Repeat rewriter
repeat_rewriter_cell::repeat_rewriter_cell(rewriter const & rw):rewriter_cell(rewriter_kind::Repeat), m_rw(rw) { }
repeat_rewriter_cell::~repeat_rewriter_cell() { }
pair<expr, expr> repeat_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    pair<expr, expr> result = mk_success_rewriter()(env, ctx, v);
    light_checker lc(env);
    try {
        while (true) {
            pair<expr, expr> new_result = m_rw(env, ctx, result.first);
            if (result.first == new_result.first)
                break;
            expr const & ty = lc(v, ctx);
            result = make_pair(new_result.first,
                               Trans(ty, v, result.first, new_result.first, result.second, new_result.second));
        }
    } catch (rewriter_exception &) {
        return result;
    }
    return result;
}
std::ostream & repeat_rewriter_cell::display(std::ostream & out) const {
    out << "Repeat_RW(" << m_rw << ")";
    return out;
}

rewriter mk_theorem_rewriter(expr const & type, expr const & body) {
    return rewriter(new theorem_rewriter_cell(type, body));
}
rewriter mk_then_rewriter(rewriter const & rw1, rewriter const & rw2) {
    return rewriter(new then_rewriter_cell(rw1, rw2));
}
rewriter mk_then_rewriter(std::initializer_list<rewriter> const & l) {
    return rewriter(new then_rewriter_cell(l));
}
rewriter mk_try_rewriter(rewriter const & rw) {
    return rewriter(new try_rewriter_cell({rw}));
}
rewriter mk_try_rewriter(rewriter const & rw1, rewriter const & rw2) {
    return rewriter(new try_rewriter_cell(rw1, rw2));
}
rewriter mk_try_rewriter(std::initializer_list<rewriter> const & l) {
    return rewriter(new try_rewriter_cell(l));
}
rewriter mk_orelse_rewriter(rewriter const & rw1, rewriter const & rw2) {
    return rewriter(new orelse_rewriter_cell(rw1, rw2));
}
rewriter mk_orelse_rewriter(std::initializer_list<rewriter> const & l) {
    return rewriter(new orelse_rewriter_cell(l));
}
rewriter mk_app_rewriter(rewriter const & rw) {
    return rewriter(new app_rewriter_cell(rw));
}
rewriter mk_lambda_type_rewriter(rewriter const & rw) {
    return rewriter(new lambda_type_rewriter_cell(rw));
}
rewriter mk_lambda_body_rewriter(rewriter const & rw) {
    return rewriter(new lambda_body_rewriter_cell(rw));
}
rewriter mk_lambda_rewriter(rewriter const & rw) {
    return rewriter(new lambda_rewriter_cell(rw));
}
rewriter mk_pi_type_rewriter(rewriter const & rw) {
    return rewriter(new pi_type_rewriter_cell(rw));
}
rewriter mk_pi_body_rewriter(rewriter const & rw) {
    return rewriter(new pi_body_rewriter_cell(rw));
}
rewriter mk_pi_rewriter(rewriter const & rw) {
    return rewriter(new pi_rewriter_cell(rw));
}
rewriter mk_let_type_rewriter(rewriter const & rw) {
    return rewriter(new let_type_rewriter_cell(rw));
}
rewriter mk_let_value_rewriter(rewriter const & rw) {
    return rewriter(new let_value_rewriter_cell(rw));
}
rewriter mk_let_body_rewriter(rewriter const & rw) {
    return rewriter(new let_body_rewriter_cell(rw));
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
