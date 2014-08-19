/*
  Copyright (c) 2013 Microsoft Corporation.
  Copyright (c) 2013 Carnegie Mellon University.
  All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Soonho Kong
*/
#include "kernel/abstract.h"
#include "kernel/kernel.h"
#include "kernel/context.h"
#include "kernel/environment.h"
#include "kernel/expr.h"
#include "kernel/replace_fn.h"
#include "kernel/type_checker.h"
#include "library/printer.h"
#include "library/rewriter/fo_match.h"
#include "library/rewriter/rewriter.h"
#include "util/buffer.h"
#include "util/trace.h"

using std::cout;
using std::endl;
using std::initializer_list;
using std::make_pair;
using std::ostream;

namespace lean {

/**
   \brief For a lambda term v = \f$(\lambda n : ty. body)\f$ and the rewriting result
   for ty, it constructs a new rewriting result for v' = \f$(\lambda n : ty'.
   body)\f$ with the proof of v = v'.

   \param env environment
   \param ctx context
   \param v \f$(\lambda n : ty. body)\f$
   \param result_ty rewriting result of ty -- pair of ty'
          rewritten type of ty and pf_ty the proof of (ty = ty')
   \return pair of v' = \f$(\lambda n : ty'. body)\f$, and proof of v = v'
*/
pair<expr, expr> rewrite_lambda_type(environment const & env, context & ctx, expr const & v, pair<expr, expr> const & result_ty) {
    lean_assert(is_lambda(v));
    type_inferer ti(env);
    expr const & ty     = abst_domain(v);
    expr const & new_ty = result_ty.first;
    expr const & ty_v   = ti(v, ctx);
    if (ty == new_ty) {
        return make_pair(v, mk_refl_th(ty_v, v));
    } else {
        name const & n         = abst_name(v);
        expr const & body      = abst_body(v);
        // expr const & pf_ty     = result_ty.second;
        expr const & new_v     = mk_lambda(n, new_ty, body);
        // expr const & ty_ty     = ti(ty, ctx);
        // lean_assert_eq(ty_ty, ti(new_ty, ctx)); // TODO(soonhok): generalize for hetreogeneous types
        expr proof;
#if 0  // TODO(Leo): we don't have heterogeneous equality anymore
            = mk_subst_th(ty_ty, ty, new_ty,
                          Fun({Const("T"), ty_ty},
                              mk_heq(v, mk_lambda(n, Const("T"), body))),
                          mk_refl_th(ty_v, v), pf_ty);
#endif
        return make_pair(new_v, proof);
    }
}

/**
   \brief For a lambda term v = \f$(\lambda n : ty. body)\f$ and the rewriting result
   for body, it constructs a new rewriting result for v' = \f$(\lambda n : ty.
   body')\f$ with the proof of v = v'.

   \param env environment
   \param ctx context
   \param v \f$(\lambda n : ty. body)\f$
   \param result_body rewriting result of body -- pair of \c body'
          rewritten term of body and \c pf_body the proof of (body =
          body')
   \return pair of v' = \f$(\lambda n : ty. body')\f$, and proof of v = v'
*/
pair<expr, expr> rewrite_lambda_body(environment const & env, context & ctx, expr const & v, pair<expr, expr> const & result_body) {
    lean_assert(is_lambda(v));
    type_inferer ti(env);
    expr const & body     = abst_body(v);
    expr const & new_body = result_body.first;
    expr const & ty_v     = ti(v, ctx);
    if (body == new_body) {
        return make_pair(v, mk_refl_th(ty_v, v));
    } else {
        name const & n       = abst_name(v);
        expr const & ty      = abst_domain(v);
        expr const & pf_body = result_body.second;
        expr const & new_v   = mk_lambda(n, ty, new_body);
        expr const & ty_body = ti(body, extend(ctx, n, ty));
        lean_assert_eq(ty_body, ti(new_body, ctx)); // TODO(soonhok): generalize for hetreogeneous types
        expr const & proof = mk_funext_th(ty, mk_lambda(n, ty, ty_body), v, new_v, mk_lambda(n, ty, pf_body));
        return make_pair(new_v, proof);
    }
}

/**
   \brief For a lambda term v = \f$(\lambda n : ty. body)\f$ and the rewriting
   result for ty and body, it constructs a new rewriting result for v'
   = \f$(\lambda n : ty'. body')\f$ with the proof of v = v'.

   \param env environment
   \param ctx context
   \param v \f$(\lambda n : ty. body)\f$
   \param result_ty rewriting result of ty -- pair of ty'
          rewritten type of ty and pf_ty the proof of (ty = ty')
   \param result_body rewriting result of body -- pair of body'
          rewritten term of body and \c pf_body the proof of (body =
          body')
   \return pair of v' = \f$(\lambda n : ty'. body')\f$, and proof of v = v'
*/
pair<expr, expr> rewrite_lambda(environment const & env, context & /* ctx */,  expr const & v, pair<expr, expr> const & result_ty, pair<expr, expr> const & result_body) {
    lean_assert(is_lambda(v));
    type_inferer ti(env);
    name const & n         = abst_name(v);
    // expr const & ty        = abst_domain(v);
    // expr const & body      = abst_body(v);
    expr const & new_ty    = result_ty.first;
    // expr const & pf_ty     = result_ty.second;
    expr const & new_body  = result_body.first;
    // expr const & pf_body   = result_body.second;
    // expr const & ty_ty     = ti(ty, ctx);
    // expr const & ty_body   = ti(body, ctx);
    // expr const & ty_v      = ti(v, ctx);
    // expr const & new_v1    = mk_lambda(n, new_ty, body);
    // expr const & ty_new_v1 = ti(v, ctx);
    expr const & new_v2    = mk_lambda(n, new_ty, new_body);
    // proof1 : v = new_v1

    expr proof;
#if 0 // TODO(Leo): we don't have heterogeneous equality anymore
    expr proof1 = mk_subst_th(ty_ty, ty, new_ty,
                                         Fun({Const("T"), ty_ty},
                                             mk_heq(v, mk_lambda(n, Const("T"), body))),
                                         mk_refl_th(ty_v, v),
                                         pf_ty);
    expr proof2 = mk_subst_th(ty_body, body, new_body,
                                         Fun({Const("e"), ty_body},
                                             mk_heq(new_v1, mk_lambda(n, new_ty, Const("e")))),
                                         mk_refl_th(ty_new_v1, new_v1),
                                         pf_body);
    expr const & proof     = mk_trans_th(ty_v, v, new_v1, new_v2, proof1, proof2);
#endif
    return make_pair(new_v2, proof);
}

/**
   \brief For a Pi term v = \f$(\Pi n : ty. body)\f$ and the rewriting
   result for ty, it constructs a new rewriting result for v'
   = \f$(\Pi n : ty'. body)\f$ with the proof of v = v'.

   \param env environment
   \param ctx context
   \param v \f$(\Pi n : ty. body)\f$
   \param result_ty rewriting result of ty -- pair of ty'
          rewritten type of ty and pf_ty the proof of (ty = ty')
   \return pair of v' = \f$(\Pi n : ty'. body)\f$, and proof of v = v'
*/
pair<expr, expr> rewrite_pi_type(environment const & env, context & /* ctx */, expr const & v, pair<expr, expr> const & result_ty) {
    lean_assert(is_pi(v));
    type_inferer ti(env);
    name const & n      = abst_name(v);
    // expr const & ty     = abst_domain(v);
    expr const & body   = abst_body(v);
    expr const & new_ty = result_ty.first;
    // expr const & pf     = result_ty.second;
    expr const & new_v  = mk_pi(n, new_ty, body);
    // expr const & ty_ty  = ti(ty, ctx);
    // expr const & ty_v   = ti(v, ctx);
    expr proof;
#if 0 // TODO(Leo): HEq is gone
    = mk_subst_th(ty_ty, ty, new_ty,
                                      Fun({Const("T"), ty_ty},
                                          mk_heq(v, mk_pi(n, Const("T"), body))),
                                      mk_refl_th(ty_v, v),
                                      pf);
#endif
    return make_pair(new_v, proof);
}

/**
   \brief For a Pi term v = \f$(\Pi n : ty. body)\f$ and the rewriting
   result for body, it constructs a new rewriting result for v'
   = \f$(\Pi n : ty. body')\f$ with the proof of v = v'.

   \param env environment
   \param ctx context
   \param v \f$(\Pi n : ty. body)\f$
   \param result_body rewriting result of body -- pair of body'
          rewritten term of body and \c pf_body the proof of (body =
          body')
   \return pair of v' = \f$(\Pi n : ty. body')\f$, and proof of v = v'
*/
pair<expr, expr> rewrite_pi_body(environment const & env, context & /* ctx */, expr const & v, pair<expr, expr> const & result_body) {
    lean_assert(is_pi(v));
    type_inferer ti(env);
    name const & n        = abst_name(v);
    expr const & ty       = abst_domain(v);
    // expr const & body     = abst_body(v);
    expr const & new_body = result_body.first;
    // expr const & pf       = result_body.second;
    expr const & new_v    = mk_pi(n, ty, new_body);
    // expr const & ty_body  = ti(body, extend(ctx, n, ty));
    // expr const & ty_v     = ti(v, ctx);
    expr proof;
#if 0 // TODO(Leo): HEq is gone
    expr const & proof    = mk_subst_th(ty_body, body, new_body,
                                  Fun({Const("e"), ty_body},
                                      mk_heq(v, mk_pi(n, ty, Const("e")))),
                                  mk_refl_th(ty_v, v),
                                  pf);
#endif
    return make_pair(new_v, proof);
}

/**
   \brief For a Pi term v = \f$(\Pi n : ty. body)\f$ and the rewriting
   result for ty and body, it constructs a new rewriting result for v'
   = \f$(\Pi n : ty'. body')\f$ with the proof of v = v'.

   \param env environment
   \param ctx context
   \param v \f$(\Pi n : ty. body)\f$
   \param result_ty rewriting result of ty -- pair of ty'
          rewritten type of ty and pf_ty the proof of (ty = ty')
   \param result_body rewriting result of body -- pair of body'
          rewritten term of body and \c pf_body the proof of (body =
          body')
   \return pair of v' = \f$(\Pi n : ty'. body')\f$, and proof of v = v'
*/
pair<expr, expr> rewrite_pi(environment const & env, context & /*ctx*/, expr const & v, pair<expr, expr> const & result_ty, pair<expr, expr> const & result_body) {
    lean_assert(is_pi(v));
    type_inferer ti(env);
    name const & n         = abst_name(v);
    // expr const & ty        = abst_domain(v);
    // expr const & body      = abst_body(v);
    expr const & new_ty    = result_ty.first;
    // expr const & pf_ty     = result_ty.second;
    expr const & new_body  = result_body.first;
    // expr const & pf_body   = result_body.second;
    // expr const & ty_ty     = ti(ty, ctx);
    // expr const & ty_body   = ti(body, ctx);
    // expr const & ty_v      = ti(v, ctx);
    // expr const & new_v1    = mk_pi(n, new_ty, body);
    // expr const & ty_new_v1 = ti(v, ctx);
    expr const & new_v2    = mk_pi(n, new_ty, new_body);
    expr proof;
#if 0 // TODO(Leo): HEq is gone
    expr const & proof1    = mk_subst_th(ty_ty, ty, new_ty,
                                   Fun({Const("T"), ty_ty},
                                       mk_heq(v, mk_pi(n, Const("T"), body))),
                                   mk_refl_th(ty_v, v),
                                   pf_ty);
    expr const & proof2    = mk_subst_th(ty_body, body, new_body,
                                   Fun({Const("e"), ty_body},
                                       mk_heq(new_v1, mk_pi(n, new_ty, Const("e")))),
                                   mk_refl_th(ty_new_v1, new_v1),
                                   pf_body);
    expr const & proof     = mk_trans_th(ty_v, v, new_v1, new_v2, proof1, proof2);
#endif
    return make_pair(new_v2, proof);
}

/**
   \brief For a lambda term v = (let n : ty = val in body) and the rewriting result
   for ty, it constructs a new rewriting result for v' = (let n : ty'
   = val in body) with the proof of v = v'.

   \param env environment
   \param ctx context
   \param v (let n : ty = val in body)
   \param result_ty rewriting result of ty -- pair of ty'
          rewritten type of ty and \c pf_ty the proof of (ty = ty')
   \return pair of v' = (let n : ty' = val in body), and proof of v = v'
*/
pair<expr, expr> rewrite_let_type(environment const & env, context & /* ctx */, expr const & v, pair<expr, expr> const & result_ty) {
    lean_assert(is_let(v));
    type_inferer ti(env);
    if (!let_type(v)) {
        name const & n       = let_name(v);
        // expr const & ty      = *let_type(v);
        expr const & val     = let_value(v);
        expr const & body    = let_body(v);
        expr const & new_ty  = result_ty.first;
        // expr const & pf      = result_ty.second;
        expr const & new_v   = mk_let(n, new_ty, val, body);
        // expr const & ty_ty   = ti(ty, ctx);
        // expr const & ty_v    = ti(v, ctx);
        expr proof;
#if 0 // TODO(Leo): HEq is gone
        expr const & proof   = mk_subst_th(ty_ty, ty, new_ty,
                                     Fun({Const("x"), ty_ty},
                                         mk_heq(v, mk_let(n, Const("x"), val, body))),
                                     mk_refl_th(ty_v, v),
                                     pf);
#endif
        return make_pair(new_v, proof);
    } else {
        throw rewriter_exception();
    }
}

/**
   \brief For a lambda term v = (let n : ty = val in body) and the rewriting result
   for val, it constructs a new rewriting result for v' = (let n : ty
   = val' in body) with the proof of v = v'.

   \param env environment
   \param ctx context
   \param v (let n : ty = val in body)
   \param result_value rewriting result of val -- pair of val'
          rewritten term of val and \c pf_val the proof of (val = val')
   \return pair of v' = (let n : ty = val' in body), and proof of v = v'
*/
pair<expr, expr> rewrite_let_value(environment const & env, context & /* ctx */, expr const & v, pair<expr, expr> const & result_value) {
    lean_assert(is_let(v));
    type_inferer ti(env);
    name const & n       = let_name(v);
    optional<expr> const & ty = let_type(v);
    // expr const & val     = let_value(v);
    expr const & body    = let_body(v);
    expr const & new_val = result_value.first;
    // expr const & pf      = result_value.second;
    expr const & new_v   = mk_let(n, ty, new_val, body);
    // expr const & ty_val  = ti(val, ctx);
    // expr const & ty_v    = ti(v, ctx);
    expr proof;
    #if 0 // TODO(Leo): HEq is gone
    expr const & proof   = mk_subst_th(ty_val, val, new_val,
                                 Fun({Const("x"), ty_val},
                                     mk_heq(v, mk_let(n, ty, Const("x"), body))),
                                 mk_refl_th(ty_v, v),
                                 pf);
    #endif
    return make_pair(new_v, proof);
}

/**
   \brief For a lambda term v = (let n : ty = val in body) and the rewriting result
   for body, it constructs a new rewriting result for v' = (let n : ty
   = val in body') with the proof of v = v'.

   \param env environment
   \param ctx context
   \param v (let n : ty = val in body)
   \param result_body rewriting result of body -- pair of \c body'
          rewritten term of body and \c pf_body the proof of (body =
          body')
   \return pair of v' = (let n : ty = val in body'), and proof of v = v'
*/
pair<expr, expr> rewrite_let_body(environment const & env, context & /* ctx */, expr const & v, pair<expr, expr> const & result_body) {
    lean_assert(is_let(v));
    type_inferer ti(env);
    name const & n        = let_name(v);
    optional<expr> const & ty = let_type(v);
    expr const & val      = let_value(v);
    // expr const & body     = let_body(v);
    expr const & new_body = result_body.first;
    // expr const & pf       = result_body.second;
    expr const & new_v    = mk_let(n, ty, val, new_body);
    // expr const & ty_body  = ti(body, extend(ctx, n, ty, body));
    // expr const & ty_v     = ti(v, ctx);
    expr proof;
#if 0 // TODO(Leo): HEq is gone
    expr const & proof    = mk_subst_th(ty_body, body, new_body,
                                  Fun({Const("e"), ty_body},
                                      mk_heq(v, mk_let(n, ty, val, Const("e")))),
                                  mk_refl_th(ty_v, v),
                                  pf);
#endif
    return make_pair(new_v, proof);
}

/**
   \brief For a lambda term v = (e_0 e_1 ... e_n) and the rewriting results
   for each e_i, it constructs a new rewriting result for v' = (e'_0
   e'_1 ... e'_n) with the proof of v = v'.

   \param env environment
   \param ctx context
   \param v (e_0 e_1 ... e_n)
   \param results rewriting result foe each e_i -- pair of e'_i
          rewritten term of e_i and \c pf_e_i the proof of (e_i = e'_i)
   \return pair of v' = (e'_0 e'_1 ... e'_n), and proof of v = v'
*/
pair<expr, expr> rewrite_app(environment const & env, context & ctx, expr const & v, buffer<pair<expr, expr>> const & results ) {
    type_inferer ti(env);
    expr f = arg(v, 0);
    expr new_f = results[0].first;
    expr pf = results[0].second;
    for (unsigned i = 1; i < results.size(); i++) {
        expr const & f_ty = ti(f, ctx);
        lean_assert(is_pi(f_ty));
        expr const & f_ty_domain = abst_domain(f_ty); // A
        expr f_ty_body = mk_lambda(abst_name(f_ty), f_ty_domain, abst_body(f_ty)); // B
        expr const & e_i = arg(v, i);
        expr const & new_e_i = results[i].first;
        expr const & pf_e_i  = results[i].second;
        bool f_changed = f != new_f;
        if (f_changed) {
            if (arg(v, i) != results[i].first) {
                // congr : Pi (A : Type u) (B : A -> Type u) (f g : Pi
                // (x : A) B x) (a b : A) (H1 : f = g) (H2 : a = b), f
                // a = g b
                pf = mk_congr_th(f_ty_domain, f_ty_body, f, new_f, e_i, new_e_i, pf, pf_e_i);
            } else {
                // congr1 : Pi (A : Type u) (B : A -> Type u) (f g: Pi
                // (x : A) B x) (a : A) (H : f = g), f a = g a
                pf = mk_congr1_th(f_ty_domain, f_ty_body, f, new_f, e_i, pf);
            }
        } else {
            if (arg(v, i) != results[i].first) {
                // congr2 : Pi (A : Type u) (B : A -> Type u)  (a b : A) (f : Pi (x : A) B x) (H : a = b), f a = f b
                pf = mk_congr2_th(f_ty_domain, f_ty_body, e_i, new_e_i, f, pf_e_i);
            } else {
                // refl
                pf = mk_refl_th(ti(f(e_i), ctx), f(e_i));
            }
        }
        f = f (e_i);
        new_f = new_f (new_e_i);
    }
    return make_pair(new_f, pf);
}

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
#if 0 // HEq is gone
    if (!is_heq(m_pattern)) {
        lean_trace("rewriter", tout << "Theorem " << m_type << " is not in the form of "
                   << "Pi (x_1 : t_1 ... x_n : t_n), pattern = rhs" << endl;);
    }
    m_rhs = heq_rhs(m_pattern);
    m_pattern = heq_lhs(m_pattern);

    lean_trace("rewriter", tout << "Number of Arg = " << m_num_args << endl;);
#endif
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
ostream & theorem_rewriter_cell::display(ostream & out) const {
    out << "Thm_RW(" << m_type << ", " << m_body << ")";
    return out;
}

// OrElse Rewriter
orelse_rewriter_cell::orelse_rewriter_cell(rewriter const & rw1, rewriter const & rw2)
    :rewriter_cell(rewriter_kind::OrElse), m_rwlist({rw1, rw2}) { }
orelse_rewriter_cell::orelse_rewriter_cell(initializer_list<rewriter> const & l)
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
ostream & orelse_rewriter_cell::display(ostream & out) const {
    out << "Or_RW({";
    for (rewriter const & rw : m_rwlist) { out << rw << "; "; }
    out << "})";
    return out;
}

// Then Rewriter
then_rewriter_cell::then_rewriter_cell(rewriter const & rw1, rewriter const & rw2)
    :rewriter_cell(rewriter_kind::Then), m_rwlist({rw1, rw2}) { }
then_rewriter_cell::then_rewriter_cell(initializer_list<rewriter> const & l)
    :rewriter_cell(rewriter_kind::Then), m_rwlist(l) {
    lean_assert(l.size() >= 2);
}
then_rewriter_cell::~then_rewriter_cell() { }
pair<expr, expr> then_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    pair<expr, expr> result = car(m_rwlist)(env, ctx, v);
    pair<expr, expr> new_result = result;
    for (rewriter const & rw : cdr(m_rwlist)) {
        new_result = rw(env, ctx, result.first);
        expr const & ty = type_inferer(env)(v, ctx);
        if (v != new_result.first) {
            result = make_pair(new_result.first,
                               mk_trans_th(ty, v, result.first, new_result.first, result.second, new_result.second));
        }
    }
    return result;
}
ostream & then_rewriter_cell::display(ostream & out) const {
    out << "Then_RW({";
    for (rewriter const & rw : m_rwlist) { out << rw << "; "; }
    out << "})";
    return out;
}

// Try Rewriter
try_rewriter_cell::try_rewriter_cell(rewriter const & rw1, rewriter const & rw2)
    :rewriter_cell(rewriter_kind::Try), m_rwlist({rw1, rw2}) { }
try_rewriter_cell::try_rewriter_cell(initializer_list<rewriter> const & l)
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
    expr const & t = type_inferer(env)(v, ctx);
    return make_pair(v, mk_refl_th(t, v));
}
ostream & try_rewriter_cell::display(ostream & out) const {
    out << "Try_RW({";
    for (rewriter const & rw : m_rwlist) { out << rw << "; "; }
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

    buffer<pair<expr, expr>> results;
    for (unsigned i = 0; i < num_args(v); i++) {
        results.push_back(m_rw(env, ctx, arg(v, i)));
    }
    return rewrite_app(env, ctx, v, results);
}

ostream & app_rewriter_cell::display(ostream & out) const {
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
    type_inferer ti(env);
    pair<expr, expr> result_ty = m_rw(env, ctx, ty);
    if (ty != result_ty.first) {
        return rewrite_lambda_type(env, ctx, v, result_ty);
    } else {
        // nothing changed
        return make_pair(v, mk_refl_th(ti(v, ctx), v));
    }
}
ostream & lambda_type_rewriter_cell::display(ostream & out) const {
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

    name const & n = abst_name(v);
    expr const & ty = abst_domain(v);
    expr const & body = abst_body(v);
    context new_ctx = extend(ctx, n, ty);
    pair<expr, expr> result_body = m_rw(env, new_ctx, body);
    if (body != result_body.first) {
        // body changed
        return rewrite_lambda_body(env, ctx, v, result_body);
    } else {
        // nothing changed
        type_inferer ti(env);
        return make_pair(v, mk_refl_th(ti(v, ctx), v));
    }
}
ostream & lambda_body_rewriter_cell::display(ostream & out) const {
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
ostream & lambda_rewriter_cell::display(ostream & out) const {
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
    pair<expr, expr> result_ty = m_rw(env, ctx, ty);
    if (ty != result_ty.first) {
        return rewrite_pi_type(env, ctx, v, result_ty);
    } else {
        // nothing changed
        type_inferer ti(env);
        return make_pair(v, mk_refl_th(ti(v, ctx), v));
    }
}
ostream & pi_type_rewriter_cell::display(ostream & out) const {
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

    name const & n = abst_name(v);
    expr const & ty = abst_domain(v);
    expr const & body = abst_body(v);
    context new_ctx = extend(ctx, n, ty);
    pair<expr, expr> result_body = m_rw(env, new_ctx, body);
    if (body != result_body.first) {
        // body changed
        return rewrite_pi_body(env, ctx, v, result_body);
    } else {
        // nothing changed
        type_inferer ti(env);
        return make_pair(v, mk_refl_th(ti(v, ctx), v));
    }
}
ostream & pi_body_rewriter_cell::display(ostream & out) const {
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
ostream & pi_rewriter_cell::display(ostream & out) const {
    out << "Pi_RW(" << m_rw << ")";
    return out;
}

// Let Type rewriter
let_type_rewriter_cell::let_type_rewriter_cell(rewriter const & rw)
    :rewriter_cell(rewriter_kind::LetType), m_rw(rw) { }
let_type_rewriter_cell::~let_type_rewriter_cell() { }
pair<expr, expr> let_type_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    if (!is_let(v) || !let_type(v))
        throw rewriter_exception();

    expr const & ty = *let_type(v);

    pair<expr, expr> result_ty = m_rw(env, ctx, ty);
    if (ty != result_ty.first) {
        // ty changed
        return rewrite_let_type(env, ctx, v, result_ty);
    } else {
        type_inferer ti(env);
        return make_pair(v, mk_refl_th(ti(v, ctx), v));
    }
}
ostream & let_type_rewriter_cell::display(ostream & out) const {
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

    expr const & val  = let_value(v);
    pair<expr, expr> result_val = m_rw(env, ctx, val);
    if (val != result_val.first) {
        // ty changed
        return rewrite_let_value(env, ctx, v, result_val);
    } else {
        type_inferer ti(env);
        return make_pair(v, mk_refl_th(ti(v, ctx), v));
    }
}
ostream & let_value_rewriter_cell::display(ostream & out) const {
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

    name const & n    = let_name(v);
    optional<expr> const & ty = let_type(v);
    expr const & body = let_body(v);
    context new_ctx = extend(ctx, n, ty, let_value(v));
    pair<expr, expr> result_body = m_rw(env, new_ctx, body);
    if (body != result_body.first) {
        return rewrite_let_body(env, ctx, v, result_body);
    } else {
        type_inferer ti(env);
        return make_pair(v, mk_refl_th(ti(v, ctx), v));
    }
}
ostream & let_body_rewriter_cell::display(ostream & out) const {
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
ostream & let_rewriter_cell::display(ostream & out) const {
    out << "Let_RW(" << m_rw << ")";
    return out;
}

// Fail rewriter
fail_rewriter_cell::fail_rewriter_cell():rewriter_cell(rewriter_kind::Fail) { }
fail_rewriter_cell::~fail_rewriter_cell() { }
pair<expr, expr> fail_rewriter_cell::operator()(environment const &, context &, expr const &) const throw(rewriter_exception) {
    throw rewriter_exception();
}
ostream & fail_rewriter_cell::display(ostream & out) const {
    out << "Fail_RW()";
    return out;
}

// Success rewriter (trivial)
success_rewriter_cell::success_rewriter_cell():rewriter_cell(rewriter_kind::Success) { }
success_rewriter_cell::~success_rewriter_cell() { }
pair<expr, expr> success_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    expr const & t = type_inferer(env)(v, ctx);
    return make_pair(v, mk_refl_th(t, v));
}
ostream & success_rewriter_cell::display(ostream & out) const {
    out << "Success_RW()";
    return out;
}

// Repeat rewriter
repeat_rewriter_cell::repeat_rewriter_cell(rewriter const & rw):rewriter_cell(rewriter_kind::Repeat), m_rw(rw) { }
repeat_rewriter_cell::~repeat_rewriter_cell() { }
pair<expr, expr> repeat_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    pair<expr, expr> result = mk_success_rewriter()(env, ctx, v);
    type_inferer ti(env);
    try {
        while (true) {
            pair<expr, expr> new_result = m_rw(env, ctx, result.first);
            if (result.first == new_result.first)
                break;
            expr const & ty = ti(v, ctx);
            result = make_pair(new_result.first,
                               mk_trans_th(ty, v, result.first, new_result.first, result.second, new_result.second));
        }
    } catch (rewriter_exception &) {
        return result;
    }
    return result;
}
ostream & repeat_rewriter_cell::display(ostream & out) const {
    out << "Repeat_RW(" << m_rw << ")";
    return out;
}

// Depth rewriter
depth_rewriter_cell::depth_rewriter_cell(rewriter const & rw):rewriter_cell(rewriter_kind::Depth), m_rw(rw) { }
depth_rewriter_cell::~depth_rewriter_cell() { }
pair<expr, expr> depth_rewriter_cell::operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) {
    return apply_rewriter_fn<decltype(m_rw)>(m_rw)(env, ctx, v);
}
ostream & depth_rewriter_cell::display(ostream & out) const {
    out << "Depth_RW(" << m_rw << ")";
    return out;
}

rewriter mk_theorem_rewriter(expr const & type, expr const & body) {
    return rewriter(new theorem_rewriter_cell(type, body));
}
rewriter mk_then_rewriter(rewriter const & rw1, rewriter const & rw2) {
    return rewriter(new then_rewriter_cell(rw1, rw2));
}
rewriter mk_then_rewriter(initializer_list<rewriter> const & l) {
    return rewriter(new then_rewriter_cell(l));
}
rewriter mk_try_rewriter(rewriter const & rw) {
    return rewriter(new try_rewriter_cell({rw}));
}
rewriter mk_try_rewriter(rewriter const & rw1, rewriter const & rw2) {
    return rewriter(new try_rewriter_cell(rw1, rw2));
}
rewriter mk_try_rewriter(initializer_list<rewriter> const & l) {
    return rewriter(new try_rewriter_cell(l));
}
rewriter mk_orelse_rewriter(rewriter const & rw1, rewriter const & rw2) {
    return rewriter(new orelse_rewriter_cell(rw1, rw2));
}
rewriter mk_orelse_rewriter(initializer_list<rewriter> const & l) {
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
rewriter mk_depth_rewriter(rewriter const & rw) {
    return rewriter(new depth_rewriter_cell(rw));
}
}
