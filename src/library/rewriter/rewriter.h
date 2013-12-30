/*
Copyright (c) 2013 Microsoft Corporation.
Copyright (c) 2013 Carnegie Mellon University.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#pragma once
#include <algorithm>
#include <utility>
#include "kernel/abstract.h"
#include "kernel/context.h"
#include "kernel/environment.h"
#include "kernel/expr.h"
#include "kernel/replace_fn.h"
#include "kernel/type_checker.h"
#include "kernel/builtin.h"
#include "library/rewriter/rewriter.h"
#include "util/exception.h"
#include "util/scoped_map.h"
// TODO(soonhok)
// FORALL
// FAIL_IF

namespace lean {

class rewriter_exception : public exception {
public:
    virtual exception * clone() const { return new rewriter_exception(); }
    virtual void rethrow() const { throw *this; }
};

enum class rewriter_kind { Theorem, OrElse, Then, Try, App,
        LambdaType, LambdaBody, Lambda,
        PiType, PiBody, Pi,
        LetType, LetValue, LetBody, Let,
        Fail, Success, Repeat, Depth };

std::pair<expr, expr> rewrite_lambda_type(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_ty);
std::pair<expr, expr> rewrite_lambda_body(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_body);
std::pair<expr, expr> rewrite_lambda(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_ty, std::pair<expr, expr> const & result_body);
std::pair<expr, expr> rewrite_pi_type(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_ty);
std::pair<expr, expr> rewrite_pi_body(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_body);
std::pair<expr, expr> rewrite_pi(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_ty, std::pair<expr, expr> const & result_body);
std::pair<expr, expr> rewrite_eq_lhs(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_lhs);
std::pair<expr, expr> rewrite_eq_rhs(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_rhs);
std::pair<expr, expr> rewrite_eq(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_lhs, std::pair<expr, expr> const & result_rhs);
std::pair<expr, expr> rewrite_let_type(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_ty);
std::pair<expr, expr> rewrite_let_value(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_value);
std::pair<expr, expr> rewrite_let_body(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_body);
std::pair<expr, expr> rewrite_app(environment const & env, context & ctx, expr const & v, buffer<std::pair<expr, expr>> const & results );

class rewriter;

class rewriter_cell {
protected:
    rewriter_kind m_kind;
    MK_LEAN_RC();
    void dealloc();
    virtual std::ostream & display(std::ostream & out) const = 0;
public:
    rewriter_cell(rewriter_kind k);
    virtual ~rewriter_cell();
    rewriter_kind kind() const { return m_kind; }
//    unsigned hash() const { return m_hash; }
    virtual std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) = 0;
    friend std::ostream & operator<<(std::ostream & out, rewriter_cell const & rw);
};

class rewriter {
private:
    rewriter_cell * m_ptr;
public:
    explicit rewriter(rewriter_cell * ptr):m_ptr(ptr) {}
    rewriter():m_ptr(nullptr) {}
    rewriter(rewriter const & r):m_ptr(r.m_ptr) {
        if (m_ptr) m_ptr->inc_ref();
    }
    rewriter(rewriter && r):m_ptr(r.m_ptr) { r.m_ptr = nullptr; }
    ~rewriter() { if (m_ptr) m_ptr->dec_ref(); }
    void release() { if (m_ptr) m_ptr->dec_ref(); m_ptr = nullptr; }
    friend void swap(rewriter & a, rewriter & b) { std::swap(a.m_ptr, b.m_ptr); }
    rewriter_kind kind() const { return m_ptr->kind(); }
    rewriter & operator=(rewriter const & s) { LEAN_COPY_REF(s); }
    rewriter & operator=(rewriter && s) { LEAN_MOVE_REF(s); }
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const {
        return (*m_ptr)(env, ctx, v);
    }
    friend std::ostream & operator<<(std::ostream & out, rewriter const & rw);
};

class theorem_rewriter_cell : public rewriter_cell {
private:
    expr const & m_type;
    expr const & m_body;
    expr m_pattern;
    expr m_rhs;
    unsigned m_num_args;
    std::ostream & display(std::ostream & out) const;

public:
    theorem_rewriter_cell(expr const & type, expr const & body);
    ~theorem_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class orelse_rewriter_cell : public rewriter_cell {
private:
    list<rewriter> m_rwlist;
    std::ostream & display(std::ostream & out) const;
public:
    orelse_rewriter_cell(rewriter const & rw1, rewriter const & rw2);
    orelse_rewriter_cell(std::initializer_list<rewriter> const & l);
    ~orelse_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class then_rewriter_cell : public rewriter_cell {
private:
    list<rewriter> m_rwlist;
    std::ostream & display(std::ostream & out) const;
public:
    then_rewriter_cell(rewriter const & rw1, rewriter const & rw2);
    then_rewriter_cell(std::initializer_list<rewriter> const & l);
    ~then_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class try_rewriter_cell : public rewriter_cell {
private:
    list<rewriter> m_rwlist;
    std::ostream & display(std::ostream & out) const;
public:
    try_rewriter_cell(rewriter const & rw1, rewriter const & rw2);
    try_rewriter_cell(std::initializer_list<rewriter> const & l);
    ~try_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class app_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    app_rewriter_cell(rewriter const & rw);
    ~app_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class lambda_type_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    lambda_type_rewriter_cell(rewriter const & rw);
    ~lambda_type_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class lambda_body_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    lambda_body_rewriter_cell(rewriter const & rw);
    ~lambda_body_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class lambda_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    lambda_rewriter_cell(rewriter const & rw);
    ~lambda_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class pi_type_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    pi_type_rewriter_cell(rewriter const & rw);
    ~pi_type_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class pi_body_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    pi_body_rewriter_cell(rewriter const & rw);
    ~pi_body_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class pi_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    pi_rewriter_cell(rewriter const & rw);
    ~pi_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};


class let_type_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    let_type_rewriter_cell(rewriter const & rw);
    ~let_type_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class let_value_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    let_value_rewriter_cell(rewriter const & rw);
    ~let_value_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class let_body_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    let_body_rewriter_cell(rewriter const & rw);
    ~let_body_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class let_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    let_rewriter_cell(rewriter const & rw);
    ~let_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class fail_rewriter_cell : public rewriter_cell {
private:
    std::ostream & display(std::ostream & out) const;
public:
    fail_rewriter_cell();
    ~fail_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class success_rewriter_cell : public rewriter_cell {
private:
    std::ostream & display(std::ostream & out) const;
public:
    success_rewriter_cell();
    ~success_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class repeat_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    repeat_rewriter_cell(rewriter const & rw);
    ~repeat_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class depth_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    depth_rewriter_cell(rewriter const & rw);
    ~depth_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

/** \brief (For debugging) Display the content of this rewriter */
inline std::ostream & operator<<(std::ostream & out, rewriter_cell const & rc) { rc.display(out); return out; }
inline std::ostream & operator<<(std::ostream & out, rewriter const & rw) { out << *(rw.m_ptr); return out; }

rewriter mk_theorem_rewriter(expr const & type, expr const & body);
rewriter mk_then_rewriter(rewriter const & rw1, rewriter const & rw2);
rewriter mk_then_rewriter(std::initializer_list<rewriter> const & l);
rewriter mk_try_rewriter(rewriter const & rw);
rewriter mk_try_rewriter(rewriter const & rw1, rewriter const & rw2);
rewriter mk_try_rewriter(std::initializer_list<rewriter> const & l);
rewriter mk_orelse_rewriter(rewriter const & rw1, rewriter const & rw2);
rewriter mk_orelse_rewriter(std::initializer_list<rewriter> const & l);
rewriter mk_app_rewriter(rewriter const & rw);
rewriter mk_lambda_type_rewriter(rewriter const & rw);
rewriter mk_lambda_body_rewriter(rewriter const & rw);
rewriter mk_lambda_rewriter(rewriter const & rw);
rewriter mk_pi_type_rewriter(rewriter const & rw);
rewriter mk_pi_body_rewriter(rewriter const & rw);
rewriter mk_pi_rewriter(rewriter const & rw);
rewriter mk_let_type_rewriter(rewriter const & rw);
rewriter mk_let_value_rewriter(rewriter const & rw);
rewriter mk_let_body_rewriter(rewriter const & rw);
rewriter mk_let_rewriter(rewriter const & rw);
rewriter mk_fail_rewriter();
rewriter mk_success_rewriter();
rewriter mk_repeat_rewriter(rewriter const & rw);
rewriter mk_depth_rewriter(rewriter const & rw);

/**
   \brief Functional for applying <tt>F</tt> to the subexpressions of a given expression.

   The signature of \c F is
   expr const &, context const & ctx, unsigned n -> expr

   F is invoked for each subexpression \c s of the input expression e.
   In a call <tt>F(s, c, n)</tt>, \c c is the context where \c s occurs,
   and \c n is the size of \c c.

   P is a "post-processing" functional object that is applied to each
   pair (old, new)
*/
template<typename RW, typename P = default_replace_postprocessor>
class apply_rewriter_fn {
    // the return type of RW()(env, ctx, e) should be std::pair<expr, expr>
    static_assert(std::is_same<typename std::result_of<decltype(std::declval<RW>())(environment const &, context &, expr const &)>::type,
                  std::pair<expr, expr>>::value,
                  "apply_rewriter_fn: the return type of RW()(env, ctx, e) should be std::pair<expr, expr>");
    // the return type of P()(e1, e2) should be void
    static_assert(std::is_same<typename std::result_of<decltype(std::declval<P>())(expr const &, expr const &)>::type,
                  void>::value,
                  "apply_rewriter_fn: the return type of P()(e1, e2) is not void");

    typedef scoped_map<expr, std::pair<expr, expr>, expr_hash, expr_eqp> cache;
    cache                      m_cache;
    RW                         m_rw;
    P                          m_post;

    std::pair<expr, expr> apply(environment const & env, context & ctx, expr const & v) {
        bool shared = false;
        if (is_shared(v)) {
            shared = true;
            auto it = m_cache.find(v);
            if (it != m_cache.end())
                return it->second;
        }

        std::pair<expr, expr> result; // m_rw(env, ctx, v);
        // if (is_eqp(v, result.first))
        type_inferer ti(env);
        expr ty_v = ti(v, ctx);

        switch (v.kind()) {
        case expr_kind::Type:
            result = m_rw(env, ctx, v);
            break;
        case expr_kind::Value:
            result = m_rw(env, ctx, v);
            break;
        case expr_kind::Constant:
            result = m_rw(env, ctx, v);
            break;
        case expr_kind::Var:
            result = m_rw(env, ctx, v);
            break;
        case expr_kind::MetaVar:
            result = m_rw(env, ctx, v);
            break;
        case expr_kind::App: {
            buffer<std::pair<expr, expr>> results;
            for (unsigned i = 0; i < num_args(v); i++) {
                results.push_back(apply(env, ctx, arg(v, i)));
            }
            result = rewrite_app(env, ctx, v, results);
            std::pair<expr, expr> tmp = m_rw(env, ctx, result.first);
            if (result.first != tmp.first) {
                tmp.second = Trans(ty_v, v, result.first, tmp.first, result.second, tmp.second);
                result = tmp;
            }
        }
            break;
        case expr_kind::Eq: {
            expr const & lhs = eq_lhs(v);
            expr const & rhs = eq_rhs(v);
            std::pair<expr, expr> result_lhs = apply(env, ctx, lhs);
            std::pair<expr, expr> result_rhs = apply(env, ctx, rhs);
            expr const & new_lhs = result_lhs.first;
            expr const & new_rhs = result_rhs.first;
            if (lhs != new_lhs) {
                if (rhs != new_rhs) {
                    // lhs & rhs changed
                    result = rewrite_eq(env, ctx, v, result_lhs, result_rhs);
                } else {
                    // only lhs changed
                    result = rewrite_eq_lhs(env, ctx, v, result_lhs);
                }
            } else {
                if (rhs != new_rhs) {
                    // only rhs changed
                    result = rewrite_eq_rhs(env, ctx, v, result_rhs);
                } else {
                    // nothing changed
                    result = std::make_pair(v, Refl(ti(v, ctx), v));
                }
            }
            std::pair<expr, expr> tmp = m_rw(env, ctx, result.first);
            if (result.first != tmp.first) {
                tmp.second = Trans(ty_v, v, result.first, tmp.first, result.second, tmp.second);
                result = tmp;
            }
        }
            break;
        case expr_kind::Lambda: {
            name const & n = abst_name(v);
            expr const & ty = abst_domain(v);
            expr const & body = abst_body(v);
            context new_ctx = extend(ctx, n, ty);
            std::pair<expr, expr> result_ty   = apply(env, ctx, ty);
            std::pair<expr, expr> result_body = apply(env, new_ctx, body);
            if (ty != result_ty.first) {
                if (body != result_body.first) {
                    // ty and body changed
                    result = rewrite_lambda(env, ctx, v, result_ty, result_body);
                } else {
                    // ty changed
                    result = rewrite_lambda_type(env, ctx, v, result_ty);
                }
            } else {
                if (body != result_body.first) {
                    // body changed
                    result = rewrite_lambda_body(env, ctx, v, result_body);
                } else {
                    // nothing changed
                    result = std::make_pair(v, Refl(ti(v, ctx), v));
                }
            }
            std::pair<expr, expr> tmp = m_rw(env, ctx, result.first);
            if (result.first != tmp.first) {
                tmp.second = Trans(ty_v, v, result.first, tmp.first, result.second, tmp.second);
                result = tmp;
            }
        }
            break;

        case expr_kind::Pi: {
            name const & n = abst_name(v);
            expr const & ty = abst_domain(v);
            expr const & body = abst_body(v);
            context new_ctx = extend(ctx, n, ty);
            std::pair<expr, expr> result_ty   = apply(env, ctx, ty);
            std::pair<expr, expr> result_body = apply(env, new_ctx, body);
            if (ty != result_ty.first) {
                if (body != result_body.first) {
                    // ty and body changed
                    result = rewrite_pi(env, ctx, v, result_ty, result_body);
                } else {
                    // ty changed
                    result = rewrite_pi_type(env, ctx, v, result_ty);
                }
            } else {
                if (body != result_body.first) {
                    // body changed
                    result = rewrite_pi_body(env, ctx, v, result_body);
                } else {
                    // nothing changed
                    result = std::make_pair(v, Refl(ti(v, ctx), v));
                }
            }
            std::pair<expr, expr> tmp = m_rw(env, ctx, result.first);
            if (result.first != tmp.first) {
                tmp.second = Trans(ty_v, v, result.first, tmp.first, result.second, tmp.second);
                result = tmp;
            }
        }
            break;
        case expr_kind::Let: {
            name const & n    = let_name(v);
            optional<expr> const & ty = let_type(v);
            expr const & val  = let_value(v);
            expr const & body = let_body(v);

            expr new_v = v;
            expr ty_v = ti(v, ctx);
            expr pf = Refl(ty_v, v);
            bool changed = false;

            if (ty) {
                std::pair<expr, expr> result_ty = apply(env, ctx, *ty);
                if (*ty != result_ty.first) {
                    // ty changed
                    result  = rewrite_let_type(env, ctx, new_v, result_ty);
                    new_v   = result.first;
                    pf      = result.second;
                    changed = true;
                }
            }

            std::pair<expr, expr> result_val = apply(env, ctx, val);
            if (val != result_val.first) {
                result = rewrite_let_value(env, ctx, new_v, result_val);
                if (changed) {
                    pf = Trans(ty_v, v, new_v, result.first, pf, result.second);
                } else {
                    pf = result.second;
                }
                new_v = result.first;
                changed = true;
            }

            context new_ctx = extend(ctx, n, ty, val);
            std::pair<expr, expr> result_body = apply(env, new_ctx, body);
            if (body != result_body.first) {
                result = rewrite_let_body(env, ctx, new_v, result_body);
                if (changed) {
                    pf = Trans(ty_v, v, new_v, result.first, pf, result.second);
                } else {
                    pf = result.second;
                }
                new_v = result.first;
                changed = true;
            }
            result = std::make_pair(new_v, pf);

            std::pair<expr, expr> tmp = m_rw(env, ctx, result.first);
            if (result.first != tmp.first) {
                tmp.second = Trans(ty_v, v, result.first, tmp.first, result.second, tmp.second);
                result = tmp;
            }
        }
            break;
        }
        if (shared)
            m_cache.insert(std::make_pair(v, result));
        return result;
    }

public:
    apply_rewriter_fn(RW const & rw, P const & p = P()):
        m_rw(rw),
        m_post(p) {
    }
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) {
        return apply(env, ctx, v);
    }
};

}
