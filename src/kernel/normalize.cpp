/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "normalize.h"
#include "expr.h"
#include "context.h"
#include "environment.h"
#include "scoped_map.h"
#include "builtin.h"
#include "free_vars.h"
#include "list.h"
#include "buffer.h"
#include "trace.h"
#include "exception.h"

namespace lean {

class svalue;
typedef list<svalue> value_stack; //!< Normalization stack
enum class svalue_kind { Expr, Closure, BoundedVar };
/** \brief Stack value: simple expressions, closures and bounded variables. */
class svalue {
    svalue_kind m_kind;
    unsigned    m_bvar;
    expr        m_expr;
    value_stack m_ctx;
public:
    svalue() {}
    explicit svalue(expr const & e):              m_kind(svalue_kind::Expr), m_expr(e) {}
    explicit svalue(unsigned k):                  m_kind(svalue_kind::BoundedVar), m_bvar(k) {}
    svalue(expr const & e, value_stack const & c):m_kind(svalue_kind::Closure), m_expr(e), m_ctx(c) { lean_assert(is_lambda(e)); }

    svalue_kind kind() const { return m_kind; }

    bool is_expr() const        { return kind() == svalue_kind::Expr; }
    bool is_closure() const     { return kind() == svalue_kind::Closure; }
    bool is_bounded_var() const { return kind() == svalue_kind::BoundedVar; }

    expr  const & get_expr() const { lean_assert(is_expr() || is_closure()); return m_expr; }
    value_stack const & get_ctx()  const { lean_assert(is_closure());              return m_ctx; }
    unsigned get_var_idx()   const { lean_assert(is_bounded_var());          return m_bvar; }
};

svalue_kind         kind(svalue const & v)     { return v.kind(); }
expr const &        to_expr(svalue const & v)  { return v.get_expr(); }
value_stack const & stack_of(svalue const & v) { return v.get_ctx(); }
unsigned            to_bvar(svalue const & v)  { return v.get_var_idx(); }

value_stack extend(value_stack const & s, svalue const & v) { return cons(v, s); }

/** \brief Expression normalizer. */
class normalize_fn {
    typedef scoped_map<expr, svalue, expr_hash, expr_eqp> cache;

    environment const & m_env;
    context     const & m_ctx;
    cache               m_cache;

    svalue lookup(value_stack const & s, unsigned i, unsigned k) {
        unsigned j = i;
        value_stack const * it1 = &s;
        while (*it1) {
            if (j == 0)
                return head(*it1);
            --j;
            it1 = &tail(*it1);
        }
        auto p = lookup_ext(m_ctx, j);
        context_entry const & entry = p.first;
        context const & entry_c     = p.second;
        if (entry.get_body())
            return svalue(::lean::normalize(entry.get_body(), m_env, entry_c));
        else
            return svalue(length(entry_c));
    }

    /** \brief Convert the closure \c a into an expression using the given stack in a context that contains \c k binders. */
    expr reify_closure(expr const & a, value_stack const & s, unsigned k) {
        lean_assert(is_lambda(a));
        expr new_t = reify(normalize(abst_domain(a), s, k), k);
        expr new_b = reify(normalize(abst_body(a), extend(s, svalue(k)), k+1), k+1);
        return mk_lambda(abst_name(a), new_t, new_b);
#if 0
        // Eta-reduction + Cumulativity + Set theoretic interpretation is unsound.
        // Example:
        //   f : (Type 2) -> (Type 2)
        //   (lambda (x : (Type 1)) (f x)) : (Type 1) -> (Type 2)
        // The domains of these two terms are different. So, they must have different denotations.
        // However, by eta-reduction, we have:
        //     (lambda (x : (Type 1)) (f x)) == f
        // For now, we will disable it.
        // REMARK: we can workaround this problem by applying only when the domain of f is equal
        // to the domain of the lambda abstraction.
        //
        if (is_app(new_b)) {
            // (lambda (x:T) (app f ... (var 0)))
            // check eta-rule applicability
            unsigned n = num_args(new_b);
            if (is_var(arg(new_b, n - 1), 0) &&
                std::all_of(begin_args(new_b),
                            end_args(new_b) - 1,
                            [](expr const & arg) { return !has_free_var(arg, 0); })) {
                if (n == 2)
                    return lower_free_vars(arg(new_b, 0), 1);
                else
                    return lower_free_vars(app(n - 1, begin_args(new_b)), 1);
            }
            return lambda(abst_name(a), new_t, new_b);
        } else {
            return lambda(abst_name(a), new_t, new_b);
        }
#endif
    }

    /** \brief Convert the value \c v back into an expression in a context that contains \c k binders. */
    expr reify(svalue const & v, unsigned k) {
        lean_trace("normalize", tout << "Reify kind: " << static_cast<unsigned>(v.kind()) << "\n";
                   if (v.is_bounded_var()) tout << "#" << to_bvar(v); else tout << to_expr(v); tout << "\n";);
        switch (v.kind()) {
        case svalue_kind::Expr:       return to_expr(v);
        case svalue_kind::BoundedVar: return mk_var(k - to_bvar(v) - 1);
        case svalue_kind::Closure:    return reify_closure(to_expr(v), stack_of(v), k);
        }
        lean_unreachable();
        return expr();
    }

    /** \brief Normalize the expression \c a in a context composed of stack \c s and \c k binders. */
    svalue normalize(expr const & a, value_stack const & s, unsigned k) {
        lean_trace("normalize", tout << "Normalize, k: " << k << "\n" << a << "\n";);

        bool shared = false;
        if (is_shared(a)) {
            shared = true;
            auto it = m_cache.find(a);
            if (it != m_cache.end())
                return it->second;
        }

        svalue r;
        switch (a.kind()) {
        case expr_kind::Var:
            r = lookup(s, var_idx(a), k);
            break;
        case expr_kind::Constant: {
            named_object const & obj = m_env.get_object(const_name(a));
            if (obj.is_definition() && !obj.is_opaque()) {
                r = normalize(obj.get_value(), value_stack(), 0);
            }
            else {
                r = svalue(a);
            }
            break;
        }
        case expr_kind::Type: case expr_kind::Value:
            r = svalue(a);
            break;
        case expr_kind::App: {
            svalue f    = normalize(arg(a, 0), s, k);
            unsigned i = 1;
            unsigned n = num_args(a);
            while (true) {
                if (f.is_closure()) {
                    // beta reduction
                    expr const & fv = to_expr(f);
                    lean_trace("normalize", tout << "beta reduction...\n" << fv << "\n";);
                    {
                        cache::mk_scope sc(m_cache);
                        value_stack new_s = extend(stack_of(f), normalize(arg(a, i), s, k));
                        f = normalize(abst_body(fv), new_s, k);
                    }
                    if (i == n - 1) {
                        r = f;
                        break;
                    }
                    i++;
                } else {
                    buffer<expr> new_args;
                    expr new_f = reify(f, k);
                    new_args.push_back(new_f);
                    for (; i < n; i++)
                        new_args.push_back(reify(normalize(arg(a, i), s, k), k));
                    if (is_value(new_f)) {
                        expr m;
                        if (to_value(new_f).normalize(new_args.size(), new_args.data(), m)) {
                            r = svalue(m);
                            break;
                        }
                    }
                    r = svalue(mk_app(new_args.size(), new_args.data()));
                    break;
                }
            }
            break;
        }
        case expr_kind::Eq: {
            expr new_lhs = reify(normalize(eq_lhs(a), s, k), k);
            expr new_rhs = reify(normalize(eq_rhs(a), s, k), k);
            if (new_lhs == new_rhs) {
                r = svalue(mk_bool_value(true));
            } else if (is_value(new_lhs) && is_value(new_rhs)) {
                r = svalue(mk_bool_value(false));
            } else {
                r = svalue(mk_eq(new_lhs, new_rhs));
            }
            break;
        }
        case expr_kind::Lambda:
            r = svalue(a, s);
            break;
        case expr_kind::Pi: {
            expr new_t = reify(normalize(abst_domain(a), s, k), k);
            expr new_b;
            {
                cache::mk_scope sc(m_cache);
                new_b = reify(normalize(abst_body(a), extend(s, svalue(k)), k+1), k+1);
            }
            r = svalue(mk_pi(abst_name(a), new_t, new_b));
            break;
        }
        case expr_kind::Let: {
            svalue v = normalize(let_value(a), s, k);
            {
                cache::mk_scope sc(m_cache);
                r = normalize(let_body(a), extend(s, v), k+1);
            }
            break;
        }}
        if (shared) {
            m_cache.insert(a, r);
        }
        return r;
    }

public:
    normalize_fn(environment const & env, context const & ctx):
        m_env(env),
        m_ctx(ctx) {
    }

    expr operator()(expr const & e) {
        unsigned k = length(m_ctx);
        return reify(normalize(e, value_stack(), k), k);
    }
};

expr normalize(expr const & e, environment const & env, context const & ctx) {
    return normalize_fn(env, ctx)(e);
}
}
