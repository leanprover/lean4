/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <limits>
#include "util/scoped_map.h"
#include "util/list.h"
#include "util/flet.h"
#include "util/buffer.h"
#include "util/sexpr/options.h"
#include "kernel/normalizer.h"
#include "kernel/expr.h"
#include "kernel/context.h"
#include "kernel/environment.h"
#include "kernel/builtin.h"
#include "kernel/metavar.h"
#include "kernel/free_vars.h"
#include "kernel/instantiate.h"
#include "kernel/kernel_exception.h"

#ifndef LEAN_KERNEL_NORMALIZER_MAX_DEPTH
#define LEAN_KERNEL_NORMALIZER_MAX_DEPTH std::numeric_limits<unsigned>::max()
#endif

namespace lean {
static name g_kernel_normalizer_max_depth       {"kernel", "normalizer", "max_depth"};
RegisterUnsignedOption(g_kernel_normalizer_max_depth, LEAN_KERNEL_NORMALIZER_MAX_DEPTH, "(kernel) maximum recursion depth for expression normalizer");
unsigned get_normalizer_max_depth(options const & opts) {
    return opts.get_unsigned(g_kernel_normalizer_max_depth, LEAN_KERNEL_NORMALIZER_MAX_DEPTH);
}

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
class normalizer::imp {
    typedef scoped_map<expr, svalue, expr_hash, expr_eqp> cache;

    environment const &  m_env;
    context              m_ctx;
    substitution const * m_subst;
    unsigned             m_subst_timestamp;
    cache                m_cache;
    unsigned             m_max_depth;
    unsigned             m_depth;
    volatile bool        m_interrupted;

    /**
        \brief Auxiliary object for saving the current context.
        We need this to be able to process values in the context.
    */
    struct save_context {
        imp &           m_imp;
        context         m_saved_ctx;
        cache           m_saved_cache;
        save_context(imp & imp):
            m_imp(imp),
            m_saved_ctx(m_imp.m_ctx) {
            m_imp.m_cache.swap(m_saved_cache);
        }
        ~save_context() {
            m_imp.m_ctx = m_saved_ctx;
            m_imp.m_cache.swap(m_saved_cache);
        }
    };

    svalue lookup(value_stack const & s, unsigned i) {
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
        if (entry.get_body()) {
            save_context save(*this); // it restores the context and cache
            m_ctx = entry_c;
            unsigned k = m_ctx.size();
            return svalue(reify(normalize(entry.get_body(), value_stack(), k), k));
        } else {
            return svalue(entry_c.size());
        }
    }

    /** \brief Convert the closure \c a into an expression using the given stack in a context that contains \c k binders. */
    expr reify_closure(expr const & a, value_stack const & s, unsigned k) {
        lean_assert(is_lambda(a));
        expr new_t = reify(normalize(abst_domain(a), s, k), k);
        expr new_b;
        {
            cache::mk_scope sc(m_cache);
            new_b = reify(normalize(abst_body(a), extend(s, svalue(k)), k+1), k+1);
        }
        return mk_lambda(abst_name(a), new_t, new_b);
    }

    /** \brief Convert the value \c v back into an expression in a context that contains \c k binders. */
    expr reify(svalue const & v, unsigned k) {
        switch (v.kind()) {
        case svalue_kind::Expr:       return to_expr(v);
        case svalue_kind::BoundedVar: return mk_var(k - to_bvar(v) - 1);
        case svalue_kind::Closure:    return reify_closure(to_expr(v), stack_of(v), k);
        }
        lean_unreachable();
    }

    /** \brief Return true iff the value_stack does affect the context of a metavariable */
    bool is_identity_stack(value_stack const & s, unsigned k) {
        unsigned i = 0;
        for (auto e : s) {
            if (e.kind() != svalue_kind::BoundedVar || k - to_bvar(e) - 1 != i)
                return false;
            ++i;
        }
        return true;
    }

    /**
       \brief Update the metavariable context for \c m based on the
       value_stack \c s and the number of binders \c k.
       \pre is_metavar(m)
    */
    expr updt_metavar(expr const & m, value_stack const & s, unsigned k) {
        lean_assert(is_metavar(m));
        if (is_identity_stack(s, k))
            return m; // nothing to be done
        local_context lctx = metavar_lctx(m);
        unsigned len_s     = length(s);
        unsigned len_ctx   = m_ctx.size();
        lean_assert(k >= len_ctx);
        if (k > len_ctx)
            lctx = add_lift(lctx, len_s, k - len_ctx);
        expr r = update_metavar(m, lctx);
        buffer<expr> subst;
        for (auto e : s) {
            subst.push_back(reify(e, k));
        }
        std::reverse(subst.begin(), subst.end());
        return instantiate(r, subst.size(), subst.data());
    }

    /** \brief Normalize the expression \c a in a context composed of stack \c s and \c k binders. */
    svalue normalize(expr const & a, value_stack const & s, unsigned k) {
        flet<unsigned> l(m_depth, m_depth+1);
        check_interrupted(m_interrupted);
        if (m_depth > m_max_depth)
            throw kernel_exception(m_env, "normalizer maximum recursion depth exceeded");
        bool shared = false;
        if (is_shared(a)) {
            shared = true;
            auto it = m_cache.find(a);
            if (it != m_cache.end())
                return it->second;
        }

        svalue r;
        switch (a.kind()) {
        case expr_kind::MetaVar:
            if (m_subst && m_subst->is_assigned(a)) {
                r = normalize(m_subst->get_subst(a), s, k);
            } else {
                r = svalue(updt_metavar(a, s, k));
            }
            break;
        case expr_kind::Var:
            r = lookup(s, var_idx(a));
            break;
        case expr_kind::Constant: {
            object const & obj = m_env.get_object(const_name(a));
            if (obj.is_definition() && !obj.is_opaque()) {
                r = normalize(obj.get_value(), value_stack(), 0);
            } else {
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
                            r = normalize(m, s, k);
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

    void set_ctx(context const & ctx) {
        if (!is_eqp(ctx, m_ctx)) {
            m_ctx = ctx;
            m_cache.clear();
        }
    }

    void set_subst(substitution const * subst) {
        if (m_subst == subst) {
            // Check whether m_subst has been updated since the last time the normalizer has been invoked
            if (m_subst && m_subst->get_timestamp() > m_subst_timestamp) {
                m_subst_timestamp = m_subst->get_timestamp();
                m_cache.clear();
            }
        } else {
            m_subst = subst;
            m_cache.clear();
            m_subst_timestamp = m_subst ? m_subst->get_timestamp() : 0;
        }
    }

public:
    imp(environment const & env, unsigned max_depth):
        m_env(env) {
        m_interrupted     = false;
        m_max_depth       = max_depth;
        m_depth           = 0;
        m_subst           = nullptr;
        m_subst_timestamp = 0;
    }

    expr operator()(expr const & e, context const & ctx, substitution const * subst) {
        set_ctx(ctx);
        set_subst(subst);
        unsigned k = m_ctx.size();
        return reify(normalize(e, value_stack(), k), k);
    }

    void clear() { m_ctx = context(); m_cache.clear(); m_subst = nullptr; m_subst_timestamp = 0; }
    void set_interrupt(bool flag) { m_interrupted = flag; }
};

normalizer::normalizer(environment const & env, unsigned max_depth):m_ptr(new imp(env, max_depth)) {}
normalizer::normalizer(environment const & env):normalizer(env, std::numeric_limits<unsigned>::max()) {}
normalizer::normalizer(environment const & env, options const & opts):normalizer(env, get_normalizer_max_depth(opts)) {}
normalizer::~normalizer() {}
expr normalizer::operator()(expr const & e, context const & ctx, substitution const * subst) { return (*m_ptr)(e, ctx, subst); }
void normalizer::clear() { m_ptr->clear(); }
void normalizer::set_interrupt(bool flag) { m_ptr->set_interrupt(flag); }

expr normalize(expr const & e, environment const & env, context const & ctx, substitution const * subst) {
    return normalizer(env)(e, ctx, subst);
}
}

/*
  Remark:

  Eta-reduction + Cumulativity + Set theoretic interpretation is unsound.
  Example:
     f : (Type 2) -> (Type 2)
     (fun (x : (Type 1)) (f x)) : (Type 1) -> (Type 2)
     The domains of these two terms are different. So, they must have different denotations.

     However, by eta-reduction, we have:
     (fun (x : (Type 1)) (f x)) == f

     For now, we will disable it.
     REMARK: we can workaround this problem by applying only when the domain of f is equal
     to the domain of the lambda abstraction.

  Cody Roux suggested we use Eta-expanded normal forms.

  Remark: The source code for eta-reduction can be found in the commit 519a290f320c6a
*/
