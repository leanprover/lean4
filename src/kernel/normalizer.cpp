/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <limits>
#include <unordered_map>
#include "util/list.h"
#include "util/flet.h"
#include "util/freset.h"
#include "util/buffer.h"
#include "util/interrupt.h"
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

typedef list<expr> value_stack;
value_stack extend(value_stack const & s, expr const & v) {
    lean_assert(!is_lambda(v) && !is_pi(v) && !is_metavar(v) && !is_let(v));
    return cons(v, s);
}

/**
   \brief Internal value used to store closures.
   This is a transient value that is only used during normalization.
*/
class closure : public value {
    expr         m_expr;
    context      m_ctx;
    value_stack  m_stack;
public:
    closure(expr const & e, context const & ctx, value_stack const & s):m_expr(e), m_ctx(ctx), m_stack(s) {}
    virtual ~closure() {}
    virtual expr get_type() const { lean_unreachable(); } // LCOV_EXCL_LINE
    virtual name get_name() const { return name("Closure"); }
    virtual void display(std::ostream & out) const {
        out << "(Closure " << m_expr << " [";
        bool first = true;
        for (auto v : m_stack) {
            if (first) first = false; else out << " ";
            out << v;
        }
        out << "])";
    }
    expr const & get_expr() const { return m_expr; }
    context const & get_context() const { return m_ctx; }
    value_stack const & get_stack() const { return m_stack; }
};

expr mk_closure(expr const & e, context const & ctx, value_stack const & s) { return mk_value(*(new closure(e, ctx, s))); }
bool is_closure(expr const & e) { return is_value(e) && dynamic_cast<closure const *>(&to_value(e)) != nullptr; }
closure const & to_closure(expr const & e) { lean_assert(is_closure(e));   return static_cast<closure const &>(to_value(e)); }

/** \brief Expression normalizer. */
class normalizer::imp {
    typedef std::unordered_map<expr, expr, expr_hash_alloc, expr_eqp> cache;

    ro_environment::weak_ref m_env;
    context                  m_ctx;
    cached_metavar_env       m_menv;
    cache                    m_cache;
    unsigned                 m_max_depth;
    unsigned                 m_depth;

    ro_environment env() const { return ro_environment(m_env); }

    expr instantiate(expr const & e, unsigned n, expr const * s) {
        return ::lean::instantiate(e, n, s, m_menv.to_some_menv());
    }

    expr add_lift(expr const & m, unsigned s, unsigned n) {
        return ::lean::add_lift(m, s, n, m_menv.to_some_menv());
    }

    expr lookup(value_stack const & s, unsigned i) {
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
            // Save the current context and cache
            freset<cache>    reset(m_cache);
            flet<context>    set(m_ctx, entry_c);
            unsigned k = m_ctx.size();
            return normalize(*(entry.get_body()), value_stack(), k);
        } else {
            return mk_var(entry_c.size());
        }
    }

    /** \brief Convert the value \c v back into an expression in a context that contains \c k binders. */
    expr reify(expr const & v, unsigned k) {
        return replace(v, [&](expr const & e, unsigned DEBUG_CODE(offset)) -> expr {
                lean_assert(offset == 0);
                lean_assert(!is_lambda(e) && !is_pi(e) && !is_metavar(e) && !is_let(e));
                if (is_var(e)) {
                    // de Bruijn level --> de Bruijn index
                    return mk_var(k - var_idx(e) - 1);
                } else if (is_closure(e)) {
                    return reify_closure(to_closure(e), k);
                } else {
                    return e;
                }
            });
    }

    /** \brief Return true iff the value_stack does affect the context of a metavariable */
    bool is_identity_stack(value_stack const & s, unsigned k) {
        unsigned i = 0;
        for (auto e : s) {
            if (!is_var(e) || k - var_idx(e) - 1 != i)
                return false;
            ++i;
        }
        return true;
    }

    /** \brief Convert the closure \c c into an expression in a context that contains \c k binders. */
    expr reify_closure(closure const & c, unsigned k) {
        expr const & e        = c.get_expr();
        context const & ctx   = c.get_context();
        value_stack const & s = c.get_stack();
        freset<cache>    reset(m_cache);
        flet<context>    set(m_ctx, ctx);
        if (is_abstraction(e)) {
            return update_abst(e, [&](expr const & d, expr const & b) {
                    expr new_d = reify(normalize(d, s, k), k);
                    m_cache.clear(); // make sure we do not reuse cached values from the previous call
                    expr new_b = reify(normalize(b, extend(s, mk_var(k)), k+1), k+1);
                    return mk_pair(new_d, new_b);
                });
        } else {
            lean_assert(is_metavar(e));
            if (is_identity_stack(s, k))
                return e; // nothing to be done
            local_context lctx = metavar_lctx(e);
            unsigned len_s     = length(s);
            unsigned len_ctx   = ctx.size();
            lean_assert(k >= len_ctx);
            expr r;
            if (k > len_ctx)
                r = add_lift(e, len_s, k - len_ctx);
            else
                r = e;
            buffer<expr> subst;
            for (auto v : s)
                subst.push_back(reify(v, k));
            std::reverse(subst.begin(), subst.end());
            return instantiate(r, subst.size(), subst.data());
        }
    }

    /** \brief Normalize the expression \c a in a context composed of stack \c s and \c k binders. */
    expr normalize(expr const & a, value_stack const & s, unsigned k) {
        flet<unsigned> l(m_depth, m_depth+1);
        check_system("normalizer");
        if (m_depth > m_max_depth)
            throw kernel_exception(env(), "normalizer maximum recursion depth exceeded");
        bool shared = false;
        if (is_shared(a)) {
            shared = true;
            auto it = m_cache.find(a);
            if (it != m_cache.end())
                return it->second;
        }

        expr r;
        switch (a.kind()) {
        case expr_kind::MetaVar: case expr_kind::Pi: case expr_kind::Lambda:
            r = mk_closure(a, m_ctx, s);
            break;
        case expr_kind::Var:
            r = lookup(s, var_idx(a));
            break;
        case expr_kind::Constant: {
            object const & obj = env()->get_object(const_name(a));
            if (obj.is_definition() && !obj.is_opaque()) {
                freset<cache> reset(m_cache);
                r = normalize(obj.get_value(), value_stack(), 0);
            } else {
                r = a;
            }
            break;
        }
        case expr_kind::Type: case expr_kind::Value:
            r = a;
            break;
        case expr_kind::App: {
            expr f      = normalize(arg(a, 0), s, k);
            unsigned i  = 1;
            unsigned n  = num_args(a);
            while (true) {
                if (is_closure(f) && is_lambda(to_closure(f).get_expr())) {
                    // beta reduction
                    expr fv = to_closure(f).get_expr();
                    value_stack new_s = to_closure(f).get_stack();
                    while (is_lambda(fv) && i < n) {
                        new_s = extend(new_s, normalize(arg(a, i), s, k));
                        i++;
                        fv = abst_body(fv);
                    }
                    {
                        freset<cache> reset(m_cache);
                        flet<context> set(m_ctx, to_closure(f).get_context());
                        f = normalize(fv, new_s, k);
                    }
                    if (i == n) {
                        r = f;
                        break;
                    }
                } else {
                    buffer<expr> new_args;
                    new_args.push_back(f);
                    for (; i < n; i++)
                        new_args.push_back(normalize(arg(a, i), s, k));
                    if (is_value(f) && !is_closure(f)) {
                        buffer<expr> reified_args;
                        for (auto arg : new_args) reified_args.push_back(reify(arg, k));
                        optional<expr> m = to_value(f).normalize(reified_args.size(), reified_args.data());
                        if (m) {
                            r = normalize(*m, s, k);
                            break;
                        }
                    }
                    r = mk_app(new_args);
                    break;
                }
            }
            break;
        }
        case expr_kind::Eq: {
            expr new_lhs = normalize(eq_lhs(a), s, k);
            expr new_rhs = normalize(eq_rhs(a), s, k);
            if (is_value(new_lhs) && is_value(new_rhs) && !is_closure(new_lhs) && !is_closure(new_rhs)) {
                r = mk_bool_value(new_lhs == new_rhs);
            } else {
                r = mk_eq(new_lhs, new_rhs);
            }
            break;
        }
        case expr_kind::Let: {
            expr v = normalize(let_value(a), s, k);
            {
                freset<cache> reset(m_cache);
                r = normalize(let_body(a), extend(s, v), k);
            }
            break;
        }}
        if (shared) {
            m_cache[a] = r;
        }
        return r;
    }

    void set_ctx(context const & ctx) {
        if (!is_eqp(ctx, m_ctx)) {
            m_ctx = ctx;
            m_cache.clear();
        }
    }

public:
    imp(ro_environment const & env, unsigned max_depth):
        m_env(env) {
        m_max_depth      = max_depth;
        m_depth          = 0;
    }

    expr operator()(expr const & e, context const & ctx, optional<metavar_env> const & menv) {
        set_ctx(ctx);
        if (m_menv.update(menv))
            m_cache.clear();
        unsigned k = m_ctx.size();
        return reify(normalize(e, value_stack(), k), k);
    }

    void clear() { m_ctx = context(); m_cache.clear(); m_menv.clear(); }
};

normalizer::normalizer(ro_environment const & env, unsigned max_depth):m_ptr(new imp(env, max_depth)) {}
normalizer::normalizer(ro_environment const & env):normalizer(env, std::numeric_limits<unsigned>::max()) {}
normalizer::normalizer(ro_environment const & env, options const & opts):normalizer(env, get_normalizer_max_depth(opts)) {}
normalizer::~normalizer() {}
expr normalizer::operator()(expr const & e, context const & ctx, optional<metavar_env> const & menv) { return (*m_ptr)(e, ctx, menv); }
expr normalizer::operator()(expr const & e, context const & ctx, metavar_env const & menv) { return operator()(e, ctx, some_menv(menv)); }
expr normalizer::operator()(expr const & e, context const & ctx) { return operator()(e, ctx, none_menv()); }
void normalizer::clear() { m_ptr->clear(); }

expr normalize(expr const & e, ro_environment const & env, context const & ctx) {
    return normalizer(env)(e, ctx);
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
