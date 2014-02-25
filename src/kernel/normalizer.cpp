/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <limits>
#include "util/list.h"
#include "util/flet.h"
#include "util/freset.h"
#include "util/buffer.h"
#include "util/interrupt.h"
#include "util/sexpr/options.h"
#include "kernel/normalizer.h"
#include "kernel/environment.h"
#include "kernel/expr_maps.h"
#include "kernel/free_vars.h"
#include "kernel/instantiate.h"
#include "kernel/replace_fn.h"
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
class closure : public macro {
    expr         m_expr;
    value_stack  m_stack;
public:
    closure(expr const & e, value_stack const & s):m_expr(e), m_stack(s) {}
    virtual ~closure() {}
    virtual expr get_type(buffer<expr> const & ) const { lean_unreachable(); } // LCOV_EXCL_LINE
    virtual void write(serializer & ) const { lean_unreachable(); } // LCOV_EXCL_LINE
    virtual expr expand1(buffer<expr> const & ) const { lean_unreachable(); }
    virtual expr expand(buffer<expr> const & ) const { lean_unreachable(); }
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
    value_stack const & get_stack() const { return m_stack; }
    virtual bool is_atomic_pp(bool /* unicode */, bool /* coercion */) const { return false; } // NOLINT
};

expr mk_closure(expr const & e, value_stack const & s) { return mk_macro(new closure(e, s)); }
bool is_closure(expr const & e) { return is_macro(e) && dynamic_cast<closure const *>(&to_macro(e)) != nullptr; }
closure const & to_closure(expr const & e) { lean_assert(is_closure(e)); return static_cast<closure const &>(to_macro(e)); }

/** \brief Expression normalizer. */
class normalizer::imp {
    typedef expr_map<expr> cache;

    ro_environment::weak_ref m_env;
    cache                    m_cache;
    unsigned                 m_max_depth;
    unsigned                 m_depth;

    ro_environment env() const { return ro_environment(m_env); }

    expr lookup(value_stack const & s, unsigned i) {
        unsigned j = i;
        value_stack const * it1 = &s;
        while (*it1) {
            if (j == 0)
                return head(*it1);
            --j;
            it1 = &tail(*it1);
        }
        throw kernel_exception(env(), "normalizer failure, unexpected occurrence of free variable");
    }

    /** \brief Convert the value \c v back into an expression in a context that contains \c k binders. */
    expr reify(expr const & v, unsigned k) {
        return replace(v, [&](expr const & e, unsigned DEBUG_CODE(offset)) -> expr {
                lean_assert(offset == 0);
                lean_assert(!is_lambda(e) && !is_pi(e) && !is_sigma(e) && !is_let(e));
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

    /** \brief Convert the closure \c c into an expression in a context that contains \c k binders. */
    expr reify_closure(closure const & c, unsigned k) {
        expr const & e        = c.get_expr();
        value_stack const & s = c.get_stack();
        lean_assert(is_binder(e));
        freset<cache>    reset(m_cache);
        expr new_d = reify(normalize(binder_domain(e), s, k), k);
        m_cache.clear(); // make sure we do not reuse cached values from the previous call
        expr new_b = reify(normalize(binder_body(e), extend(s, mk_var(k)), k+1), k+1);
        return update_binder(e, new_d, new_b);
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
        case expr_kind::Sigma: case expr_kind::Pi: case expr_kind::Lambda:
            r = mk_closure(a, s);
            break;
        case expr_kind::Var:
            r = lookup(s, var_idx(a));
            break;
        case expr_kind::Constant: {
            optional<object> obj = env()->find_object(const_name(a));
            if (should_unfold(obj)) {
                // TODO(Leo): instantiate level parameters
                freset<cache> reset(m_cache);
                r = normalize(obj->get_value(), value_stack(), 0);
            } else {
                r = a;
            }
            break;
        }
        case expr_kind::Pair: {
            expr new_first  = normalize(pair_first(a), s, k);
            expr new_second = normalize(pair_second(a), s, k);
            expr new_type   = normalize(pair_type(a), s, k);
            r = update_pair(a, new_first, new_second, new_type);
            break;
        }
        case expr_kind::Fst: case expr_kind::Snd: {
            expr new_arg = normalize(proj_arg(a), s, k);
            if (is_dep_pair(new_arg)) {
                if (is_fst(a))
                    r = pair_first(new_arg);
                else
                    r = pair_second(new_arg);
            } else {
                r = update_proj(a, new_arg);
            }
            break;
        }
        case expr_kind::Sort: case expr_kind::Macro: case expr_kind::Local: case expr_kind::Meta:
            r = a;
            break;
        case expr_kind::App: {
            buffer<expr> new_args;
            expr const * it = &a;
            while (is_app(*it)) {
                new_args.push_back(normalize(app_arg(*it), s, k));
                it = &app_fn(*it);
            }
            expr f = normalize(*it, s, k);
            unsigned i  = 0;
            unsigned n  = new_args.size();
            while (true) {
                if (is_closure(f) && is_lambda(to_closure(f).get_expr())) {
                    // beta reduction
                    expr fv = to_closure(f).get_expr();
                    value_stack new_s = to_closure(f).get_stack();
                    while (is_lambda(fv) && i < n) {
                        new_s = extend(new_s, new_args[n - i - 1]);
                        i++;
                        fv = binder_body(fv);
                    }
                    {
                        freset<cache> reset(m_cache);
                        f = normalize(fv, new_s, k);
                    }
                    if (i == n) {
                        r = f;
                        break;
                    }
                } else {
                    if (is_macro(f) && !is_closure(f)) {
                        buffer<expr> reified_args;
                        unsigned i = new_args.size();
                        while (i > 0) {
                            --i;
                            reified_args.push_back(reify(new_args[i], k));
                        }
                        r = to_macro(f).expand(reified_args);
                    } else {
                        new_args.push_back(f);
                        std::reverse(new_args.begin(), new_args.end());
                        r = mk_app(new_args);
                    }
                    break;
                }
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


public:
    imp(ro_environment const & env, unsigned max_depth):
        m_env(env) {
        m_max_depth      = max_depth;
        m_depth          = 0;
    }

    expr operator()(expr const & e) {
        unsigned k = 0;
        return reify(normalize(e, value_stack(), k), k);
    }

    void clear() { m_cache.clear(); }
};

normalizer::normalizer(ro_environment const & env, unsigned max_depth):m_ptr(new imp(env, max_depth)) {}
normalizer::normalizer(ro_environment const & env):normalizer(env, std::numeric_limits<unsigned>::max()) {}
normalizer::normalizer(ro_environment const & env, options const & opts):normalizer(env, get_normalizer_max_depth(opts)) {}
normalizer::~normalizer() {}
expr normalizer::operator()(expr const & e) { return (*m_ptr)(e); }
void normalizer::clear() { m_ptr->clear(); }
expr normalize(expr const & e, ro_environment const & env) { return normalizer(env)(e); }
}
