/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/hash.h"
#include "util/interrupt.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "library/abstract_expr.h"
#include "library/cache_helper.h"
#include "library/fun_info.h"

namespace lean {
struct abstract_expr_cache {
    environment        m_env;
    expr_map<unsigned> m_hash_cache;
    expr_map<unsigned> m_weight_cache;
    abstract_expr_cache(environment const & env):m_env(env) {}
    environment const & env() const { return m_env; }
};

/* The abstract_expr_cache does not depend on the transparency mode */
typedef transparencyless_cache_compatibility_helper<abstract_expr_cache>
abstract_expr_cache_helper;

MK_THREAD_LOCAL_GET_DEF(abstract_expr_cache_helper, get_aech);

abstract_expr_cache & get_abstract_cache_for(type_context const & ctx) {
    return get_aech().get_cache_for(ctx);
}

#define EASY_HASH(e) {                                  \
    switch (e.kind()) {                                 \
    case expr_kind::Constant: case expr_kind::Local:    \
    case expr_kind::Meta:     case expr_kind::Sort:     \
    case expr_kind::Var:                                \
        return e.hash();                                \
    default:                                            \
        break;                                          \
    }                                                   \
}

struct abstract_fn {
    type_context &                   m_ctx;
    buffer<expr>                     m_locals;
    type_context::transparency_scope m_scope;

    static void check_system() { ::lean::check_system("abstract expression operator"); }

    abstract_fn(type_context & ctx):
        m_ctx(ctx),
        m_scope(m_ctx, transparency_mode::All) {}

    expr instantiate_locals(expr const & e) {
        return instantiate_rev(e, m_locals.size(), m_locals.data());
    }

    expr push_local(name const & pp_name, expr const & type) {
        expr l = m_ctx.push_local(pp_name, instantiate_locals(type));
        m_locals.push_back(l);
        return l;
    }

    expr push_let(name const & pp_name, expr const & type, expr const & value) {
        expr l = m_ctx.push_let(pp_name, instantiate_locals(type), instantiate_locals(value));
        m_locals.push_back(l);
        return l;
    }

    void pop() {
        m_locals.pop_back();
    }
};

struct abstract_hash_fn : public abstract_fn {
    expr_map<unsigned> & m_cache;
    abstract_hash_fn(type_context & ctx):
        abstract_fn(ctx),
        m_cache(get_abstract_cache_for(ctx).m_hash_cache) {
    }

    unsigned hash(expr const & e) {
        EASY_HASH(e);

        auto it = m_cache.find(e);
        if (it != m_cache.end())
            return it->second;

        check_system();

        unsigned r = 0;

        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Local:
        case expr_kind::Meta:     case expr_kind::Sort:
        case expr_kind::Var:
            lean_unreachable();
        case expr_kind::Lambda:
        case expr_kind::Pi:
            r = hash(binding_domain(e));
            push_local(binding_name(e), binding_domain(e));
            r = ::lean::hash(r, hash(binding_body(e)));
            pop();
            break;
        case expr_kind::Let:
            r = ::lean::hash(hash(let_type(e)), hash(let_value(e)));
            push_let(let_name(e), let_type(e), let_value(e));
            r = ::lean::hash(r, hash(let_body(e)));
            pop();
            break;
        case expr_kind::Macro:
            r = lean::hash(macro_num_args(e), [&](unsigned i) { return hash(macro_arg(e, i)); },
                           macro_def(e).hash());
            break;
        case expr_kind::App:
            buffer<expr> args;
            expr const & f = get_app_args(e, args);
            r = hash(f);
            fun_info info  = get_fun_info(m_ctx, instantiate_locals(f), args.size());
            unsigned i = 0;
            for (param_info const & pinfo : info.get_params_info()) {
                lean_assert(i < args.size());
                if (!pinfo.is_inst_implicit() && !pinfo.is_prop()) {
                    r = ::lean::hash(r, hash(args[i]));
                }
                i++;
            }
            /* Remark: the property (i == args.size()) does not necessarily hold here.
               This can happen whenever the arity of f depends on its arguments. */
            break;
        }
        m_cache.insert(mk_pair(e, r));
        return r;
    }

    unsigned operator()(expr const & e) {
        return hash(e);
    }
};

unsigned abstract_hash(type_context & ctx, expr const & e) {
    EASY_HASH(e);
    return abstract_hash_fn(ctx)(e);
}

#define EASY_WEIGHT(e) {                                \
    switch (e.kind()) {                                 \
    case expr_kind::Constant: case expr_kind::Local:    \
    case expr_kind::Meta:     case expr_kind::Sort:     \
    case expr_kind::Var:                                \
        return 1;                                       \
    default:                                            \
        break;                                          \
    }                                                   \
}

/* TODO(Leo): this class is too similar to abstract_hash_fn, both are folding expr.
   We should try to merge both implementations. */
struct abstract_weight_fn : public abstract_fn {
    expr_map<unsigned> & m_cache;
    abstract_weight_fn(type_context & ctx):
        abstract_fn(ctx),
        m_cache(get_abstract_cache_for(ctx).m_weight_cache) {}

    unsigned weight(expr const & e) {
        EASY_WEIGHT(e);

        auto it = m_cache.find(e);
        if (it != m_cache.end())
            return it->second;

        check_system();

        unsigned r = 0;

        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Local:
        case expr_kind::Meta:     case expr_kind::Sort:
        case expr_kind::Var:
            lean_unreachable();
        case expr_kind::Lambda:
        case expr_kind::Pi:
            r  = weight(binding_domain(e));
            push_local(binding_name(e), binding_domain(e));
            r += weight(binding_body(e));
            pop();
            break;
        case expr_kind::Let:
            r  = weight(let_type(e));
            r += weight(let_value(e));
            push_let(let_name(e), let_type(e), let_value(e));
            r += weight(let_body(e));
            pop();
            break;
        case expr_kind::Macro:
            r = 0;
            for (unsigned i = 0; i < macro_num_args(e); i++)
                r += weight(macro_arg(e, i));
            break;
        case expr_kind::App:
            buffer<expr> args;
            expr const & f = get_app_args(e, args);
            r = weight(f);
            fun_info info  = get_fun_info(m_ctx, instantiate_locals(f), args.size());
            unsigned i = 0;
            for (param_info const & pinfo : info.get_params_info()) {
                lean_assert(i < args.size());
                if (!pinfo.is_inst_implicit() && !pinfo.is_prop()) {
                    r += weight(args[i]);
                }
                i++;
            }
            /* Remark: the property (i == args.size()) does not necessarily hold here.
               This can happen whenever the arity of f depends on its arguments. */
            break;
        }
        m_cache.insert(mk_pair(e, r));
        return r;
    }

    unsigned operator()(expr const & e) {
        return weight(e);
    }
};

unsigned abstract_weight(type_context & ctx, expr const & e) {
    EASY_WEIGHT(e);
    return abstract_weight_fn(ctx)(e);
}

struct abstract_eq_fn : public abstract_fn {
    abstract_eq_fn(type_context & ctx):
        abstract_fn(ctx) {}

    bool equal(expr const & a, expr const & b) {
        if (is_eqp(a, b))
            return true;
        if (abstract_hash(m_ctx, a) != abstract_hash(m_ctx, b))
            return false;
        if (a.kind() != b.kind())
            return false;

        switch (a.kind()) {
        case expr_kind::Var:
        case expr_kind::Constant:
        case expr_kind::Meta:
        case expr_kind::Sort:
        case expr_kind::Local:
            return a == b;
        case expr_kind::Lambda:
        case expr_kind::Pi:
            check_system();
            if (!equal(binding_domain(a), binding_domain(b)))
                return false;
            push_local(binding_name(a), binding_domain(a));
            if (!equal(binding_body(a), binding_body(b)))
                return false;
            pop();
            return true;
        case expr_kind::Let:
            check_system();
            if (!equal(let_type(a), let_type(b)) ||
                !equal(let_value(a), let_value(b)))
                return false;
            push_let(let_name(a), let_type(a), let_value(a));
            if (!equal(let_body(a), let_body(b)))
                return false;
            pop();
            return true;
        case expr_kind::Macro:
            if (macro_def(a) != macro_def(b) || macro_num_args(a) != macro_num_args(b))
                return false;
            check_system();
            for (unsigned i = 0; i < macro_num_args(a); i++) {
                if (!equal(macro_arg(a, i), macro_arg(b, i)))
                    return false;
            }
            return true;
        case expr_kind::App:
            check_system();
            buffer<expr> a_args;
            buffer<expr> b_args;
            expr const & a_fn = get_app_args(a, a_args);
            expr const & b_fn = get_app_args(b, b_args);
            if (a_args.size() != b_args.size() ||
                !equal(a_fn, b_fn))
                return false;
            fun_info info  = get_fun_info(m_ctx, instantiate_locals(a_fn), a_args.size());
            unsigned i = 0;
            for (param_info const & pinfo : info.get_params_info()) {
                lean_assert(i < a_args.size());
                lean_assert(i < b_args.size());
                if (!pinfo.is_inst_implicit() && !pinfo.is_prop() && !equal(a_args[i], b_args[i]))
                    return false;
                i++;
            }
            /* Remark: the property (i == a_args.size()) does not necessarily hold here.
               This can happen whenever the arity of f depends on its arguments. */
            return true;
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

    bool operator()(expr const & a, expr const & b) {
        return equal(a, b);
    }
};

bool abstract_eq(type_context & ctx, expr const & a, expr const & b) {
    if (is_eqp(a, b))
        return true;
    return abstract_eq_fn(ctx)(a, b);
}
}
