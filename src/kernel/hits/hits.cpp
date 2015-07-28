/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Builtin HITs:
    - n-truncation
    - type quotients (non-truncated quotients)
*/
#include "util/sstream.h"
#include "kernel/kernel_exception.h"
#include "kernel/environment.h"
#include "kernel/hits/hits.h"

namespace lean {
static name * g_hits_extension             = nullptr;
static name * g_trunc                      = nullptr;
static name * g_trunc_tr                   = nullptr;
static name * g_trunc_rec                  = nullptr;
static name * g_trunc_is_trunc_trunc       = nullptr;
static name * g_hit_quotient               = nullptr;
static name * g_hit_quotient_class_of      = nullptr;
static name * g_hit_quotient_rec           = nullptr;
static name * g_hit_quotient_eq_of_rel     = nullptr;
static name * g_hit_quotient_rec_eq_of_rel = nullptr;

struct hits_env_ext : public environment_extension {
    bool m_initialized;
    hits_env_ext():m_initialized(false){}
};

/** \brief Auxiliary object for registering the environment extension */
struct hits_env_ext_reg {
    unsigned m_ext_id;
    hits_env_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<hits_env_ext>()); }
};

static hits_env_ext_reg * g_ext = nullptr;

/** \brief Retrieve environment extension */
static hits_env_ext const & get_extension(environment const & env) {
    return static_cast<hits_env_ext const &>(env.get_extension(g_ext->m_ext_id));
}

/** \brief Update environment extension */
static environment update(environment const & env, hits_env_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<hits_env_ext>(ext));
}

environment declare_hits(environment const & env) {
    hits_env_ext ext = get_extension(env);
    ext.m_initialized = true;
    return update(env, ext);
}

optional<pair<expr, constraint_seq>> hits_normalizer_extension::operator()(expr const & e, extension_context & ctx) const {
    environment const & env = ctx.env();
    expr const & fn         = get_app_fn(e);
    if (!is_constant(fn))
        return none_ecs();
    hits_env_ext const & ext = get_extension(env);
    if (!ext.m_initialized)
        return none_ecs();
    unsigned mk_pos;
    name * mk_name;
    unsigned f_pos;
    if (const_name(fn) == *g_trunc_rec) {
        mk_pos  = 5;
        mk_name = g_trunc_tr;
        f_pos   = 4;
    } else if (const_name(fn) == *g_hit_quotient_rec) {
        mk_pos  = 5;
        mk_name = g_hit_quotient_class_of;
        f_pos   = 3;
    } else {
        return none_ecs();
    }

    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() <= mk_pos)
        return none_ecs();

    auto mk_cs = ctx.whnf(args[mk_pos]);
    expr const & mk = mk_cs.first;
    expr const & mk_fn = get_app_fn(mk);
    if (!is_constant(mk_fn))
        return none_ecs();
    if (const_name(mk_fn) != *mk_name)
        return none_ecs();

    expr const & f = args[f_pos];
    expr r = mk_app(f, app_arg(mk));
    unsigned elim_arity = mk_pos+1;
    if (args.size() > elim_arity)
        r = mk_app(r, args.size() - elim_arity, args.begin() + elim_arity);
    return some_ecs(r, mk_cs.second);
}

template<typename Ctx>
optional<expr> is_hits_meta_app_core(Ctx & ctx, expr const & e) {
    expr const & fn         = get_app_fn(e);
    if (!is_constant(fn))
        return none_expr();
    unsigned mk_pos;
    if (const_name(fn) == *g_trunc_rec) {
        mk_pos = 5;
    } else if (const_name(fn) == *g_hit_quotient_rec) {
        mk_pos = 5;
    } else {
        return none_expr();
    }

    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() <= mk_pos)
        return none_expr();

    expr mk_app = ctx.whnf(args[mk_pos]).first;
    return ctx.is_stuck(mk_app);
}

optional<expr> hits_normalizer_extension::is_stuck(expr const & e, extension_context & ctx) const {
    return is_hits_meta_app_core(ctx, e);
}

bool hits_normalizer_extension::supports(name const & feature) const {
    return feature == *g_hits_extension;
}

bool hits_normalizer_extension::is_recursor(environment const &, name const & n) const {
    return n == *g_trunc_rec || n == *g_hit_quotient_rec;
}

bool hits_normalizer_extension::is_builtin(environment const & env, name const & n) const {
    return is_hits_decl(env, n);
}

bool is_hits_decl(environment const & env, name const & n) {
    if (!get_extension(env).m_initialized)
        return false;
    return
        n == *g_trunc || n == *g_trunc_tr || n == *g_trunc_rec ||
        n == *g_hit_quotient || n == *g_hit_quotient_class_of ||
        n == *g_hit_quotient_rec;
}

void initialize_hits_module() {
    g_hits_extension             = new name("hits_extension");
    g_trunc                      = new name{"trunc"};
    g_trunc_tr                   = new name{"trunc", "tr"};
    g_trunc_rec                  = new name{"trunc", "rec"};
    g_trunc_is_trunc_trunc       = new name{"trunc", "is_trunc_trunc"};
    g_hit_quotient               = new name{"quotient"};
    g_hit_quotient_class_of      = new name{"quotient", "class_of"};
    g_hit_quotient_rec           = new name{"quotient", "rec"};
    g_hit_quotient_eq_of_rel     = new name{"quotient", "eq_of_rel"};
    g_hit_quotient_rec_eq_of_rel = new name{"quotient", "rec_eq_of_rel"};
    g_ext                        = new hits_env_ext_reg();
}

void finalize_hits_module() {
    delete g_ext;
    delete g_hits_extension;
    delete g_trunc;
    delete g_trunc_tr;
    delete g_trunc_rec;
    delete g_trunc_is_trunc_trunc;
    delete g_hit_quotient;
    delete g_hit_quotient_class_of;
    delete g_hit_quotient_rec;
    delete g_hit_quotient_eq_of_rel;
    delete g_hit_quotient_rec_eq_of_rel;
}
}
