/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Quotient types for kernels with proof irrelevance.
*/
#include "util/sstream.h"
#include "kernel/kernel_exception.h"
#include "kernel/environment.h"
#include "kernel/quotient/quotient.h"

namespace lean {
static name * g_quotient_extension = nullptr;
static name * g_propext        = nullptr;
static name * g_quotient       = nullptr;
static name * g_quotient_lift  = nullptr;
static name * g_quotient_ind   = nullptr;
static name * g_quotient_mk    = nullptr;
static name * g_quotient_sound = nullptr;

struct quotient_env_ext : public environment_extension {
    bool m_initialized;
    quotient_env_ext():m_initialized(false){}
};

/** \brief Auxiliary object for registering the environment extension */
struct quotient_env_ext_reg {
    unsigned m_ext_id;
    quotient_env_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<quotient_env_ext>()); }
};

static quotient_env_ext_reg * g_ext = nullptr;

/** \brief Retrieve environment extension */
static quotient_env_ext const & get_extension(environment const & env) {
    return static_cast<quotient_env_ext const &>(env.get_extension(g_ext->m_ext_id));
}

/** \brief Update environment extension */
static environment update(environment const & env, quotient_env_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<quotient_env_ext>(ext));
}

environment declare_quotient(environment const & env) {
    quotient_env_ext ext = get_extension(env);
    ext.m_initialized = true;
    return update(env, ext);
}

optional<pair<expr, constraint_seq>> quotient_normalizer_extension::operator()(expr const & e, extension_context & ctx) const {
    environment const & env = ctx.env();
    expr const & fn         = get_app_fn(e);
    if (!is_constant(fn))
        return none_ecs();
    quotient_env_ext const & ext = get_extension(env);
    if (!ext.m_initialized)
        return none_ecs();
    unsigned mk_pos;
    unsigned arg_pos;
    if (const_name(fn) == *g_quotient_lift) {
        mk_pos  = 5;
        arg_pos = 3;
    } else if (const_name(fn) == *g_quotient_ind) {
        mk_pos  = 4;
        arg_pos = 3;
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
    if (const_name(mk_fn) != *g_quotient_mk)
        return none_ecs();

    expr const & f = args[arg_pos];
    expr r = mk_app(f, app_arg(mk));
    unsigned elim_arity = mk_pos+1;
    if (args.size() > elim_arity)
        r = mk_app(r, args.size() - elim_arity, args.begin() + elim_arity);
    return some_ecs(r, mk_cs.second);
}

template<typename Ctx>
optional<expr> is_quot_meta_app_core(Ctx & ctx, expr const & e) {
    expr const & fn         = get_app_fn(e);
    if (!is_constant(fn))
        return none_expr();
    unsigned mk_pos;
    if (const_name(fn) == *g_quotient_lift) {
        mk_pos = 5;
    } else if (const_name(fn) == *g_quotient_ind) {
        mk_pos = 4;
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

optional<expr> quotient_normalizer_extension::is_stuck(expr const & e, extension_context & ctx) const {
    return is_quot_meta_app_core(ctx, e);
}

bool quotient_normalizer_extension::supports(name const & feature) const {
    return feature == *g_quotient_extension;
}

bool quotient_normalizer_extension::is_recursor(environment const &, name const & n) const {
    return n == *g_quotient_lift || n == *g_quotient_ind;
}

bool quotient_normalizer_extension::is_builtin(environment const & env, name const & n) const {
    return is_quotient_decl(env, n);
}

bool is_quotient_decl(environment const & env, name const & n) {
    if (!get_extension(env).m_initialized)
        return false;
    return
        n == *g_quotient || n == *g_quotient_lift || n == *g_quotient_ind || n == *g_quotient_mk;
}

void initialize_quotient_module() {
    g_quotient_extension = new name("quotient_extension");
    g_propext            = new name{"propext"};
    g_quotient           = new name{"quot"};
    g_quotient_lift      = new name{"quot", "lift"};
    g_quotient_ind       = new name{"quot", "ind"};
    g_quotient_mk        = new name{"quot", "mk"};
    g_quotient_sound     = new name{"quot", "sound"};
    g_ext                = new quotient_env_ext_reg();
}

void finalize_quotient_module() {
    delete g_ext;
    delete g_propext;
    delete g_quotient_extension;
    delete g_quotient;
    delete g_quotient_lift;
    delete g_quotient_ind;
    delete g_quotient_mk;
    delete g_quotient_sound;
}
}
