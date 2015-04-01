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

// Hash code used to identify expected declarations
#define QUOT_MK_HASH    1806675635
#define QUOT_SOUND_HASH 392276735
#define QUOT_EXACT_HASH 843388255
#define QUOT_LIFT_HASH  3998074667
#define QUOT_IND_HASH   2559759863

namespace lean {
static name * g_quotient_extension = nullptr;
static name * g_quotient       = nullptr;
static name * g_quotient_lift  = nullptr;
static name * g_quotient_ind   = nullptr;
static name * g_quotient_mk    = nullptr;
static name * g_quotient_sound = nullptr;
static name * g_quotient_exact = nullptr;

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

static void check_type_hash(environment const & env, name const & d, unsigned hash) {
    auto decl = env.find(d);
    if (!decl)
        throw kernel_exception(env, sstream() << "failed to initialize quotient type, declaration '" << d << "' is missing");
    if (decl->get_type().hash() != hash)
        throw kernel_exception(env, sstream() << "invalid quotient builtin declaration '" << d << "', hash code does not match"
                               << ", expected: " << hash << ", got: " << decl->get_type().hash());
}

environment declare_quotient(environment const & env) {
    check_type_hash(env, name{"quot", "mk"},    QUOT_MK_HASH);
    check_type_hash(env, name{"quot", "sound"}, QUOT_SOUND_HASH);
    check_type_hash(env, name{"quot", "exact"}, QUOT_EXACT_HASH);
    check_type_hash(env, name{"quot", "lift"},  QUOT_LIFT_HASH);
    check_type_hash(env, name{"quot", "ind"},   QUOT_IND_HASH);
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
    if (const_name(fn) == *g_quotient_lift) {
        mk_pos = 5;
    } else if (const_name(fn) == *g_quotient_ind) {
        mk_pos = 4;
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

    expr const & f = args[mk_pos-2];
    expr r = mk_app(f, app_arg(mk));
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
    return has_expr_metavar_strict(mk_app);
}

optional<expr> quotient_normalizer_extension::may_reduce_later(expr const & e, extension_context & ctx) const {
    return is_quot_meta_app_core(ctx, e);
}

bool quotient_normalizer_extension::supports(name const & feature) const {
    return feature == *g_quotient_extension;
}

bool is_quotient_decl(environment const & env, name const & n) {
    if (!get_extension(env).m_initialized)
        return false;
    return
        n == *g_quotient || n == *g_quotient_lift || n == *g_quotient_ind || n == *g_quotient_mk ||
        n == *g_quotient_sound || n == *g_quotient_exact;
}

void initialize_quotient_module() {
    g_quotient_extension = new name("quotient_extension");
    g_quotient           = new name{"quot"};
    g_quotient_lift      = new name{"quot", "lift"};
    g_quotient_ind       = new name{"quot", "ind"};
    g_quotient_mk        = new name{"quot", "mk"};
    g_quotient_sound     = new name{"quot", "sound"};
    g_quotient_exact     = new name{"quot", "exact"};
    g_ext                = new quotient_env_ext_reg();
}

void finalize_quotient_module() {
    delete g_ext;
    delete g_quotient_extension;
    delete g_quotient;
    delete g_quotient_lift;
    delete g_quotient_ind;
    delete g_quotient_mk;
    delete g_quotient_sound;
    delete g_quotient_exact;
}
}
