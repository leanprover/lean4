/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Quotient types for kernels with proof irrelevance.
*/
#include "kernel/quotient/quotient.h"
#include "util/sstream.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "kernel/environment.h"
#include "kernel/abstract_type_context.h"
#include "kernel/inductive/inductive.h"
#include <vector>

namespace lean {
static name * g_quotient_extension = nullptr;
static name * g_quotient       = nullptr;
static name * g_quotient_lift  = nullptr;
static name * g_quotient_ind   = nullptr;
static name * g_quotient_mk    = nullptr;

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

static environment add_constant(environment const & env, name const & n, std::initializer_list<name> lvls, expr const & type) {
    auto cd = check(env, mk_constant_assumption(n, level_param_names(lvls), type));
    return env.add(cd);
}

static void check_eq_type(environment const & env) {
    optional<inductive::inductive_decl> decl = inductive::is_inductive_decl(env, "eq");
    if (!decl) throw exception("failed to initialize quot module, environment does not have 'eq' type");
    if (length(decl->m_level_params) != 1)
        throw exception("failed to initialize quot module, unexpected number of universe params at 'eq' type");
    level u = mk_param_univ(head(decl->m_level_params));
    expr alpha = mk_local("α", "α", mk_sort(u), mk_implicit_binder_info());
    expr expected_eq_type = Pi(alpha, mk_arrow(alpha, mk_arrow(alpha, mk_Prop())));
    if (decl->m_type != expected_eq_type)
        throw exception("failed to initialize quot module, 'eq' has an expected type");
    if (length(decl->m_intro_rules) != 1)
        throw exception("failed to initialize quot module, unexpected number of constructors for 'eq' type");
    expr a = mk_local("a", alpha);
    expr expected_eq_refl_type = Pi(alpha, Pi(a, mk_app(mk_constant("eq", {u}), alpha, a, a)));
    if (mlocal_type(head(decl->m_intro_rules)) != expected_eq_refl_type) {
        throw exception("failed to initialize quot module, unexpected type for 'eq' type constructor");
    }
}

environment declare_quotient(environment const & env) {
    check_eq_type(env);
    environment new_env = env;
    name u_name("u");
    level u         = mk_param_univ(u_name);
    expr Type_u     = mk_sort(u);
    expr alpha      = mk_local("α", "α", Type_u, mk_implicit_binder_info());
    expr r          = mk_local("r", mk_arrow(alpha, mk_arrow(alpha, mk_Prop())));
    /* constant {u} quot {α : Type u} (r : α → α → Prop) : Type u */
    new_env = add_constant(new_env, *g_quotient, {u_name}, Pi(alpha, Pi(r, Type_u)));
    expr quot_r     = mk_app(mk_constant(*g_quotient, {u}), alpha, r);
    expr a          = mk_local("a", alpha);
    /* constant {u} quot.mk {α : Type u} (r : α → α → Prop) (a : α) : @quot.{u} α r */
    new_env = add_constant(new_env, *g_quotient_mk, {u_name},
                           Pi(alpha, Pi(r, Pi(a, quot_r))));
    /* make r implicit */
    r               = mk_local("r", "r", mk_arrow(alpha, mk_arrow(alpha, mk_Prop())), mk_implicit_binder_info());
    name v_name("v");
    level v         = mk_param_univ(v_name);
    expr Type_v     = mk_sort(v);
    expr beta       = mk_local("β", "β", Type_v, mk_implicit_binder_info());
    expr f          = mk_local("f", mk_arrow(alpha, beta));
    expr b          = mk_local("b", alpha);
    expr r_a_b      = mk_app(r, a, b);
    /* f a = f b */
    expr f_a_eq_f_b = mk_app(mk_constant("eq", {v}), beta, mk_app(f, a), mk_app(f, b));
    /* (∀ a b : α, r a b → f a = f b) */
    expr sanity     = Pi(a, Pi(b, mk_arrow(r_a_b, f_a_eq_f_b)));
    /* constant {u v} quot.lift {α : Type u} {r : α → α → Prop} {β : Type v} (f : α → β)
                                : (∀ a b : α, r a b → f a = f b) →  @quot.{u} α r → β */
    new_env = add_constant(new_env, *g_quotient_lift, {u_name, v_name},
                           Pi(alpha, Pi(r, Pi(beta, Pi(f, mk_arrow(sanity, mk_arrow(quot_r, beta)))))));
    /* {β : @quot.{u} α r → Prop} */
    beta            = mk_local("β", "β", mk_arrow(quot_r, mk_Prop()), mk_implicit_binder_info());
    expr quot_mk_a  = mk_app(mk_constant(*g_quotient_mk, {u}), alpha, r, a);
    expr all_quot   = Pi(a, mk_app(beta, quot_mk_a));
    expr q          = mk_local("q", quot_r);
    expr beta_q     = mk_app(beta, q);
    /* constant {u} quot.ind {α : Type u} {r : α → α → Prop} {β : @quot.{u} α r → Prop}
                   : (∀ a : α, β (@quot.mk.{u} α r a)) → ∀ q : @quot.{u} α r, β q */
    new_env = add_constant(new_env, *g_quotient_ind, {u_name},
                           Pi(alpha, Pi(r, Pi(beta, mk_arrow(all_quot, Pi(q, beta_q))))));
    quotient_env_ext ext = get_extension(env);
    if (ext.m_initialized)
        throw exception("failed to initialize quot module, already initialized");
    ext.m_initialized = true;
    return update(new_env, ext);
}

optional<expr> quotient_normalizer_extension::operator()(expr const & e, abstract_type_context & ctx) const {
    environment const & env = ctx.env();
    expr const & fn         = get_app_fn(e);
    if (!is_constant(fn))
        return none_expr();
    quotient_env_ext const & ext = get_extension(env);
    if (!ext.m_initialized)
        return none_expr();
    unsigned mk_pos;
    unsigned arg_pos;
    if (const_name(fn) == *g_quotient_lift) {
        mk_pos  = 5;
        arg_pos = 3;
    } else if (const_name(fn) == *g_quotient_ind) {
        mk_pos  = 4;
        arg_pos = 3;
    } else {
        return none_expr();
    }

    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() <= mk_pos)
        return none_expr();

    expr mk = ctx.whnf(args[mk_pos]);
    expr const & mk_fn = get_app_fn(mk);
    if (!is_constant(mk_fn))
        return none_expr();
    if (const_name(mk_fn) != *g_quotient_mk)
        return none_expr();

    expr const & f = args[arg_pos];
    expr r = mk_app(f, app_arg(mk));
    unsigned elim_arity = mk_pos+1;
    if (args.size() > elim_arity)
        r = mk_app(r, args.size() - elim_arity, args.begin() + elim_arity);
    return some_expr(r);
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

    expr mk_app = ctx.whnf(args[mk_pos]);
    return ctx.is_stuck(mk_app);
}

optional<expr> quotient_normalizer_extension::is_stuck(expr const & e, abstract_type_context & ctx) const {
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

bool has_quotient(environment const & env) {
    return get_extension(env).m_initialized;
}

std::vector<name> quotient_required_decls() {
    return {"eq"};
}

void initialize_quotient_module() {
    g_quotient_extension = new name("quotient_extension");
    g_quotient           = new name{"quot"};
    g_quotient_lift      = new name{"quot", "lift"};
    g_quotient_ind       = new name{"quot", "ind"};
    g_quotient_mk        = new name{"quot", "mk"};
    g_ext                = new quotient_env_ext_reg();
}

void finalize_quotient_module() {
    delete g_ext;
    delete g_quotient_extension;
    delete g_quotient;
    delete g_quotient_lift;
    delete g_quotient_ind;
    delete g_quotient_mk;
}
}
