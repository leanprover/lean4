/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Quotient types.
*/
#include "util/name_generator.h"
#include "kernel/quot.h"
#include "kernel/local_ctx.h"

namespace lean {
name * quot_consts::g_quot = nullptr;
name * quot_consts::g_quot_lift = nullptr;
name * quot_consts::g_quot_ind  = nullptr;
name * quot_consts::g_quot_mk   = nullptr;

static void check_eq_type(environment const & env) {
    constant_info eq_info = env.get("Eq");
    if (!eq_info.is_inductive()) throw exception("failed to initialize quot module, environment does not have 'Eq' type");
    inductive_val eq_val  = eq_info.to_inductive_val();
    if (length(eq_info.get_lparams()) != 1)
        throw exception("failed to initialize quot module, unexpected number of universe params at 'Eq' type");
    if (length(eq_val.get_cnstrs()) != 1)
        throw exception("failed to initialize quot module, unexpected number of constructors for 'Eq' type");
    local_ctx lctx;
    name_generator g;
    {
        level u = mk_univ_param(head(eq_info.get_lparams()));
        expr alpha = lctx.mk_local_decl(g, "α", mk_sort(u), mk_implicit_binder_info());
        expr expected_eq_type = lctx.mk_pi(alpha, mk_arrow(alpha, mk_arrow(alpha, mk_Prop())));
        if (expected_eq_type != eq_info.get_type())
            throw exception("failed to initialize quot module, 'Eq' has an expected type");
    }
    {
        constant_info eq_refl_info = env.get(head(eq_val.get_cnstrs()));
        level u = mk_univ_param(head(eq_refl_info.get_lparams()));
        expr alpha = lctx.mk_local_decl(g, "α", mk_sort(u), mk_implicit_binder_info());
        expr a = lctx.mk_local_decl(g, "a", alpha);
        expr expected_eq_refl_type = lctx.mk_pi({alpha, a}, mk_app(mk_constant("Eq", {u}), alpha, a, a));
        if (eq_refl_info.get_type() != expected_eq_refl_type)
            throw exception("failed to initialize quot module, unexpected type for 'Eq' type constructor");
    }
}

environment environment::add_quot() const {
    if (is_quot_initialized())
        return *this;
    check_eq_type(*this);
    environment new_env = *this;
    name u_name("u");
    local_ctx lctx;
    name_generator g;
    level u         = mk_univ_param(u_name);
    expr Sort_u     = mk_sort(u);
    expr alpha      = lctx.mk_local_decl(g, "α", Sort_u, mk_implicit_binder_info());
    expr r          = lctx.mk_local_decl(g, "r", mk_arrow(alpha, mk_arrow(alpha, mk_Prop())));
    /* constant {u} quot {α : Sort u} (r : α → α → Prop) : Sort u */
    new_env.add_core(constant_info(quot_val(*quot_consts::g_quot, {u_name}, lctx.mk_pi({alpha, r}, Sort_u), quot_kind::Type)));
    expr quot_r     = mk_app(mk_constant(*quot_consts::g_quot, {u}), alpha, r);
    expr a          = lctx.mk_local_decl(g, "a", alpha);
    /* constant {u} quot.mk {α : Sort u} (r : α → α → Prop) (a : α) : @quot.{u} α r */
    new_env.add_core(constant_info(quot_val(*quot_consts::g_quot_mk, {u_name}, lctx.mk_pi({alpha, r, a}, quot_r), quot_kind::Mk)));
    /* make r implicit */
    lctx = local_ctx();
    alpha           = lctx.mk_local_decl(g, "α", Sort_u, mk_implicit_binder_info());
    r               = lctx.mk_local_decl(g, "r", mk_arrow(alpha, mk_arrow(alpha, mk_Prop())), mk_implicit_binder_info());
    quot_r          = mk_app(mk_constant(*quot_consts::g_quot, {u}), alpha, r);
    a               = lctx.mk_local_decl(g, "a", alpha);
    name v_name("v");
    level v         = mk_univ_param(v_name);
    expr Sort_v     = mk_sort(v);
    expr beta       = lctx.mk_local_decl(g, "β", Sort_v, mk_implicit_binder_info());
    expr f          = lctx.mk_local_decl(g, "f", mk_arrow(alpha, beta));
    expr b          = lctx.mk_local_decl(g, "b", alpha);
    expr r_a_b      = mk_app(r, a, b);
    /* f a = f b */
    expr f_a_eq_f_b = mk_app(mk_constant("Eq", {v}), beta, mk_app(f, a), mk_app(f, b));
    /* (∀ a b : α, r a b → f a = f b) */
    expr sanity     = lctx.mk_pi({a, b}, mk_arrow(r_a_b, f_a_eq_f_b));
    /* constant {u v} quot.lift {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β)
                                : (∀ a b : α, r a b → f a = f b) →  @quot.{u} α r → β */
    new_env.add_core(constant_info(quot_val(*quot_consts::g_quot_lift, {u_name, v_name},
                                            lctx.mk_pi({alpha, r, beta, f}, mk_arrow(sanity, mk_arrow(quot_r, beta))), quot_kind::Lift)));
    /* {β : @quot.{u} α r → Prop} */
    beta            = lctx.mk_local_decl(g, "β", mk_arrow(quot_r, mk_Prop()), mk_implicit_binder_info());
    expr quot_mk_a  = mk_app(mk_constant(*quot_consts::g_quot_mk, {u}), alpha, r, a);
    expr all_quot   = lctx.mk_pi(a, mk_app(beta, quot_mk_a));
    expr q          = lctx.mk_local_decl(g, "q", quot_r);
    expr beta_q     = mk_app(beta, q);
    /* constant {u} quot.ind {α : Sort u} {r : α → α → Prop} {β : @quot.{u} α r → Prop}
                   : (∀ a : α, β (@quot.mk.{u} α r a)) → ∀ q : @quot.{u} α r, β q */
    new_env.add_core(constant_info(quot_val(*quot_consts::g_quot_ind, {u_name},
                                            lctx.mk_pi({alpha, r, beta}, mk_pi("mk", all_quot, lctx.mk_pi(q, beta_q))), quot_kind::Ind)));
    new_env.mark_quot_initialized();
    return new_env;
}

void initialize_quot() {
    quot_consts::g_quot      = new name{"Quot"};
    mark_persistent(quot_consts::g_quot->raw());
    quot_consts::g_quot_lift = new name{"Quot", "lift"};
    mark_persistent(quot_consts::g_quot_lift->raw());
    quot_consts::g_quot_ind  = new name{"Quot", "ind"};
    mark_persistent(quot_consts::g_quot_ind->raw());
    quot_consts::g_quot_mk   = new name{"Quot", "mk"};
    mark_persistent(quot_consts::g_quot_mk->raw());
}

void finalize_quot() {
    delete quot_consts::g_quot;
    delete quot_consts::g_quot_lift;
    delete quot_consts::g_quot_ind;
    delete quot_consts::g_quot_mk;
}
}
