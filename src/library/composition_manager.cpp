/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "util/sstream.h"
#include "kernel/type_checker.h"
#include "kernel/declaration.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/replace_visitor.h"
#include "library/reducible.h"
#include "library/projection.h"
#include "library/util.h"
#include "library/module.h"

namespace lean {
struct composition_manager_ext : public environment_extension {
    typedef rb_map<name_pair, name, name_pair_quick_cmp> cache;
    cache m_cache;
};

struct composition_manager_ext_reg {
    unsigned m_ext_id;
    composition_manager_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<composition_manager_ext>()); }
};

static composition_manager_ext_reg * g_ext = nullptr;
static std::string * g_key = nullptr;
static composition_manager_ext const & get_extension(environment const & env) {
    return static_cast<composition_manager_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, composition_manager_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<composition_manager_ext>(ext));
}

struct elim_proj_mk : public replace_visitor {
    environment const & m_env;
    type_checker_ptr    m_tc;

    virtual expr visit_binding(expr const & e) {
        // stop at binders
        return e;
    }
    virtual expr visit_app(expr const & e) {
        expr const & fn = get_app_fn(e);
        if (is_constant(fn) && is_projection(m_env, const_name(fn))) {
            expr new_e = m_tc->whnf(e).first;
            if (new_e != e)
                return visit(new_e);
        }
        return replace_visitor::visit_app(e);
    }

    elim_proj_mk(environment const & env):
        m_env(env), m_tc(mk_opaque_type_checker(env, name_generator())) {}
};

// Return true iff d is a declaration of the form (mk ... )
static bool is_constructor_decl(environment const & env, declaration const & d) {
    if (!d.is_definition())
        return false;
    expr val = d.get_value();
    while (is_lambda(val))
        val = binding_body(val);
    return static_cast<bool>(is_constructor_app(env, val));
}

// Return true iff d is a declaration of the form (mk ... (pr ...)  ... )
static bool is_constructor_of_projections_decl(environment const & env, declaration const & d) {
    if (!d.is_definition())
        return false;
    expr val = d.get_value();
    while (is_lambda(val))
        val = binding_body(val);
    auto mk_name = is_constructor_app(env, val);
    if (!mk_name)
        return false;
    buffer<expr> args;
    get_app_args(val, args);
    for (expr const & arg : args) {
        expr const & fn = get_app_fn(arg);
        if (is_constant(fn) && is_projection(env, const_name(fn)))
            return true;
    }
    return false;
}

pair<environment, name> compose(environment const & env, type_checker & tc, name const & g, name const & f, optional<name> const & gf) {
    composition_manager_ext ext = get_extension(env);
    if (name const * it = ext.m_cache.find(mk_pair(g, f)))
        return mk_pair(env, *it);
    declaration const & f_decl = env.get(f);
    declaration const & g_decl = env.get(g);
    levels f_ls = param_names_to_levels(f_decl.get_univ_params());
    expr f_type = instantiate_type_univ_params(f_decl, f_ls);
    buffer<expr> f_domain;
    name_generator ngen = tc.mk_ngen();
    expr f_codomain     = to_telescope(ngen, f_type, f_domain);
    buffer<expr> B_args;
    expr const & B = get_app_args(f_codomain, B_args);
    if (!is_constant(B))
        throw exception(sstream() << "invalid function composition, '" << f << "' codomain must be of the form (B ...), "
                        "where B is a constant");
    expr new_val_body;
    if (is_constructor_decl(env, f_decl) && is_constructor_of_projections_decl(env, g_decl)) {
        expr fn      = instantiate_value_univ_params(f_decl, f_ls);
        expr gn      = instantiate_value_univ_params(g_decl, const_levels(B));
        expr b       = head_beta_reduce(mk_app(fn, f_domain));
        new_val_body = elim_proj_mk(env)(head_beta_reduce(mk_app(mk_app(gn, B_args), b)));
    } else {
        // do not expand
        expr b       = mk_app(mk_constant(f, f_ls), f_domain);
        new_val_body = mk_app(mk_app(mk_constant(g, const_levels(B)), B_args), b);
    }
    expr new_val      = Fun(f_domain, new_val_body);
    expr new_type;
    try {
        new_type = tc.infer(new_val).first;
    } catch (exception &) {
        throw exception(sstream() << "invalid function composition '" << g << "' o '" << f << "'\n");
    }
    new_type = head_beta_reduce(new_type);
    name base_name;
    if (gf) {
        base_name = *gf;
    } else {
        base_name = g + f;
    }

    name new_name = base_name;
    unsigned idx  = 1;

    // make sure name is unique
    while (true) {
        auto it = env.find(new_name);
        if (!it)
            break;
        if (it->is_definition() && it->get_num_univ_params() == f_decl.get_num_univ_params()) {
            // check if definitions is definitionally equal to exisiting one
            expr it_type = instantiate_type_univ_params(*it, f_ls);
            expr it_val  = instantiate_value_univ_params(*it, f_ls);
            if (tc.is_def_eq(it_type, new_type).first && tc.is_def_eq(it_val, new_val).first) {
                // environment already contains a definition that is definitially equal to the new one.
                // So, we do not need to create a new one
                ext.m_cache.insert(mk_pair(g, f), new_name);
                environment new_env = module::add(env, *g_key, [=](environment const &, serializer & s) { s << g << f << new_name; });
                return mk_pair(update(new_env, ext), new_name);
            }
        }
        new_name = base_name.append_after(idx);
        idx++;
    }

    ext.m_cache.insert(mk_pair(g, f), new_name);
    bool use_conv_opt   = false;
    environment new_env = module::add(env, check(env, mk_definition(env, new_name, f_decl.get_univ_params(),
                                                                    new_type, new_val, use_conv_opt)));
    new_env = module::add(new_env, *g_key, [=](environment const &, serializer & s) { s << g << f << new_name; });
    return mk_pair(update(new_env, ext), new_name);
}

pair<environment, name> compose(environment const & env, name const & g, name const & f, optional<name> const & gf) {
    type_checker tc(env);
    return compose(env, tc, g, f, gf);
}

static void composition_reader(deserializer & d, shared_environment & senv,
                               std::function<void(asynch_update_fn const &)> &,
                               std::function<void(delayed_update_fn const &)> &) {
    name g, f, gf;
    d >> g >> f >> gf;
    senv.update([=](environment const & env) -> environment {
            composition_manager_ext ext = get_extension(env);
            ext.m_cache.insert(mk_pair(g, f), gf);
            return update(env, ext);
        });
}

void initialize_composition_manager() {
    g_ext = new composition_manager_ext_reg();
    g_key = new std::string("comp");
    register_module_object_reader(*g_key, composition_reader);
}

void finalize_composition_manager() {
    delete g_key;
    delete g_ext;
}
}
