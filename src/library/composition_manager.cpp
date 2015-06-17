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

pair<environment, name> compose(type_checker & tc, name const & g, name const & f, optional<name> const & gf) {
    environment const & env = tc.env();
    composition_manager_ext ext = get_extension(env);
    if (name const * it = ext.m_cache.find(mk_pair(g, f)))
        return mk_pair(env, *it);
    declaration const & f_decl = env.get(f);
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
    expr b       = mk_app(mk_constant(f, f_ls), f_domain);
    expr new_val = Fun(f_domain, mk_app(mk_app(mk_constant(g, const_levels(B)), B_args), b));
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
    while (env.find(new_name)) {
        new_name = base_name.append_after(idx);
        idx++;
    }

    ext.m_cache.insert(mk_pair(g, f), new_name);
    environment new_env = module::add(env, check(env, mk_definition(env, new_name, f_decl.get_univ_params(),
                                                                    new_type, new_val)));
    new_env = module::add(new_env, *g_key, [=](environment const &, serializer & s) { s << g << f << new_name; });
    return mk_pair(update(new_env, ext), new_name);
}

pair<environment, name> compose(environment const & env, name const & g, name const & f, optional<name> const & gf) {
    type_checker tc(env);
    return compose(tc, g, f, gf);
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
