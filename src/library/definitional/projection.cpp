/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "kernel/inductive/inductive.h"
#include "library/reducible.h"
#include "library/module.h"
#include "library/definitional/projection.h"

namespace lean {
/** \brief This environment extension stores information about all projection functions
    defined in an environment object.
*/
struct projection_ext : public environment_extension {
    name_map<projection_info> m_info;
    projection_ext() {}
};

struct projection_ext_reg {
    unsigned m_ext_id;
    projection_ext_reg() {
        m_ext_id = environment::register_extension(std::make_shared<projection_ext>());
    }
};

static projection_ext_reg * g_ext = nullptr;
static projection_ext const & get_extension(environment const & env) {
    return static_cast<projection_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, projection_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<projection_ext>(ext));
}

static std::string * g_proj_key = nullptr;

static environment save_projection_info_core(environment const & env, name const & p, name const & mk, unsigned nparams, unsigned i) {
    projection_ext ext = get_extension(env);
    ext.m_info.insert(p, projection_info(mk, nparams, i));
    return update(env, ext);
}

static environment save_projection_info(environment const & env, name const & p, name const & mk, unsigned nparams, unsigned i) {
    environment new_env = save_projection_info_core(env, p, mk, nparams, i);
    return module::add(new_env, *g_proj_key, [=](serializer & s) { s << p << mk << nparams << i; });
}

projection_info const * get_projection_info(environment const & env, name const & p) {
    projection_ext const & ext = get_extension(env);
    return ext.m_info.find(p);
}

static void projection_reader(deserializer & d, module_idx, shared_environment & senv,
                              std::function<void(asynch_update_fn const &)> &,
                              std::function<void(delayed_update_fn const &)> &) {
    name p, mk; unsigned nparams, i;
    d >> p >> mk >> nparams >> i;
    senv.update([=](environment const & env) -> environment {
            return save_projection_info_core(env, p, mk, nparams, i);
        });
}

void initialize_projection() {
    g_ext      = new projection_ext_reg();
    g_proj_key = new std::string("proj");
    register_module_object_reader(*g_proj_key, projection_reader);
}

void finalize_projection() {
    delete g_proj_key;
    delete g_ext;
}

/** \brief Return true iff the type named \c S can be viewed as
    a structure in the given environment.

    If not, generate an error message using \c pos.
*/
bool is_structure(environment const & env, name const & S) {
    optional<inductive::inductive_decls> idecls = inductive::is_inductive_decl(env, S);
    if (!idecls || length(std::get<2>(*idecls)) != 1)
        return false;
    inductive::inductive_decl decl   = head(std::get<2>(*idecls));
    return length(inductive::inductive_decl_intros(decl)) == 1 && *inductive::get_num_indices(env, S) == 0;
}

/** \brief If \c is a constructor application, then return the name of the constructor.
    Otherwise, return none.
*/
optional<name> is_constructor_app(environment const & env, expr const & e) {
    expr const & fn = get_app_fn(e);
    if (is_constant(fn))
        if (auto I = inductive::is_intro_rule(env, const_name(fn)))
            return optional<name>(const_name(fn));
    return optional<name>();
}

/** \brief If \c d is the name of a definition of the form
            Fun (a : A), t
    where t is a constructor application, then return the name of the constructor.
*/
optional<name> is_constructor_app_def(environment const & env, name const & d) {
    if (auto decl = env.find(d)) {
        expr const * it = &decl->get_value();
        while (is_lambda(*it))
            it = &binding_body(*it);
        return is_constructor_app(env, *it);
    }
    return optional<name>();
}

/** \brief Return the name of constructor and projection functions iff \c e is of the form

        (mk ... (pr ...) ...)

    where \c mk is a constructor of a structure, and at least of the arguments is a projection \c pr
    where \c pr is not necessarily a projection associated with \c mk.
    In this case, the name of \c pr is returned. Otherwise, none is returned.
*/
optional<pair<name, name>> is_constructor_of_projections(environment const & env, expr const & e) {
    expr const & fn = get_app_fn(e);
    if (is_constant(fn)) {
        if (auto I = inductive::is_intro_rule(env, const_name(fn))) {
            if (is_structure(env, *I)) {
                expr const * it = &e;
                while (is_app(*it)) {
                    expr const & arg = app_arg(*it);
                    expr const & pr  = get_app_fn(arg);
                    if (is_constant(pr)) {
                        if (auto info = get_projection_info(env, const_name(pr))) {
                            if (info->m_nparams + 1 == get_app_num_args(arg))
                                return some(mk_pair(const_name(pr), const_name(pr)));
                        }
                    }
                    it = &app_fn(*it);
                }
            }
        }
    }
    return optional<pair<name, name>>();
}

/** \brief Return the name of constructor and projection functions iff \c d is the name of a definition of the form

       Fun (a : A), t

    where is_constructor_of_projections(env, t)
 */
optional<pair<name, name>> is_constructor_of_projections_def(environment const & env, name const & d) {
    if (auto decl = env.find(d)) {
        expr const * it = &decl->get_value();
        while (is_lambda(*it))
            it = &binding_body(*it);
        return is_constructor_of_projections(env, *it);
    }
    return optional<pair<name, name>>();
}

[[ noreturn ]] static void throw_ill_formed(name const & n) {
    throw exception(sstream() << "projection generation, '" << n << "' is an ill-formed inductive datatype");
}

static pair<unsigned, inductive::intro_rule> get_nparam_intro_rule(environment const & env, name const & n) {
    optional<inductive::inductive_decls> decls = inductive::is_inductive_decl(env, n);
    if (!decls)
        throw exception(sstream() << "projection generation, '" << n << "' is not an inductive datatype");
    optional<unsigned> num_indices = inductive::get_num_indices(env, n);
    if (num_indices && *num_indices > 0)
        throw exception(sstream() << "projection generation, '"
                        << n << "' is an indexed inductive datatype family");
    unsigned num_params = std::get<1>(*decls);
    for (auto const & decl : std::get<2>(*decls)) {
        if (inductive::inductive_decl_name(decl) == n) {
            auto intros = inductive::inductive_decl_intros(decl);
            if (length(intros) != 1)
                throw exception(sstream() << "projection generation, '"
                                << n << "' does not have a single constructor");
            return mk_pair(num_params, head(intros));
        }
    }
    throw_ill_formed(n);
}

static bool is_prop(expr type) {
    while (is_pi(type)) {
        type = binding_body(type);
    }
    return is_sort(type) && is_zero(sort_level(type));
}

environment mk_projections(environment const & env, name const & n, buffer<name> const & proj_names, bool inst_implicit) {
    // Given an inductive datatype C A (where A represent parameters)
    //   intro : Pi A (x_1 : B_1[A]) (x_2 : B_2[A, x_1]) ..., C A
    //
    // we generate projections of the form
    //   proj_i A (c : C A) : B_i[A, (proj_1 A n), ..., (proj_{i-1} A n)]
    //     C.rec A (fun (x : C A), B_i[A, ...]) (fun (x_1 ... x_n), x_i) c
    auto p = get_nparam_intro_rule(env, n);
    name_generator ngen;
    unsigned nparams             = p.first;
    inductive::intro_rule intro  = p.second;
    expr intro_type              = inductive::intro_rule_type(intro);
    name rec_name                = inductive::get_elim_name(n);
    declaration ind_decl         = env.get(n);
    if (env.impredicative() && is_prop(ind_decl.get_type()))
        throw exception(sstream() << "projection generation, '" << n << "' is a proposition");
    declaration rec_decl         = env.get(rec_name);
    level_param_names lvl_params = ind_decl.get_univ_params();
    levels lvls                  = param_names_to_levels(lvl_params);
    buffer<expr> params; // datatype parameters
    for (unsigned i = 0; i < nparams; i++) {
        if (!is_pi(intro_type))
            throw_ill_formed(n);
        expr param = mk_local(ngen.next(), binding_name(intro_type), binding_domain(intro_type), binder_info());
        intro_type = instantiate(binding_body(intro_type), param);
        params.push_back(param);
    }
    expr C_A                     = mk_app(mk_constant(n, lvls), params);
    binder_info c_bi             = inst_implicit ? mk_inst_implicit_binder_info() : binder_info();
    expr c                       = mk_local(ngen.next(), name("c"), C_A, c_bi);
    buffer<expr> intro_type_args; // arguments that are not parameters
    expr it = intro_type;
    while (is_pi(it)) {
        expr local = mk_local(ngen.next(), binding_name(it), binding_domain(it), binding_info(it));
        intro_type_args.push_back(local);
        it = instantiate(binding_body(it), local);
    }
    buffer<expr> projs; // projections generated so far
    unsigned i = 0;
    environment new_env = env;
    for (name const & proj_name : proj_names) {
        if (!is_pi(intro_type))
            throw exception(sstream() << "generating projection '" << proj_name << "', '"
                            << n << "' does not have sufficient data");
        expr result_type   = binding_domain(intro_type);
        buffer<expr> proj_args;
        proj_args.append(params);
        proj_args.push_back(c);
        expr type_former   = Fun(c, result_type);
        expr minor_premise = Fun(intro_type_args, mk_var(intro_type_args.size() - i - 1));
        expr major_premise = c;
        type_checker tc(new_env);
        level l            = sort_level(tc.ensure_sort(tc.infer(result_type).first).first);
        levels rec_lvls    = append(to_list(l), lvls);
        expr rec           = mk_constant(rec_name, rec_lvls);
        buffer<expr> rec_args;
        rec_args.append(params);
        rec_args.push_back(type_former);
        rec_args.push_back(minor_premise);
        rec_args.push_back(major_premise);
        expr rec_app      = mk_app(rec, rec_args);
        expr proj_type    = Pi(proj_args, result_type);
        bool strict       = true;
        proj_type         = infer_implicit(proj_type, nparams, strict);
        expr proj_val     = Fun(proj_args, rec_app);
        bool opaque       = false;
        bool use_conv_opt = false;
        declaration new_d = mk_definition(env, proj_name, lvl_params, proj_type, proj_val,
                                          opaque, rec_decl.get_module_idx(), use_conv_opt);
        new_env = module::add(new_env, check(new_env, new_d));
        new_env = set_reducible(new_env, proj_name, reducible_status::On);
        new_env = save_projection_info(new_env, proj_name, inductive::intro_rule_name(intro), nparams, i);
        expr proj         = mk_app(mk_app(mk_constant(proj_name, lvls), params), c);
        intro_type        = instantiate(binding_body(intro_type), proj);
        i++;
    }
    return new_env;
}

static name mk_fresh_name(environment const & env, buffer<name> const & names, name const & s) {
    unsigned i = 1;
    name c = s;
    while (true) {
        if (!env.find(c) &&
            std::find(names.begin(), names.end(), c) == names.end())
            return c;
        c = s.append_after(i);
        i++;
    }
}

environment mk_projections(environment const & env, name const & n, bool inst_implicit) {
    auto p  = get_nparam_intro_rule(env, n);
    unsigned num_params = p.first;
    inductive::intro_rule ir = p.second;
    expr type = inductive::intro_rule_type(ir);
    buffer<name> proj_names;
    unsigned i = 0;
    while (is_pi(type)) {
        if (i >= num_params)
            proj_names.push_back(mk_fresh_name(env, proj_names, n + binding_name(type)));
        i++;
        type = binding_body(type);
    }
    return mk_projections(env, n, proj_names, inst_implicit);
}
}
