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
#include "kernel/kernel_exception.h"
#include "kernel/inductive/inductive.h"
#include "library/reducible.h"
#include "library/module.h"
#include "library/util.h"
#include "library/kernel_serializer.h"
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

static void projection_info_reader(deserializer & d, module_idx, shared_environment & senv,
                                   std::function<void(asynch_update_fn const &)> &,
                                   std::function<void(delayed_update_fn const &)> &) {
    name p, mk; unsigned nparams, i;
    d >> p >> mk >> nparams >> i;
    senv.update([=](environment const & env) -> environment {
            return save_projection_info_core(env, p, mk, nparams, i);
        });
}

/** \brief If \c e is a constructor application, then return the name of the constructor.
    Otherwise, return none.
*/
optional<name> is_constructor_app(environment const & env, expr const & e) {
    expr const & fn = get_app_fn(e);
    if (is_constant(fn))
        if (auto I = inductive::is_intro_rule(env, const_name(fn)))
            return optional<name>(const_name(fn));
    return optional<name>();
}

/** \brief If \c e is a constructor application, or a definition that wraps a
    constructor application, then return the name of the constructor.
    Otherwise, return none.
*/
optional<name> is_constructor_app_ext(environment const & env, expr const & e) {
    if (auto r = is_constructor_app(env, e))
        return r;
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return optional<name>();
    auto decl = env.find(const_name(f));
    if (!decl || !decl->is_definition() || decl->is_opaque())
        return optional<name>();
    expr const * it = &decl->get_value();
    while (is_lambda(*it))
        it = &binding_body(*it);
    return is_constructor_app_ext(env, *it);
}

static name * g_projection_macro_name    = nullptr;
static std::string * g_projection_opcode = nullptr;

class projection_macro_definition_cell : public macro_definition_cell {
    name m_proj_name;
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 1)
            throw exception(sstream() << "invalid '" << m_proj_name
                            << "' projection macro, incorrect number of arguments");
    }

public:
    projection_macro_definition_cell(name const & n):m_proj_name(n) {}
    name const & get_proj_name() const { return m_proj_name; }
    virtual name get_name() const { return m_proj_name; } // *g_projection_macro_name; }
    virtual format pp(formatter const &) const { return format(m_proj_name); }
    virtual void display(std::ostream & out) const { out << m_proj_name; }

    virtual pair<expr, constraint_seq> get_type(expr const & m, extension_context & ctx) const {
        check_macro(m);
        environment const & env = ctx.env();
        constraint_seq cs;
        expr s   = macro_arg(m, 0);
        expr s_t = ctx.whnf(ctx.infer_type(s, cs), cs);
        buffer<expr> I_args;
        expr const & I = get_app_args(s_t, I_args);
        if (is_constant(I)) {
            declaration proj_decl = env.get(m_proj_name);
            if (length(const_levels(I)) != proj_decl.get_num_univ_params())
                throw_kernel_exception(env, sstream() << "invalid projection application '" << m_proj_name
                                       << "', incorrect number of universe parameters", m);
            expr t = instantiate_type_univ_params(proj_decl, const_levels(I));
            I_args.push_back(s);
            unsigned num = I_args.size();
            for (unsigned i = 0; i < num; i++) {
                if (!is_pi(t))
                    throw_kernel_exception(env, sstream() << "invalid projection application '" << m_proj_name
                                           << "', number of arguments mismatch", m);
                t = binding_body(t);
            }
            return mk_pair(instantiate_rev(t, I_args.size(), I_args.data()), cs);
        } else {
            // TODO(Leo)
            throw_kernel_exception(env, sstream() << "projection macros do not support arbitrary terms "
                                   << "containing metavariables yet (solution: use trust-level 0)", m);
        }
    }

    // try to unfold projection argument into a \c c constructor application
    static optional<expr> process_proj_arg(environment const & env, name const & c, expr const & s) {
        if (optional<name> mk_name = is_constructor_app_ext(env, s)) {
            if (*mk_name == c) {
                expr new_s = s;
                while (is_app(new_s) && !is_constructor_app(env, new_s)) {
                    if (auto next_new_s = unfold_app(env, new_s))
                        new_s = *next_new_s;
                    else
                        return none_expr();
                }
                if (is_app(new_s))
                    return some_expr(new_s);
            }
        }
        return none_expr();
    }

    virtual optional<expr> expand(expr const & m, extension_context & ctx) const {
        check_macro(m);
        environment const & env = ctx.env();
        auto info = get_projection_info(env, m_proj_name);
        if (!info)
            throw_kernel_exception(env, sstream() << "invalid projection application '" << m_proj_name
                                   << "', constant is not a projection function", m);
        expr const & s  = macro_arg(m, 0);
        if (optional<expr> mk = process_proj_arg(env, info->m_constructor, s)) {
            // efficient version
            buffer<expr> mk_args;
            get_app_args(*mk, mk_args);
            unsigned i = info->m_nparams + info->m_i;
            lean_assert(i < mk_args.size());
            return some_expr(mk_args[i]);
        } else {
            // use definition
            constraint_seq cs;
            expr s_t = ctx.whnf(ctx.infer_type(s, cs), cs);
            if (cs)
                return none_expr();
            buffer<expr> I_args;
            expr const & I = get_app_args(s_t, I_args);
            if (!is_constant(I))
                return none_expr();
            return some_expr(mk_app(mk_app(mk_constant(m_proj_name, const_levels(I)), I_args), s));
        }
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_projection_opcode);
        s << m_proj_name;
    }
};

expr mk_projection_macro(name const & proj_name, expr const & e) {
    macro_definition def(new projection_macro_definition_cell(proj_name));
    return mk_macro(def, 1, &e);
}

void initialize_projection() {
    g_ext      = new projection_ext_reg();
    g_proj_key = new std::string("proj");
    register_module_object_reader(*g_proj_key, projection_info_reader);
    g_projection_macro_name = new name("projection");
    g_projection_opcode     = new std::string("Proj");
    register_macro_deserializer(*g_projection_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    name proj_name;
                                    d >> proj_name;
                                    return mk_projection_macro(proj_name, args[0]);
                                });
}

void finalize_projection() {
    delete g_proj_key;
    delete g_ext;
    delete g_projection_macro_name;
    delete g_projection_opcode;
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

environment mk_projections(environment const & env, name const & n, buffer<name> const & proj_names,
                           implicit_infer_kind infer_k, bool inst_implicit) {
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
        proj_type         = infer_implicit_params(proj_type, nparams, infer_k);
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

environment mk_projections(environment const & env, name const & n,
                           implicit_infer_kind infer_k, bool inst_implicit) {
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
    return mk_projections(env, n, proj_names, infer_k, inst_implicit);
}
}
