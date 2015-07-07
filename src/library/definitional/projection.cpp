/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/kernel_exception.h"
#include "kernel/inductive/inductive.h"
#include "library/reducible.h"
#include "library/projection.h"
#include "library/module.h"
#include "library/util.h"
#include "library/normalize.h"
#include "library/kernel_serializer.h"
#include "library/definitional/projection.h"

namespace lean {
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


static name * g_projection_macro_name    = nullptr;
static std::string * g_projection_opcode = nullptr;

/** \brief Auxiliary macro used to implement projections efficiently.
    They bypass the recursor.

    These macros are only used to speedup type checking when sending declarations to the kernel.
    During elaboration, we use a custom converter that never unfolds projections.
*/
class projection_macro_definition_cell : public macro_definition_cell {
    name              m_I_name;
    name              m_constructor_name;
    name              m_proj_name;
    unsigned          m_idx;
    level_param_names m_ps;
    expr              m_type;
    expr              m_val; // expanded form
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 1)
            throw exception(sstream() << "invalid '" << m_proj_name
                            << "' projection macro, incorrect number of arguments");
    }

public:
    projection_macro_definition_cell(name const & I, name const & c, name const & p, unsigned i,
                                     level_param_names const & ps, expr const & type, expr const & val):
        m_I_name(I), m_constructor_name(c), m_proj_name(p), m_idx(i), m_ps(ps), m_type(type), m_val(val) {}

    virtual name get_name() const { return m_proj_name; }
    virtual format pp(formatter const &) const { return format(m_proj_name); }
    virtual void display(std::ostream & out) const { out << m_proj_name; }
    virtual pair<expr, constraint_seq> check_type(expr const & m, extension_context & ctx, bool infer_only) const {
        check_macro(m);
        environment const & env = ctx.env();
        constraint_seq cs;
        expr s   = macro_arg(m, 0);
        expr s_t = ctx.whnf(ctx.check_type(s, cs, infer_only), cs);
        buffer<expr> I_args;
        expr const & I = get_app_args(s_t, I_args);
        if (!is_constant(I)) {
            // remark: this is not an issue since this macro should not be used during elaboration.
            throw_kernel_exception(env, sstream() << "projection macros do not support arbitrary terms "
                                   << "containing metavariables yet (solution: use trust-level 0)", m);
        }

        if (length(const_levels(I)) != length(m_ps))
            throw_kernel_exception(env, sstream() << "invalid projection application '" << m_proj_name
                                   << "', incorrect number of universe parameters", m);
        expr t = instantiate_univ_params(m_type, m_ps, const_levels(I));
        I_args.push_back(s);
        return mk_pair(instantiate_rev(t, I_args.size(), I_args.data()), cs);
    }

    virtual optional<expr> expand(expr const & m, extension_context & ctx) const {
        check_macro(m);
        expr const & s  = macro_arg(m, 0);
        constraint_seq cs;
        expr new_s      = ctx.whnf(s, cs);
        if (cs)
            return none_expr();
        buffer<expr> c_args;
        expr const & c  = get_app_args(new_s, c_args);
        if (is_constant(c) && const_name(c) == m_constructor_name && m_idx < c_args.size()) {
            return some_expr(c_args[m_idx]);
        } else {
            // expand into recursor
            expr s_type = ctx.whnf(ctx.infer_type(s, cs), cs);
            if (cs)
                return none_expr();
            buffer<expr> args;
            expr const & I = get_app_args(s_type, args);
            if (!is_constant(I) || length(m_ps) != length(const_levels(I)))
                return none_expr();
            expr r = instantiate_univ_params(m_val, m_ps, const_levels(I));
            args.push_back(new_s);
            return some(instantiate_rev(r, args.size(), args.data()));
        }
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_projection_opcode);
        s << m_I_name << m_constructor_name << m_proj_name << m_idx << m_ps << m_type << m_val;
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto other_ptr = dynamic_cast<projection_macro_definition_cell const *>(&other)) {
            return m_proj_name == other_ptr->m_proj_name;
        } else {
            return false;
        }
    }

    virtual unsigned hash() const {
        return m_proj_name.hash();
    }
};

static expr mk_projection_macro(name const & I, name const & c, name const & p, unsigned i,
                                level_param_names const & ps, expr const & type, expr const & val, expr const & arg) {
    macro_definition m(new projection_macro_definition_cell(I, c, p, i, ps, type, val));
    return mk_macro(m, 1, &arg);
}

void initialize_def_projection() {
    g_projection_macro_name = new name("projection");
    g_projection_opcode     = new std::string("Proj");
    register_macro_deserializer(*g_projection_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    name I_name, c_name, proj_name; unsigned idx;
                                    level_param_names ps; expr type, val;
                                    d >> I_name >> c_name >> proj_name >> idx >> ps >> type >> val;
                                    return mk_projection_macro(I_name, c_name, proj_name, idx,
                                                               ps, type, val, args[0]);
                                });
}

void finalize_def_projection() {
    delete g_projection_macro_name;
    delete g_projection_opcode;
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
        if (new_env.trust_lvl() > 0) {
            // use macros
            expr mval  = proj_val;
            expr mtype = proj_type;
            for (unsigned i = 0; i < proj_args.size(); i++) {
                mval  = binding_body(mval);
                mtype = binding_body(mtype);
            }
            proj_val = mk_projection_macro(n, inductive::intro_rule_name(intro), proj_name,
                                           nparams + i, lvl_params, mtype, mval, proj_args.back());
            proj_val = Fun(proj_args, proj_val);
        }
        bool use_conv_opt = false;
        declaration new_d = mk_definition(env, proj_name, lvl_params, proj_type, proj_val,
                                          use_conv_opt);
        new_env = module::add(new_env, check(new_env, new_d));
        new_env = set_reducible(new_env, proj_name, reducible_status::Reducible);
        new_env = add_unfold_hint(new_env, proj_name, nparams);
        new_env = save_projection_info(new_env, proj_name, inductive::intro_rule_name(intro), nparams, i, inst_implicit);
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
