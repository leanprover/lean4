/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/module.h"
#include "library/protected.h"
#include "library/reducible.h"
#include "library/aux_recursors.h"
#include "library/constructions/util.h"

namespace lean {
using inductive::inductive_decl;

enum class drec_kind {DRec, DRecOn, DCasesOn};

struct mk_drec_fn {
    environment const & env;
    name_generator      ngen;
    type_checker        tc;
    name const &        I;
    drec_kind           kind;
    inductive_decl      I_ind_decl;
    name                I_rec_name;
    declaration         I_rec_decl;
    declaration         I_decl;
    unsigned            num_idx_major;
    unsigned            num_minors;
    unsigned            major_idx;
    unsigned            num_params;
    levels              lvls;
    bool                elim_to_prop;
    levels              I_lvls;

    buffer<expr> rec_params;
    buffer<expr> drec_params;
    buffer<expr> rec_args; // arguments for rec used to define drec

    mk_drec_fn(environment const & _env, name const & _I, drec_kind k):
        env(_env), ngen(mk_constructions_name_generator()),
        tc(env), I(_I), kind(k),
        I_ind_decl(*inductive::is_inductive_decl(env, I)),
        I_rec_name(inductive::get_elim_name(I)),
        I_rec_decl(env.get(I_rec_name)),
        I_decl(env.get(I)),
        num_idx_major(*inductive::get_num_indices(env, I) + 1),
        num_minors(*inductive::get_num_minor_premises(env, I)),
        major_idx(*inductive::get_elim_major_idx(env, I_rec_name)),
        num_params(I_ind_decl.m_num_params),
        lvls(param_names_to_levels(I_rec_decl.get_univ_params())),
        elim_to_prop(I_rec_decl.get_num_univ_params() == I_decl.get_num_univ_params()),
        I_lvls(elim_to_prop ? lvls : tail(lvls)) {
    }

    expr mk_local_from_binding(expr const & b) {
        lean_assert(is_binding(b));
        return mk_local(ngen.next(), binding_name(b), binding_domain(b), binding_info(b));
    }

    expr init_rec_params() {
        expr rec_type = I_rec_decl.get_type();
        while (is_pi(rec_type)) {
            expr local = mk_local_from_binding(rec_type);
            rec_type   = instantiate(binding_body(rec_type), local);
            rec_params.push_back(local);
        }
        return rec_type;
    }

    void copy_params() {
        for (unsigned i = 0; i < num_params; i++) {
            drec_params.push_back(rec_params[i]);
            rec_args.push_back(rec_params[i]);
        }
    }

    expr mk_motive() {
        // Construct motive
        expr rec_motive = rec_params[num_params];
        name C_name     = mlocal_name(rec_motive);
        expr rec_motive_type = mlocal_type(rec_motive);
        buffer<expr> motive_params;
        while (is_pi(rec_motive_type)) {
            expr local = mk_local_from_binding(rec_motive_type);
            rec_motive_type = instantiate(binding_body(rec_motive_type), local);
            motive_params.push_back(local);
        }
        expr new_param_type  = mk_app(mk_app(mk_constant(I, I_lvls), num_params, rec_params.data()), motive_params);
        expr new_param       = mk_local(ngen.next(), "h", new_param_type, binder_info());
        expr new_motive_type = Pi(motive_params, Pi(new_param, rec_motive_type));
        expr new_motive      = update_mlocal(rec_motive, new_motive_type);
        expr motive_arg      = Fun(motive_params, Pi(new_param, mk_app(mk_app(new_motive, motive_params), new_param)));
        drec_params.push_back(new_motive);
        rec_args.push_back(motive_arg);
        return new_motive;
    }

    void mk_minor_premises(expr const & motive) {
        // Add minor premises to rec_params and rec_args
        unsigned i = num_params + 1;
        for (auto ir : I_ind_decl.m_intro_rules) {
            name const & ir_name = inductive::intro_rule_name(ir);
            buffer<bool> rec_mask;
            get_constructor_rec_arg_mask(env, ir_name, rec_mask);
            unsigned num_fields = rec_mask.size() - num_params;
            expr const & minor  = rec_params[i];
            expr minor_type     = mlocal_type(minor);
            buffer<expr> new_minor_params;
            buffer<expr> recursive_params;
            buffer<expr> app_params;
            buffer<expr> app_args;
            unsigned j = 0;
            while (is_pi(minor_type)) {
                expr local      = mk_local_from_binding(minor_type);
                if (j < num_fields && rec_mask[num_params+j]) {
                    recursive_params.push_back(local);
                }
                if (j < num_fields) {
                    new_minor_params.push_back(local);
                    app_params.push_back(local);
                    app_args.push_back(local);
                } else {
                    // inductive hypothesis
                    lean_assert(j - num_fields < recursive_params.size());
                    expr const & recursive_param = recursive_params[j - num_fields];
                    expr ih_type = mlocal_type(local);
                    buffer<expr> ih_params;
                    while (is_pi(ih_type)) {
                        expr ih_param = mk_local_from_binding(ih_type);
                        ih_params.push_back(ih_param);
                        ih_type = instantiate(binding_body(ih_type), ih_param);
                    }
                    buffer<expr> new_C_args;
                    get_app_args(ih_type, new_C_args);
                    expr new_C_pre   = mk_app(motive, new_C_args);
                    if (kind != drec_kind::DCasesOn) {
                        expr new_C       = mk_app(new_C_pre, mk_app(recursive_param, ih_params));
                        expr new_ih_type = Pi(ih_params, new_C);
                        expr new_ih      = update_mlocal(local, new_ih_type);
                        new_minor_params.push_back(new_ih);
                    }
                    expr h_type = mlocal_type(recursive_param);
                    while (is_pi(h_type))
                        h_type = binding_body(h_type);
                    h_type = instantiate_rev(h_type, ih_params);
                    expr h           = mk_local(ngen.next(), "_h", h_type, binder_info());
                    expr app_ih_type = Pi(ih_params, Pi(h, mk_app(new_C_pre, h)));
                    expr app_ih      = update_mlocal(local, app_ih_type);
                    app_params.push_back(app_ih);
                    if (kind != drec_kind::DCasesOn) {
                        app_args.push_back(Fun(ih_params, mk_app(mk_app(app_ih, ih_params),
                                                                 mk_app(recursive_param, ih_params))));
                    }
                }
                j++;
                minor_type      = instantiate(binding_body(minor_type), local);
            }
            lean_assert(new_minor_params.size() == num_fields +
                        (kind == drec_kind::DCasesOn ? 0 : recursive_params.size()));
            buffer<expr> new_C_args;
            get_app_args(minor_type, new_C_args);
            expr constructor_app = mk_app(mk_app(mk_constant(ir_name, I_lvls), num_params, rec_params.data()),
                                          num_fields, new_minor_params.data());
            new_C_args.push_back(constructor_app);
            expr new_C = mk_app(motive, new_C_args);
            expr new_minor_type  = Pi(new_minor_params, new_C);
            expr new_minor       = update_mlocal(minor, new_minor_type);
            drec_params.push_back(new_minor);
            expr _h_type         = tc.infer(constructor_app);
            expr _h              = mk_local(ngen.next(), "_", _h_type, binder_info());
            rec_args.push_back(Fun(app_params, Fun(_h, mk_app(new_minor, app_args))));
            i++;
        }
    }

    name mk_drec_name() {
        switch (kind) {
        case drec_kind::DRec:     return name(I, "drec");
        case drec_kind::DRecOn:   return name(I, "drec_on");
        case drec_kind::DCasesOn: return name(I, "dcases_on");
        }
        lean_unreachable();
    }

    environment add_decl(expr const & rec_type, expr const & motive) {
        buffer<expr> new_C_args;
        get_app_args(rec_type, new_C_args);
        expr drec_type    = Pi(drec_params, mk_app(mk_app(motive, new_C_args), rec_params[major_idx]));
        expr rec_cnst     = mk_constant(I_rec_name, lvls);
        expr drec_value   = Fun(drec_params, mk_app(rec_cnst, rec_args));
        name drec_name    = mk_drec_name();
        declaration new_d = mk_definition_inferring_trusted(env, drec_name, I_rec_decl.get_univ_params(),
                                                            drec_type, drec_value,
                                                            reducibility_hints::mk_abbreviation());
        environment new_env = module::add(env, check(env, new_d));
        new_env = set_reducible(new_env, drec_name, reducible_status::Reducible, true);
        new_env = add_aux_recursor(new_env, drec_name);
        return add_protected(new_env, drec_name);
    }

    void add_indices_major_params() {
        for (unsigned i = 0; i < num_idx_major; i++)
            drec_params.push_back(rec_params[num_params + 1 + num_minors + i]);
    }

    void add_indices_major_args() {
        for (unsigned i = 0; i < num_idx_major; i++)
            rec_args.push_back(rec_params[num_params + 1 + num_minors + i]);
    }

    environment operator()() {
        expr rec_type = init_rec_params();
        copy_params();
        expr motive = mk_motive();

        if (kind == drec_kind::DRecOn || kind == drec_kind::DCasesOn)
            add_indices_major_params();

        mk_minor_premises(motive);

        if (kind == drec_kind::DRec)
            add_indices_major_params();
        add_indices_major_args();

        // Add major again
        rec_args.push_back(rec_params[major_idx]);

        return add_decl(rec_type, motive);
    }
};

environment mk_drec(environment const & env, name const & I) {
    if (!is_inductive_predicate(env, I))
        throw exception(sstream() << "error in 'drec' generation, '" << I << "' is not an inductive predicate");
    environment new_env = mk_drec_fn(env, I, drec_kind::DRec)();
    new_env             = mk_drec_fn(new_env, I, drec_kind::DRecOn)();
    new_env             = mk_drec_fn(new_env, I, drec_kind::DCasesOn)();
    return new_env;
}
}
