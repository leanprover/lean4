/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"
#include "kernel/find_fn.h"

namespace lean {

class ginductive_decl {
    buffer<name> m_lp_names;
    buffer<expr> m_params;
    buffer<expr> m_inds;
    buffer<buffer<expr> > m_intro_rules;
public:
    ginductive_decl() {}
    ginductive_decl(buffer<name> const & lp_names, buffer<expr> const & params):
        m_lp_names(lp_names), m_params(params) {}
    ginductive_decl(buffer<name> const & lp_names, buffer<expr> const & params,
                    buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules):
        m_lp_names(lp_names), m_params(params), m_inds(inds), m_intro_rules(intro_rules) {}

    bool is_mutual() const { return m_inds.size() > 1; }
    unsigned get_num_params() const { return m_params.size(); }
    unsigned get_num_inds() const { return m_inds.size(); }
    unsigned get_num_intro_rules(unsigned ind_idx) const { return m_intro_rules[ind_idx].size(); }
    levels get_levels() const { return param_names_to_levels(to_list(m_lp_names)); }

    expr const & get_param(unsigned i) const { return m_params[i]; }
    expr const & get_ind(unsigned i) const { return m_inds[i]; }
    expr const & get_intro_rule(unsigned ind_idx, unsigned ir_idx) const { return m_intro_rules[ind_idx][ir_idx]; }
    buffer<expr> const & get_intro_rules(unsigned ind_idx) const { return m_intro_rules[ind_idx]; }

    buffer<name> const & get_lp_names() const { return m_lp_names; }
    buffer<expr> const & get_params() const { return m_params; }
    buffer<expr> const & get_inds() const { return m_inds; }
    buffer<buffer<expr> > const & get_intro_rules() const { return m_intro_rules; }

    buffer<name> & get_lp_names() { return m_lp_names; }
    buffer<expr> & get_params() { return m_params; }
    buffer<expr> & get_inds() { return m_inds; }
    buffer<buffer<expr> > & get_intro_rules() { return m_intro_rules; }

    expr get_c_ind(unsigned ind_idx) const {
        return mk_constant(mlocal_name(m_inds[ind_idx]), get_levels());
    }

    expr get_c_ind_params(unsigned ind_idx) const {
        return mk_app(mk_constant(mlocal_name(m_inds[ind_idx]), get_levels()), m_params);
    }

    expr get_c_ir(unsigned ind_idx, unsigned ir_idx) const {
        return mk_constant(mlocal_name(m_intro_rules[ind_idx][ir_idx]), get_levels());
    }

    expr get_c_ir_params(unsigned ind_idx, unsigned ir_idx) const {
        return mk_app(mk_constant(mlocal_name(m_intro_rules[ind_idx][ir_idx]), get_levels()), m_params);
    }

    void args_to_indices(buffer<expr> const & args, buffer<expr> & indices) const {
        for (unsigned i = get_num_params(); i < args.size(); ++i)
            indices.push_back(args[i]);
    }

    bool is_ind(expr const & e) const {
        return is_constant(e)
            && std::any_of(m_inds.begin(), m_inds.end(), [&](expr const & ind) {
                    return const_name(e) == mlocal_name(ind);
                });
    }

    bool has_ind_occ(expr const & t) const {
        return static_cast<bool>(find(t, [&](expr const & e, unsigned) { return is_ind(e); }));
    }
};

environment register_ginductive_decl(environment const & env, ginductive_decl const & decl);

bool is_ginductive(environment const & env, name const & ind_name);

/* \brief Returns the names of the introduction rules for the inductive type \e ind_name. */
optional<list<name> > get_ginductive_intro_rules(environment const & env, name const & ind_name);

/* \brief Returns the name of the inductive type if \e ir_name is indeed an introduction rule. */
optional<name> is_ginductive_intro_rule(environment const & env, name const & ir_name);

/* \brief Returns the number of parameters for the given inductive type \e ind_name. */
unsigned get_ginductive_num_params(environment const & env, name const & ind_name);

/* \brief Returns the names of all types that are mutually inductive with \e ind_name */
list<name> get_mut_ind_names(environment const & env, name const & ind_name);

void initialize_inductive_compiler_ginductive();
void finalize_inductive_compiler_ginductive();
}
