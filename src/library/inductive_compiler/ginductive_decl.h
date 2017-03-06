/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"
#include "kernel/find_fn.h"
#include "library/tactic/simp_lemmas.h"
#include "library/inductive_compiler/util.h"

namespace lean {

class ginductive_decl {
    unsigned m_nest_depth{0};
    bool m_is_inner;
    buffer<name> m_lp_names;
    buffer<expr> m_params;
    buffer<expr> m_inds;
    buffer<buffer<expr> > m_intro_rules;
    buffer<unsigned> m_num_indices;

    buffer<unsigned>                  m_ir_offsets; // # total intro rules @ basic
    buffer<pair<unsigned, unsigned> > m_idx_to_ir_range; // # total inds @ mutual

    buffer<name> m_packs;
    buffer<name> m_unpacks;

    optional<simp_lemmas> m_sizeof_lemmas;
public:
    ginductive_decl(unsigned nest_depth, buffer<name> const & lp_names, buffer<expr> const & params,
                    buffer<unsigned> const & num_indices, buffer<unsigned> const & ir_offsets):
        m_nest_depth(nest_depth), m_is_inner(true), m_lp_names(lp_names), m_params(params), m_num_indices(num_indices), m_ir_offsets(ir_offsets) {}

    ginductive_decl(unsigned nest_depth, buffer<name> const & lp_names, buffer<expr> const & params, buffer<unsigned> const & ir_offsets):
        m_nest_depth(nest_depth), m_is_inner(true), m_lp_names(lp_names), m_params(params), m_ir_offsets(ir_offsets) {
        m_num_indices.emplace_back(1);
    }

    ginductive_decl(environment const & env, unsigned nest_depth, buffer<name> const & lp_names, buffer<expr> const & params,
                    buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules):
        m_nest_depth(nest_depth), m_is_inner(false), m_lp_names(lp_names), m_params(params), m_inds(inds), m_intro_rules(intro_rules) {
        // Two things to do:
        // 1. initialize num_indices
        // 2. initialize ir_offsets
        for (unsigned ind_idx = 0; ind_idx < inds.size(); ++ind_idx) {
            m_num_indices.emplace_back(::lean::get_num_indices(env, inds[ind_idx]));
            for (unsigned ir_idx = 0; ir_idx < intro_rules[ind_idx].size(); ++ir_idx) {
                m_ir_offsets.emplace_back(0);
            }
        }
    }

    void set_sizeof_lemmas(simp_lemmas const & sizeof_lemmas) {
        m_sizeof_lemmas = optional<simp_lemmas>(sizeof_lemmas);
    }

    bool has_sizeof_lemmas() const { return static_cast<bool>(m_sizeof_lemmas); }
    simp_lemmas get_sizeof_lemmas() const { return *m_sizeof_lemmas; }

    unsigned get_nest_depth() const { return m_nest_depth; }
    bool is_inner() const { return m_is_inner; }

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

    buffer<unsigned> const & get_num_indices() const { return m_num_indices; }
    buffer<unsigned> & get_num_indices() { return m_num_indices; }

    buffer<unsigned> const & get_ir_offsets() const { return m_ir_offsets; }
    buffer<unsigned> & get_ir_offsets() { return m_ir_offsets; }

    buffer<pair<unsigned, unsigned> > const & get_idx_to_ir_range() const { return m_idx_to_ir_range; }
    buffer<pair<unsigned, unsigned> > & get_idx_to_ir_range() { return m_idx_to_ir_range; }

    buffer<name> const & get_packs() const { return m_packs; }
    buffer<name> & get_packs() { return m_packs; }
    buffer<name> const & get_unpacks() const { return m_unpacks; }
    buffer<name> & get_unpacks() { return m_unpacks; }

    expr mk_const(name const & n) const { return mk_constant(n, get_levels()); }
    expr mk_const_params(name const & n) const { return mk_app(mk_const(n), m_params); }
    expr get_c_ind(unsigned ind_idx) const { return mk_const(mlocal_name(m_inds[ind_idx])); }
    expr get_c_ind_params(unsigned ind_idx) const { return mk_const_params(mlocal_name(m_inds[ind_idx])); }
    expr get_c_ir(unsigned ind_idx, unsigned ir_idx) const { return mk_const(mlocal_name(m_intro_rules[ind_idx][ir_idx])); }
    expr get_c_ir_params(unsigned ind_idx, unsigned ir_idx) const { return mk_const_params(mlocal_name(m_intro_rules[ind_idx][ir_idx])); }

    bool is_ind_name(name const & n) const;
    bool is_ind_name(name const & n, unsigned ind_idx) { return n == mlocal_name(m_inds[ind_idx]); }
    bool is_ind(expr const & e, unsigned ind_idx) const { return e == get_c_ind(ind_idx); }
    bool is_ind(expr const & e) const { return is_constant(e) && is_ind_name(const_name(e)); }
    bool has_ind_occ(expr const & t) const;
    bool is_ind_app(expr const & e, unsigned ind_idx) const { return is_ind(get_app_fn(e), ind_idx); }
    bool is_ind_app(expr const & e, unsigned ind_idx, buffer<expr> & indices) const;
    bool is_ind_app(expr const & e) const { return is_ind(get_app_fn(e)); }
    bool is_ind_app(expr const & e, buffer<expr> & indices) const;
    bool is_ir_name(name const & n, unsigned ind_idx) const;
    bool is_ir_name(name const & n) const;
    bool is_ir(expr const & e, unsigned ind_idx) const;
    bool is_ir(expr const & e) const;
    void args_to_indices(buffer<expr> const & args, buffer<expr> & indices) const;
    expr get_app_indices(expr const & e, buffer<expr> & indices) const;
    bool is_param(expr const & e) const;
    level get_result_level(environment const & env) const;
};
}
