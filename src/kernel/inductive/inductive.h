/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include <tuple>
#include "util/list.h"
#include "kernel/environment.h"

namespace lean {
class read_certified_inductive_decl_fn;
namespace inductive {
/** \brief Normalizer extension for applying inductive datatype computational rules. */
class inductive_normalizer_extension : public normalizer_extension {
public:
    virtual optional<pair<expr, constraint_seq>> operator()(expr const & e, extension_context & ctx) const;
    virtual optional<expr> is_stuck(expr const & e, extension_context & ctx) const;
    virtual bool supports(name const & feature) const;
    virtual bool is_recursor(environment const & env, name const & n) const;
    virtual bool is_builtin(environment const & env, name const & n) const;
};

/** \brief Introduction rule */
typedef expr intro_rule;
inline intro_rule mk_intro_rule(name const & n, expr const & t) { return mk_local(n, t); }
inline name const & intro_rule_name(intro_rule const & r) { return mlocal_name(r); }
inline expr const & intro_rule_type(intro_rule const & r) { return mlocal_type(r); }

/** \brief Inductive datatype */
typedef std::tuple<name,                // datatype name
                   expr,                // type
                   list<intro_rule>     // introduction rules for this datatype
                   > inductive_decl;

inline name const & inductive_decl_name(inductive_decl const & d) { return std::get<0>(d); }
inline expr const & inductive_decl_type(inductive_decl const & d) { return std::get<1>(d); }
inline list<intro_rule> const & inductive_decl_intros(inductive_decl const & d) { return std::get<2>(d); }

/** \brief Auxiliary class that stores the "compiled" version of an inductive declaration.
    It is used to save/read compiled .olean files efficiently.
*/
class certified_inductive_decl {
public:
    struct comp_rule {
        unsigned          m_num_bu;        // sum of number of arguments u and v in the corresponding introduction rule.
        expr              m_comp_rhs;      // computational rule RHS: Fun (A, C, e, b, u), (e_k_i b u v)
        comp_rule(unsigned num_bu, expr const & rhs):m_num_bu(num_bu), m_comp_rhs(rhs) {}
    };

    struct data {
        inductive_decl    m_decl;
        bool              m_K_target;
        unsigned          m_num_indices;
        list<comp_rule>   m_comp_rules;
        data(inductive_decl const & decl, bool is_K_target, unsigned num_indices, list<comp_rule> const & rules):
            m_decl(decl), m_K_target(is_K_target), m_num_indices(num_indices), m_comp_rules(rules) {}
    };

private:
    level_param_names  m_levels; // eliminator levels
    unsigned           m_num_params;
    unsigned           m_num_ACe;
    bool               m_elim_prop;
    // remark: if m_elim_prop == true, then inductive datatype levels == m_levels, otherwise it is tail(m_levels)
    bool               m_dep_elim;
    list<expr>         m_elim_types;
    list<data>         m_decl_data;

    friend struct add_inductive_fn;
    friend class ::lean::read_certified_inductive_decl_fn;

    environment add_core(environment const & env, bool update_ext_only) const;
    environment add_constant(environment const & env, name const & n, level_param_names const & ls, expr const & t) const;

    certified_inductive_decl(level_param_names const & ps, unsigned num_params, unsigned num_ACe,
                             bool elim_prop, bool dep_delim, list<expr> const & ets, list<data> const & d):
        m_levels(ps), m_num_params(num_params), m_num_ACe(num_ACe),
        m_elim_prop(elim_prop), m_dep_elim(dep_delim), m_elim_types(ets), m_decl_data(d) {}
public:
    level_param_names const & get_univ_params() const { return m_levels; }
    unsigned get_num_params() const { return m_num_params; }
    unsigned get_num_ACe() const { return m_num_ACe; }
    bool elim_prop_only() const { return m_elim_prop; }
    bool has_dep_elim() const { return m_dep_elim; }
    list<expr> const & get_elim_types() const { return m_elim_types; }
    list<data> const & get_decl_data() const { return m_decl_data; }

    /** \brief Update the environment with this "certified declaration"
        \remark If trust_level is 0, then declaration is rechecked.
    */
    environment add(environment const & env) const;
};

/** \brief Declare a finite set of mutually dependent inductive datatypes. */
pair<environment, certified_inductive_decl>
add_inductive(environment                  env,
              level_param_names const &    level_params,
              unsigned                     num_params,
              list<inductive_decl> const & decls);

typedef std::tuple<level_param_names, unsigned, list<inductive::inductive_decl>> inductive_decls;

/**
    \brief If \c n is the name of an inductive declaration in the environment \c env, then return the
    list of all inductive decls that were simultaneously defined with \c n.
    Return none otherwise
*/
optional<inductive_decls> is_inductive_decl(environment const & env, name const & n);

/**
   \brief If \c n is the name of an introduction rule in \c env, then return the name of the inductive datatype D
   s.t. \c n is an introduction rule of D. Otherwise, return none.
*/
optional<name> is_intro_rule(environment const & env, name const & n);

/**
   \brief If \c n is the name of an elimination rule in \c env, then return the name of the inductive datatype D
   s.t. \c n is an elimination rule of D. Otherwise, return none.
*/
optional<name> is_elim_rule(environment const & env, name const & n);

/** \brief Given the eliminator \c n, this function return the position of major premise */
optional<unsigned> get_elim_major_idx(environment const & env, name const & n);
bool is_elim_meta_app(type_checker & tc, expr const & e);

/** \brief Return the number of parameters in the given inductive datatype.
    If \c n is not an inductive datatype in \c env, then return none.
*/
inline optional<unsigned> get_num_params(environment const & env, name const & n) {
    if (auto ds = is_inductive_decl(env, n))
        return optional<unsigned>(std::get<1>(*ds));
    else
        return optional<unsigned>();
}

/** \brief Return the number of indices in the given inductive datatype.
    If \c n is not an inductive datatype in \c env, then return none.
*/
optional<unsigned> get_num_indices(environment const & env, name const & n);
/** \brief Return the number of minor premises in the given inductive datatype.
    If \c n is not an inductive datatype in \c env, then return none.
*/
optional<unsigned> get_num_minor_premises(environment const & env, name const & n);
/** \brief Return the number of introduction rules in the given inductive datatype.
    If \c n is not an inductive datatype in \c env, then return none.
*/
optional<unsigned> get_num_intro_rules(environment const & env, name const & n);
/** \brief Return the number of type formers in the given inductive datatype.
    If \c n is not an inductive datatype in \c env, then return none.
*/
optional<unsigned> get_num_type_formers(environment const & env, name const & n);

/** \brief Return true if the given datatype uses dependent elimination. */
bool has_dep_elim(environment const & env, name const & n);

/** \brief Return the eliminator/recursor associated with an inductive datatype */
name get_elim_name(name const & n);
}
void initialize_inductive_module();
void finalize_inductive_module();
}
