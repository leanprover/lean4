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
    virtual optional<expr> operator()(expr const & e, abstract_type_context & ctx) const;
    virtual optional<expr> is_stuck(expr const & e, abstract_type_context & ctx) const;
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
struct inductive_decl {
    name                 m_name;
    level_param_names    m_level_params;
    unsigned             m_num_params{0};
    expr                 m_type;
    list<intro_rule>     m_intro_rules;
    inductive_decl() {}
    inductive_decl(name const & n, level_param_names const & ls, unsigned nparams, expr const & type,
                   list<intro_rule> const & intro_rules):
        m_name(n), m_level_params(ls), m_num_params(nparams), m_type(type), m_intro_rules(intro_rules) {}
};

/** \brief Auxiliary class that stores the "compiled" version of an inductive declaration.
    It is used to save/read compiled .olean files efficiently. */
class certified_inductive_decl {
public:
    struct comp_rule {
        unsigned          m_num_bu;        // sum of number of arguments u and v in the corresponding introduction rule.
        expr              m_comp_rhs;      // computational rule RHS: Fun (A, C, e, b, u), (e_k_i b u v)
        comp_rule(unsigned num_bu, expr const & rhs):m_num_bu(num_bu), m_comp_rhs(rhs) {}
    };
private:
    unsigned           m_num_ACe;
    bool               m_elim_prop;
    // remark: if m_elim_prop == true, then inductive datatype levels == m_levels, otherwise it is tail(m_levels)
    bool               m_dep_elim;
    level_param_names  m_elim_levels; // eliminator levels
    expr               m_elim_type;
    inductive_decl     m_decl;
    bool               m_K_target;
    unsigned           m_num_indices;
    list<comp_rule>    m_comp_rules;
    bool               m_is_trusted;

    friend struct add_inductive_fn;
    friend class ::lean::read_certified_inductive_decl_fn;

    environment add_core(environment const & env, bool update_ext_only) const;
    environment add_constant(environment const & env, name const & n, level_param_names const & ls, expr const & t) const;

    certified_inductive_decl(unsigned num_ACe, bool elim_prop, bool dep_delim, level_param_names const & elim_levels,
                             expr const & elim_type, inductive_decl const & decl, bool K_target, unsigned nindices,
                             list<comp_rule> const & crules, bool is_trusted):
        m_num_ACe(num_ACe), m_elim_prop(elim_prop), m_dep_elim(dep_delim),
        m_elim_levels(elim_levels), m_elim_type(elim_type), m_decl(decl),
        m_K_target(K_target), m_num_indices(nindices), m_comp_rules(crules),
        m_is_trusted(is_trusted) {}
public:
    unsigned get_num_ACe() const { return m_num_ACe; }
    bool elim_prop_only() const { return m_elim_prop; }
    bool has_dep_elim() const { return m_dep_elim; }
    level_param_names const & get_elim_levels() const { return m_elim_levels; }
    expr const & get_elim_type() const { return m_elim_type; }
    inductive_decl const & get_decl() const { return m_decl; }
    bool is_K_target() const { return m_K_target; }
    unsigned get_num_indices() const { return m_num_indices; }
    list<comp_rule> get_comp_rules() const { return m_comp_rules; }
    bool is_trusted() const { return m_is_trusted; }

    /** \brief Update the environment with this "certified declaration"
        \remark If trust_level is 0, then declaration is rechecked. */
    environment add(environment const & env) const;
};

/** \brief Declare a finite set of mutually dependent inductive datatypes. */
pair<environment, certified_inductive_decl>
add_inductive(environment                  env,
              inductive_decl const &       decl,
              bool                         is_trusted);

/** \brief If \c n is the name of an inductive declaration in the environment \c env, then return the
    list of all inductive decls that were simultaneously defined with \c n.
    Return none otherwise */
optional<inductive_decl> is_inductive_decl(environment const & env, name const & n);

/** \brief If \c n is the name of an introduction rule in \c env, then return the name of the inductive datatype D
    s.t. \c n is an introduction rule of D. Otherwise, return none. */
optional<name> is_intro_rule(environment const & env, name const & n);

/** \brief If \c n is the name of an elimination rule in \c env, then return the name of the inductive datatype D
    s.t. \c n is an elimination rule of D. Otherwise, return none. */
optional<name> is_elim_rule(environment const & env, name const & n);

/** \brief Given the eliminator \c n, this function return the position of major premise */
optional<unsigned> get_elim_major_idx(environment const & env, name const & n);
bool is_elim_meta_app(type_checker & tc, expr const & e);

/** \brief Return the number of parameters in the given inductive datatype.
    If \c n is not an inductive datatype in \c env, then return none. */
inline optional<unsigned> get_num_params(environment const & env, name const & n) {
    if (auto decl = is_inductive_decl(env, n))
        return optional<unsigned>(decl->m_num_params);
    else
        return optional<unsigned>();
}

/** \brief Return the number of indices in the given inductive datatype.
    If \c n is not an inductive datatype in \c env, then return none. */
optional<unsigned> get_num_indices(environment const & env, name const & n);
/** \brief Return the number of minor premises in the given inductive datatype.
    If \c n is not an inductive datatype in \c env, then return none. */
optional<unsigned> get_num_minor_premises(environment const & env, name const & n);
/** \brief Return the number of introduction rules in the given inductive datatype.
    If \c n is not an inductive datatype in \c env, then return none. */
optional<unsigned> get_num_intro_rules(environment const & env, name const & n);

/** \brief Return true if the given datatype uses dependent elimination. */
bool has_dep_elim(environment const & env, name const & n);

/** \brief Return the eliminator/recursor associated with an inductive datatype */
name get_elim_name(name const & n);
}
void initialize_inductive_module();
void finalize_inductive_module();
}
