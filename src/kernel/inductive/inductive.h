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
namespace inductive {
/** \brief Normalizer extension for applying inductive datatype computational rules. */
class inductive_normalizer_extension : public normalizer_extension {
public:
    virtual optional<pair<expr, constraint_seq>> operator()(expr const & e, extension_context & ctx) const;
    virtual optional<expr> is_stuck(expr const & e, extension_context & ctx) const;
    virtual bool supports(name const & feature) const;
};

/** \brief Introduction rule */
typedef pair<name, expr> intro_rule;

inline name const & intro_rule_name(intro_rule const & r) { return r.first; }
inline expr const & intro_rule_type(intro_rule const & r) { return r.second; }

/** \brief Inductive datatype */
typedef std::tuple<name,                // datatype name
                   expr,                // type
                   list<intro_rule>     // introduction rules for this datatype
                   > inductive_decl;

inline name const & inductive_decl_name(inductive_decl const & d) { return std::get<0>(d); }
inline expr const & inductive_decl_type(inductive_decl const & d) { return std::get<1>(d); }
inline list<intro_rule> const & inductive_decl_intros(inductive_decl const & d) { return std::get<2>(d); }

/** \brief Declare a finite set of mutually dependent inductive datatypes. */
environment add_inductive(environment                  env,
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
