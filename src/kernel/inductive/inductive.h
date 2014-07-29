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
    virtual optional<expr> operator()(expr const & e, extension_context & ctx) const;
    virtual bool may_reduce_later(expr const & e, extension_context & ctx) const;
    virtual bool supports(name const & feature) const;
};

/** \brief Introduction rule */
typedef std::pair<name, expr> intro_rule;

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
}
}
