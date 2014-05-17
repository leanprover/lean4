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
/** \brief Return a normalizer extension for inductive dataypes. */
std::unique_ptr<normalizer_extension> mk_extension();

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

/** \brief Declare a single inductive datatype. */
environment add_inductive(environment const &        env,
                          name const &               ind_name,         // name of new inductive datatype
                          level_param_names const &  level_params,     // level parameters
                          unsigned                   num_params,       // number of params
                          expr const &               type,             // type of the form: params -> indices -> Type
                          list<intro_rule> const &   intro_rules);     // introduction rules
}
}
