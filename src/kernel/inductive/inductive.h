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
#include "kernel/context.h"

namespace lean {
namespace inductive {
/** \brief Return a normalizer extension for inductive dataypes. */
std::unique_ptr<normalizer_extension> mk_extension();

/** \brief Introduction rule */
typedef std::tuple<name,              // introduction rule name
                   telescope,         // arguments
                   expr               // result type
                   > intro_rule;

inline name const & intro_rule_name(intro_rule const & r) { return std::get<0>(r); }
inline telescope const & intro_rule_args(intro_rule const & r) { return std::get<1>(r); }
inline expr const & intro_rule_type(intro_rule const & r) { return std::get<2>(r); }

/** \brief Inductive datatype */
typedef std::tuple<name,                // datatype name
                   telescope,           // indices
                   list<intro_rule>     // introduction rules for this datatype
                   > inductive_decl;

inline name const & inductive_decl_name(inductive_decl const & d) { return std::get<0>(d); }
inline telescope const & inductive_decl_indices(inductive_decl const & d) { return std::get<1>(d); }
inline list<intro_rule> const & inductive_decl_intros(inductive_decl const & d) { return std::get<2>(d); }

/** \brief Declare a finite set of mutually dependent inductive datatypes. */
environment add_inductive(environment const &          env,
                          level_param_names const &    level_params,
                          telescope const &            params,
                          list<inductive_decl> const & decls,
                          // By default the resultant inductive datatypes live in max(level_params),
                          // we can add an offset/lift k, and the resultant type is succ^k(max(level_params)).
                          // If none is provided, then for impredicative environments the result types are Bool/Prop (level 0)
                          optional<unsigned> const &   univ_offset = optional<unsigned>(0));

/** \brief Declare a single inductive datatype. */
environment add_inductive(environment const &        env,
                          name const &               ind_name,         // name of new inductive datatype
                          level_param_names const &  level_params,     // level parameters
                          telescope const &          params,           // parameters
                          telescope const &          indices,          // indices
                          list<intro_rule> const &   intro_rules,      // introduction rules
                          optional<unsigned> const & univ_offset = optional<unsigned>(0));
}
}
