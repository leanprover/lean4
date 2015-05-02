/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/cmd_table.h"
namespace lean {
class parser;
expr parse_calc(parser & p);
bool is_calc_annotation(expr const & e);
/** \brief Given an operator name \c op, return the symmetry rule associated with, number of arguments, and universe parameters.
    Return none if the operator does not have a symmetry rule associated with it.
*/
optional<std::tuple<name, unsigned, unsigned>> get_calc_symm_info(environment const & env, name const & op);
optional<std::tuple<name, unsigned, unsigned>> get_calc_refl_info(environment const & env, name const & op);
optional<std::tuple<name, unsigned, unsigned>> get_calc_subst_info(environment const & env, name const & op);
void initialize_calc();
void finalize_calc();
}
