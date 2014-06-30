/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/buffer.h"
#include "kernel/expr.h"
#include "frontends/lean/cmd_table.h"
namespace lean {
class parser;
/**
    \brief Parse (optional) universe parameters <tt>'.{' l_1 ... l_k '}'</tt>
    Store the result in \c ps.
    Return true when levels were provided.
*/
bool parse_univ_params(parser & p, buffer<name> & ps);
/**
   \brief Add universe levels from \c found_ls to \c ls_buffer (only the levels that do not already occur in \c ls_buffer are added).
   Then sort \c ls_buffer (using the order in which the universe levels were declared).
*/
void update_univ_parameters(buffer<name> & ls_buffer, name_set const & found_ls, parser const & p);
/**
   \brief Copy the parameters associated with the local names in \c local_names to \c section_ps.
   Then sort \c section_ps (using the order in which they were declared).
*/
void mk_section_params(name_set const & local_names, parser const & p, buffer<expr> & section_ps);
/**
   \brief Return the levels in \c ls that are defined in the section.
*/
levels collect_section_levels(level_param_names const & ls, parser & p);
void register_decl_cmds(cmd_table & r);
}
