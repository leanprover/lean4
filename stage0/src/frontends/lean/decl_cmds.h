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
struct parser;
/** \brief Parse (optional) universe parameters <tt>'.{' l_1 ... l_k '}'</tt>
    Store the result in \c ps.

    Return true when levels were provided. */
bool parse_univ_params(parser & p, buffer<name> & ps);

/** \brief Add universe levels from \c found_ls to \c ls_buffer
    (only the levels that do not already occur in \c ls_buffer are added).

    Then sort \c ls_buffer (using the order in which the universe levels were declared). */
void update_univ_parameters(buffer<name> & ls_buffer, name_set const & found_ls, parser const & p);

enum class variable_kind { Variable, Axiom };

environment elab_var(parser & p, variable_kind const & k, cmd_meta const & meta, pos_info const & pos,
                     optional <binder_info> const & bi, name const & n, expr type, buffer <name> & ls_buffer);

/** \brief Parse a local attribute command */
environment local_attribute_cmd(parser & p);
void register_decl_cmds(cmd_table & r);

void initialize_decl_cmds();
void finalize_decl_cmds();
}
