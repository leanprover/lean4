/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "frontends/lean/parser_config.h"
#include "frontends/lean/cmd_table.h"
namespace lean {
class parser;
/** \brief Return true iff the current token is a notation declaration */
bool curr_is_notation_decl(parser & p);
/** \brief Parse a notation declaration, throws an error if the current token is not a "notation declaration".
    If allow_local is true, then notation may contain reference to local constants.
*/
notation_entry parse_notation(parser & p, bool overload, buffer<token_entry> & new_tokens, bool allow_local);

/** \brief Parse local notation */
environment local_notation_cmd(parser & p);

void register_notation_cmds(cmd_table & r);

bool is_notation_cmd(name const & cmd_name);

void initialize_notation_cmd();
void finalize_notation_cmd();
}
