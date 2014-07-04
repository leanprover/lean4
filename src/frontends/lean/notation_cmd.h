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

environment precedence_cmd(parser & p);
environment notation_cmd_core(parser & p, bool overload);
environment infixl_cmd_core(parser & p, bool overload);
environment infixr_cmd_core(parser & p, bool overload);
environment postfix_cmd_core(parser & p, bool overload);
environment prefix_cmd_core(parser & p, bool overload);

/** \brief Return true iff the current token is a notation declaration */
bool curr_is_notation_decl(parser & p);
/** \brief Parse a notation declaration, throws an error if the current token is not a "notation declaration". */
notation_entry parse_notation(parser & p, bool overload, buffer<token_entry> & new_tokens);

void register_notation_cmds(cmd_table & r);
}
