/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
class parser;
environment precedence_cmd(parser & p);
environment notation_cmd_core(parser & p, bool overload);
environment infixl_cmd_core(parser & p, bool overload);
environment infixr_cmd_core(parser & p, bool overload);
environment postfix_cmd_core(parser & p, bool overload);
inline environment notation_cmd(parser & p) { return notation_cmd_core(p, true); }
inline environment infixl_cmd(parser & p) { return infixl_cmd_core(p, true); }
inline environment infixr_cmd(parser & p) { return infixr_cmd_core(p, true); }
inline environment postfix_cmd(parser & p) { return postfix_cmd_core(p, true); }
}
