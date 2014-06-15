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
environment notation_cmd(parser & p);
environment infixl_cmd(parser & p);
environment infixr_cmd(parser & p);
environment postfix_cmd(parser & p);
}
