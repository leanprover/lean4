/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
static char const * g_extra_code =
    "function Consts(s)\n"
    "  r = {}\n"
    "  i = 1\n"
    "  for c in string.gmatch(s, '[^ ,;\\t\\n]+') do\n"
    "     r[i] = Const(c)\n"
    "     i = i + 1\n"
    "  end\n"
    "  return unpack(r)\n"
    "end\n";
