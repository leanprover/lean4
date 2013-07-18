/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved. 
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura 
*/
#pragma once
#include <iostream>

namespace lean {
void          set_verbosity_level(unsigned lvl);
unsigned      get_verbosity_level();
std::ostream& verbose_stream();
void          set_verbose_stream(std::ostream& s);
#define lean_verbose(LVL, CODE) { if (get_verbosity_level() >= LVL) { CODE } }
}


