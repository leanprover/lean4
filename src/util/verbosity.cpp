/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved. 
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura 
*/
#include "verbosity.h"

namespace lean {

unsigned g_verbosity_level = 0;

void set_verbosity_level(unsigned lvl) {
    g_verbosity_level = lvl;
}

unsigned get_verbosity_level() {
    return g_verbosity_level;
}

static std::ostream* g_verbose_stream = &std::cerr;

void set_verbose_stream(std::ostream& str) {
    g_verbose_stream = &str;
}

std::ostream& verbose_stream() {
    return *g_verbose_stream;
}

}
