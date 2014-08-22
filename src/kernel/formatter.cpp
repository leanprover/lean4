/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "kernel/formatter.h"

namespace lean {
static std::unique_ptr<std::function<void(std::ostream &, expr const & e)>> g_print;

void set_print_fn(std::function<void(std::ostream &, expr const &)> const & fn) {
    g_print.reset(new std::function<void(std::ostream &, expr const &)>(fn));
}

std::ostream & operator<<(std::ostream & out, expr const & e) {
    if (g_print) {
        (*g_print)(out, e);
    } else {
        throw exception("print function is not available, Lean was not initialized correctly");
    }
    return out;
}

void print(lean::expr const & a) { std::cout << a << std::endl; }
}
