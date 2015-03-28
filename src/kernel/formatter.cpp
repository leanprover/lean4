/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/sexpr/option_declarations.h"
#include "kernel/formatter.h"

#ifndef LEAN_DEFAULT_FORMATTER_HIDE_FULL_TERMS
#define LEAN_DEFAULT_FORMATTER_HIDE_FULL_TERMS false
#endif

namespace lean {
static name * g_formatter_hide_full = nullptr;

name const & get_formatter_hide_full_terms_name() { return *g_formatter_hide_full; }
bool get_formatter_hide_full_terms(options const & opts) { return opts.get_bool(*g_formatter_hide_full, LEAN_DEFAULT_FORMATTER_HIDE_FULL_TERMS); }

static std::function<void(std::ostream &, expr const & e)> * g_print = nullptr;

void set_print_fn(std::function<void(std::ostream &, expr const &)> const & fn) {
    delete g_print;
    g_print = new std::function<void(std::ostream &, expr const &)>(fn);
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

void initialize_formatter() {
    g_formatter_hide_full = new name{"formatter", "hide_full_terms"};
    register_bool_option(*g_formatter_hide_full, LEAN_DEFAULT_FORMATTER_HIDE_FULL_TERMS,
                         "(formatter) replace terms which do not contain metavariables with `...`");
}

void finalize_formatter() {
    delete g_formatter_hide_full;
    delete g_print;
}
}
